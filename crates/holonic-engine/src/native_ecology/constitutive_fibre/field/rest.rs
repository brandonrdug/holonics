//! Complete cold field chart and explicitly supplied capabilities. Remount consumes the rest
//! and installs its sections directly; it does not replay development or regenerate dropped handles.
use super::*;
use super::junction::operative::{OperativeState,rest::{OperativeWire,OperativeRest,OperativeHistoryRest}};
use crate::native_ecology::constitutive_fibre::circulation::rest::{
    blob, expect, point_section, read_blob,
};
use serde::{Deserialize, Serialize};
use std::io::{Read, Write};

const MAGIC: &[u8] = b"HNA-NATIVE-FIELD-REST\x01";
const END: &[u8] = b"HNA-NATIVE-FIELD-END\x01";
type Error = ConstitutiveFibreError;
fn invalid(detail: impl std::fmt::Display) -> Error {
    Error::Rest(detail.to_string())
}

#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct FrameWire {
    ordinal: u64,
    root_to_local: Vec<NativePhaseCurrent>,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct RechartWire {
    before: usize,
    after: usize,
    at_state: Option<usize>,
    gauges: Vec<NativePhaseCurrent>,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct ChangeWire {
    at_state: Option<usize>,
    frame: usize,
    node: usize,
    before: NativePhaseCurrent,
    after: NativePhaseCurrent,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct EmissionWire {
    lineage: NativeFieldLineage,
    returned: bool,
    frame: usize,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct JunctionWire {
    representation: NativeFieldJunctionRepresentation,
    solver: NativeFieldJunctionSolver,
}
#[derive(Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct Header {
    nodes: usize,
    material: Vec<NativeJunctionSeed>,
    frames: Vec<FrameWire>,
    recharts: Vec<RechartWire>,
    changes: Vec<ChangeWire>,
    history: Vec<EmissionWire>,
    junction: Option<JunctionWire>,
    transport: bool,
    #[serde(
        default,
        skip_serializing_if = "NativeMaterialTransportSource::is_outgoing"
    )]
    transport_source: NativeMaterialTransportSource,
    #[serde(default,skip_serializing_if="NativeMaterialTarget::is_direct")]
    transport_target: NativeMaterialTarget,
    #[serde(default,skip_serializing_if="Option::is_none")]
    operative:Option<OperativeWire>,
    source_slots: Vec<Option<usize>>,
    anchor_slots: Vec<Option<usize>>,
}
#[derive(Debug, PartialEq, Eq)]
pub(super) struct HeldRest {
    pub(super) operative:Option<OperativeHistoryRest>,
    pub(super) source: ResidentSectionRest,
    pub(super) incoming: Option<ResidentSectionRest>,
    pub(super) junction: Option<ResidentSectionRest>,
    pub(super) transport: Option<ResidentSectionRest>,
}

/// Serialized chart, not another live ecology. Deliberately not Clone.
#[derive(Debug, PartialEq, Eq)]
pub struct NativeFieldRest {
    operative:Option<OperativeRest>,
    header: Header,
    seed: ResidentSectionRest,
    memory: ResidentSectionRest,
    basis: ResidentSectionRest,
    covariance: Option<ResidentSectionRest>,
    initial_junction: Option<ResidentSectionRest>,
    transport: Option<ResidentSectionRest>,
    history: Vec<HeldRest>,
}

fn packed(rest: &ResidentSectionRest) -> Result<Vec<i128>, Error> {
    if rest.intervals.len() % 2 != 0 || rest.intervals.iter().any(|(a, b)| a != b) {
        return Err(invalid("packed field word"));
    }
    Ok(rest
        .intervals
        .chunks_exact(2)
        .map(|p| (((p[1].0 as u64 as u128) << 64) | p[0].0 as u64 as u128) as i128)
        .collect())
}

// Every admitted section in this field wire has exact i64 codewords. Store each codeword once
// and reconstruct both identical endpoints. This does not quotient a current ball or a fibre.
pub(super) fn point_bytes(section: &ResidentSectionRest) -> Result<Vec<u8>, Error> {
    point_section(section, section.rows, section.width)?;
    let extent = section
        .intervals
        .len()
        .checked_mul(8)
        .and_then(|n| n.checked_add(24))
        .ok_or(Error::Shape)?;
    let mut bytes = Vec::new();
    bytes.try_reserve_exact(extent).map_err(invalid)?;
    for value in [section.rows, section.width, section.intervals.len()] {
        bytes.extend_from_slice(&u64::try_from(value).map_err(invalid)?.to_le_bytes());
    }
    for (value, _) in &section.intervals {
        bytes.extend_from_slice(&value.to_le_bytes());
    }
    Ok(bytes)
}
pub(super) fn read_point(bytes: &[u8]) -> Result<ResidentSectionRest, Error> {
    if bytes.len() < 24 {
        return Err(invalid("point section header"));
    }
    let word = |at| u64::from_le_bytes(bytes[at..at + 8].try_into().expect("checked header"));
    let rows = usize::try_from(word(0)).map_err(invalid)?;
    let width = usize::try_from(word(8)).map_err(invalid)?;
    let count = usize::try_from(word(16)).map_err(invalid)?;
    if rows.checked_mul(width) != Some(count)
        || count.checked_mul(8).and_then(|n| n.checked_add(24)) != Some(bytes.len())
    {
        return Err(invalid("point section extent"));
    }
    let intervals = bytes[24..]
        .chunks_exact(8)
        .map(|v| {
            let value = i64::from_le_bytes(v.try_into().expect("word"));
            (value, value)
        })
        .collect();
    ResidentSectionRest::found(rows, width, ResidentGrain(0), 64, intervals).map_err(invalid)
}
fn junction_section(
    rest: &ResidentSectionRest,
    dimension: usize,
    representation: NativeFieldJunctionRepresentation,
) -> Result<(), Error> {
    let stride = dimension.checked_add(1).ok_or(Error::Shape)?;
    match representation {
        NativeFieldJunctionRepresentation::RationalWords => {
            point_section(rest, 1, 4 * stride)?;
            if (0..4).any(|i| rest.intervals[i * stride + dimension].0 <= 0) {
                return Err(invalid("exact junction denominator"));
            }
        }
        NativeFieldJunctionRepresentation::EnclosedDyadic { fractional_bits } => {
            if !(1..=120).contains(&fractional_bits) {
                return Err(invalid("junction grain"));
            }
            point_section(rest, 1, 12 * stride)?;
            let values = packed(rest)?;
            if (0..5).any(|i| values[i * stride + dimension] < 0)
                || values[5 * stride + dimension] <= 0
            {
                return Err(invalid("junction radius or residual denominator"));
            }
        }
    }
    Ok(())
}
fn transport_section(
    rest: &ResidentSectionRest,
    nodes: usize,
    linked: bool,
) -> Result<i128, Error> {
    point_section(rest, 1, 36 * nodes + 24)?;
    let values = packed(rest)?;
    let target = 2 * nodes;
    let stride = target + 1;
    let gain = 6 * stride;
    let extra = gain + 6 * nodes + 1;
    if (0..6).any(|i| values[i * stride + target] < 0)
        || values[gain + 6 * nodes] < 0
        || values[extra..].iter().any(|v| *v < 0)
        || (linked && values[extra + 1] <= 0)
    {
        return Err(invalid("material transport error or gain"));
    }
    Ok(values[extra])
}

impl NativeFieldRest {
    pub fn material_target(&self)->Option<NativeMaterialTarget>{self.header.transport.then_some(self.header.transport_target)}
    pub fn nodes(&self) -> usize {
        self.header.nodes
    }
    pub fn occurrences(&self) -> usize {
        self.header.history.len()
    }
    pub fn source_slots(&self) -> &[Option<usize>] {
        &self.header.source_slots
    }
    pub fn anchor_slots(&self) -> &[Option<usize>] {
        &self.header.anchor_slots
    }
    pub fn has_material_transport(&self) -> bool {
        self.header.transport
    }
    pub fn material_transport_source(&self) -> Option<NativeMaterialTransportSource> {
        self.header
            .transport
            .then_some(self.header.transport_source)
    }
    pub fn junction_representation(&self) -> Option<NativeFieldJunctionRepresentation> {
        self.header.junction.as_ref().map(|j| j.representation)
    }
    /// Structural carrier and capability validation, not certification of an externally
    /// authored developmental history. No native occurrence is replayed here.
    pub fn validate(&self) -> Result<(), Error> {
        let h = &self.header;
        let n = h.nodes;
        let dimension = n.checked_mul(6).ok_or(Error::Shape)?;
        let source_width = n.checked_mul(4).ok_or(Error::Shape)?;
        let report_width = n
            .checked_mul(16)
            .and_then(|v| v.checked_add(9))
            .ok_or(Error::Shape)?;
        let covariance_width = dimension
            .checked_mul(dimension)
            .and_then(|v| v.checked_add(1))
            .ok_or(Error::Shape)?;
        let transport_width = n
            .checked_mul(n)
            .and_then(|v| v.checked_mul(6))
            .and_then(|v| v.checked_add(1))
            .and_then(|v| v.checked_mul(2))
            .ok_or(Error::Shape)?;
        if n == 0
            || h.material.len() != n
            || h.frames.len() != h.recharts.len() + 1
            || h.history.len() != self.history.len()
            || h.junction.is_some() != self.covariance.is_some()
            || h.transport != self.transport.is_some()
            || (!h.transport && (!h.transport_source.is_outgoing() || !h.transport_target.is_direct()))
            || h.transport_source.report_words_for(n,h.transport_target).is_none()
            || self.initial_junction.is_some() != (h.junction.is_some() && h.history.is_empty())
        {
            return Err(invalid("field populations"));
        }
        for seed in &h.material {
            seed.validate()?;
        }
        if h.junction.is_some()
            && h.material
                .iter()
                .any(|s| s.incoming_admittance != 1 || s.held_admittance != 1)
        {
            return Err(invalid("paired seed admittance"));
        }
        if h.transport
            && !matches!(
                h.junction.as_ref().map(|j| j.representation),
                Some(NativeFieldJunctionRepresentation::EnclosedDyadic { .. })
            )
        {
            return Err(invalid("transport source representation"));
        }
        if h.junction.as_ref().is_some_and(|j| {
            j.representation == NativeFieldJunctionRepresentation::RationalWords
                && j.solver != NativeFieldJunctionSolver::Full
        }) {
            return Err(invalid(
                "solver does not belong to the saved representation",
            ));
        }
        for (i, frame) in h.frames.iter().enumerate() {
            if frame.ordinal != i as u64
                || frame.root_to_local.len() != n
                || frame.root_to_local.iter().any(|p| !p.is_unit())
            {
                return Err(invalid("field frame"));
            }
        }
        if h.frames[0]
            .root_to_local
            .iter()
            .any(|p| *p != NativePhaseCurrent::unit())
        {
            return Err(invalid("initial root frame"));
        }
        let state_count = |state: Option<usize>| -> Result<usize, Error> {
            match state {
                None => Ok(0),
                Some(i) if i < h.history.len() => Ok(i + 1),
                _ => Err(invalid("absent field state")),
            }
        };
        let mut last = 0;
        for (i, r) in h.recharts.iter().enumerate() {
            let at = state_count(r.at_state)?;
            if r.before != i
                || r.after != i + 1
                || at < last
                || r.gauges.len() != n
                || r.gauges.iter().any(|g| !g.is_unit())
            {
                return Err(invalid("field rechart chronology"));
            }
            for node in 0..n {
                if r.gauges[node]
                    .current()
                    .multiply(&h.frames[i].root_to_local[node].current())
                    != h.frames[i + 1].root_to_local[node].current()
                {
                    return Err(invalid("field gauge transport"));
                }
            }
            last = at;
        }
        let mut last_change = (0, 0);
        for c in &h.changes {
            let at = state_count(c.at_state)?;
            if c.frame >= h.frames.len()
                || c.node >= n
                || !c.before.is_unit()
                || !c.after.is_unit()
                || (at, c.frame) < last_change
                || (c.frame > 0 && state_count(h.recharts[c.frame - 1].at_state)? > at)
                || (c.frame < h.recharts.len() && state_count(h.recharts[c.frame].at_state)? < at)
            {
                return Err(invalid("field incidence chronology"));
            }
            last_change = (at, c.frame);
        }
        point_section(&self.seed, n, 5)?;
        point_section(&self.memory, n, 3)?;
        point_section(&self.basis, dimension, dimension)?;
        for (i, seed) in h.material.iter().enumerate() {
            let t = seed.incoming_transport.words();
            let expected = [
                seed.incoming_admittance,
                seed.held_admittance,
                t[0],
                t[1],
                t[2],
            ];
            if self.seed.intervals[5 * i..5 * i + 5]
                .iter()
                .map(|v| v.0)
                .ne(expected)
            {
                return Err(invalid("seed and material disagree"));
            }
            let m = &self.memory.intervals[3 * i..3 * i + 3];
            if NativePhaseCurrent::new(m[0].0, m[1].0, m[2].0)?.words() != [m[0].0, m[1].0, m[2].0]
            {
                return Err(invalid("held field current normalization"));
            }
            if h.history.is_empty() && [m[0].0, m[1].0, m[2].0] != seed.initial_held.words() {
                return Err(invalid("initial field memory and seed disagree"));
            }
        }
        let mut rank = 0;
        for p in 0..dimension {
            let row = &self.basis.intervals[p * dimension..(p + 1) * dimension];
            if row[p].0 < 0
                || row[..p].iter().any(|v| v.0 != 0)
                || (row[p].0 == 0 && row.iter().any(|v| v.0 != 0))
            {
                return Err(invalid("field relation echelon shape"));
            }
            rank += usize::from(row[p].0 > 0);
        }
        if let Some(covariance) = &self.covariance {
            point_section(covariance, 1, covariance_width)?;
            if covariance.intervals[covariance_width - 1].0 <= 0 {
                return Err(invalid("covariance denominator"));
            }
            for i in 0..dimension {
                for j in 0..dimension {
                    if covariance.intervals[i * dimension + j]
                        != covariance.intervals[j * dimension + i]
                    {
                        return Err(invalid("covariance symmetry"));
                    }
                }
            }
            for i in (0..dimension).step_by(2) {
                for j in (0..dimension).step_by(2) {
                    if covariance.intervals[i * dimension + j]
                        != covariance.intervals[(i + 1) * dimension + j + 1]
                        || covariance.intervals[i * dimension + j + 1].0 as i128
                            + covariance.intervals[(i + 1) * dimension + j].0 as i128
                            != 0
                    {
                        return Err(invalid("covariance is outside the complex current chart"));
                    }
                }
            }
            if h.history.is_empty()
                && (covariance.intervals[..covariance_width - 1]
                    .iter()
                    .any(|v| v.0 != 0)
                    || covariance.intervals[covariance_width - 1].0 != 1)
            {
                return Err(invalid("an empty field has a nonzero contact moment"));
            }
        }
        let mut received = vec![false; h.history.len()];
        let mut preceding_rank = 0usize;
        let mut frame_at = 0;
        let mut coefficient_error = 0;
        // Ephemeral cold validation of native reference frames, not semantic identity.
        let mut contextual_references = std::collections::BTreeMap::<Vec<(i64, i64)>, usize>::new();
        for (at, (event, rest)) in h.history.iter().zip(&self.history).enumerate() {
            while frame_at < h.recharts.len() && state_count(h.recharts[frame_at].at_state)? <= at {
                frame_at += 1;
            }
            if event.lineage.occurrence != at
                || event.lineage.predecessor_state != at.checked_sub(1)
                || event.frame != frame_at
                || event.lineage.frame != frame_at as u64
                || event.lineage.incoming.len() != n
            {
                return Err(invalid("field source/frame chronology"));
            }
            let incoming = match (&event.lineage.incoming, &rest.incoming) {
                (NativeFieldIncoming::Exterior(values), None) => values.clone(),
                (NativeFieldIncoming::Resident { resident_nodes }, Some(input))
                    if *resident_nodes == n =>
                {
                    resident_input::decode_input(input, n)?
                }
                _ => return Err(invalid("input provenance/carrier disagreement")),
            };
            for value in &incoming {
                let w = value.words();
                if NativePhaseCurrent::new(w[0], w[1], w[2])?.words() != w {
                    return Err(invalid("incoming current normalization"));
                }
            }
            match (event.lineage.received_from, event.lineage.source_contact) {
                (None, None) => {}
                (Some(source), Some(kind)) if source < at => {
                    if kind == NativeFieldSourceContact::Emission {
                        if received[source] {
                            return Err(invalid("reused linear emission"));
                        }
                        received[source] = true;
                    }
                }
                _ => return Err(invalid("field receiving source")),
            }
            point_section(&rest.source, 1, report_width)?;
            let w = &rest.source.intervals;
            let current = source_width + 1;
            let prior = current + dimension + 4;
            let pivot = w[current + dimension + 2].0;
            let current_rank = w[current + dimension + 3].0;
            let linked = event.lineage.received_from.is_some();
            if w[source_width].0 <= 0
                || w[current + dimension].0 <= 0
                || w[prior + dimension].0 <= 0
                || !(0..=2).contains(&w[current + dimension + 1].0)
                || pivot < -1
                || pivot >= dimension as i64
                || current_rank != preceding_rank as i64 + i64::from(pivot >= 0)
                || (linked
                    && (!(0..=2).contains(&w[prior + dimension + 1].0)
                        || w[prior + dimension + 3].0 != preceding_rank as i64))
                || (!linked && (w[prior + dimension + 1].0 != 3 || pivot != -1))
            {
                return Err(invalid("field current/rank receipt"));
            }
            preceding_rank = usize::try_from(current_rank).map_err(invalid)?;
            if rest.junction.is_some() != h.junction.is_some()
                || rest.transport.is_some() != h.transport
            {
                return Err(invalid("missing historical current"));
            }
            if let (Some(wire), Some(section)) = (&h.junction, &rest.junction) {
                junction_section(section, dimension, wire.representation)?;
            }
            if let Some(section) = &rest.transport {
                let error = if h.transport_source != NativeMaterialTransportSource::CoupledOutgoing
                {
                    let grain = match h.junction.as_ref().map(|j| j.representation) {
                        Some(NativeFieldJunctionRepresentation::EnclosedDyadic {
                            fractional_bits,
                        }) => fractional_bits,
                        _ => return Err(invalid("complete-current representation")),
                    };
                    match h.transport_source {
                        NativeMaterialTransportSource::Contextual
                        | NativeMaterialTransportSource::BilinearContextual
                        | NativeMaterialTransportSource::OperativeContextual => {
                            material_transport::contextual::validate_report_for(section, n, h.transport_target.dimension(n).ok_or_else(||invalid("material target extent"))?, grain, at)?
                        }
                        NativeMaterialTransportSource::HomogeneousMoment => {
                            material_transport::moment::validate_report(section, n, grain, at)?
                        }
                        _ => material_transport::complete::validate_report(section, n, grain, at)?,
                    }
                } else {
                    transport_section(section, n, linked)?
                };
                if error < coefficient_error {
                    return Err(invalid("coefficient error chronology"));
                }
                coefficient_error = error;
                if matches!(
                    h.transport_source,
                    NativeMaterialTransportSource::Contextual
                        | NativeMaterialTransportSource::BilinearContextual
                        | NativeMaterialTransportSource::OperativeContextual
                ) {
                    let [_, output, input, context, _, meta, _] =
                        material_transport::contextual::offsets_for(n,h.transport_target.dimension(n).ok_or_else(||invalid("material target extent"))?);
                    let version = if h.transport_source==NativeMaterialTransportSource::OperativeContextual {3} else if h.transport_source
                        == NativeMaterialTransportSource::BilinearContextual
                    {
                        2
                    } else {
                        1
                    };
                    if section.intervals[meta + 3].0 != version {
                        return Err(invalid("contextual chart version"));
                    }
                    if version==3 {
                        let op=rest.operative.as_ref().ok_or_else(||invalid("missing operative material source"))?;
                        material_transport::contextual::validate_operative_profile(&section.intervals[context..context+36*n+22],n,self.header.junction.as_ref().and_then(|j|match j.representation {NativeFieldJunctionRepresentation::EnclosedDyadic{fractional_bits}=>Some(fractional_bits),_=>None}).ok_or_else(||invalid("operative grain"))?,at,Some(&op.b))?;
                        if material_transport::wides(&section.intervals[context+36*n+16..context+36*n+18])?[0]!=material_transport::wides(&op.bounds.intervals)?[1] {return Err(invalid("operative material source radius"));}
                    }
                    let source = event.lineage.received_from;
                    if section.intervals[meta + 1].0 != source.map_or(-1, |v| v as i64) {
                        return Err(invalid("contextual source lineage"));
                    }
                    if let Some(source) = source {
                        let prior = self.history[source]
                            .transport
                            .as_ref()
                            .ok_or_else(|| invalid("missing contextual source"))?;
                        if section.intervals[input..context] != prior.intervals[output..input] {
                            return Err(invalid("changed contextual source profile"));
                        }
                        let key = section.intervals[input..input + 8 * n + 2].to_vec();
                        let reference = *contextual_references.entry(key).or_insert(at);
                        if section.intervals[meta + 2].0 != reference as i64 {
                            return Err(invalid("contextual reference frame"));
                        }
                    }
                }
            }
        }
        if preceding_rank != rank || h.history.iter().zip(received).any(|(e, r)| e.returned != r) {
            return Err(invalid("field rank or consumed-source flags"));
        }
        if let (Some(wire), Some(section)) = (&h.junction, &self.initial_junction) {
            junction_section(section, dimension, wire.representation)?;
            match wire.representation {
                NativeFieldJunctionRepresentation::RationalWords => {
                    for block in section.intervals.chunks_exact(dimension + 1) {
                        if block[..dimension].iter().any(|v| v.0 != 0) || block[dimension].0 != 1 {
                            return Err(invalid("initial exact junction"));
                        }
                    }
                }
                NativeFieldJunctionRepresentation::EnclosedDyadic { .. } => {
                    let values = packed(section)?;
                    if values[..values.len() - 1].iter().any(|v| *v != 0)
                        || values.last() != Some(&1)
                    {
                        return Err(invalid("initial enclosed junction"));
                    }
                }
            }
        }
        if let Some(state) = &self.transport {
            if h.transport_source != NativeMaterialTransportSource::CoupledOutgoing {
                let grain = match h.junction.as_ref().map(|j| j.representation) {
                    Some(NativeFieldJunctionRepresentation::EnclosedDyadic { fractional_bits }) => {
                        fractional_bits
                    }
                    _ => return Err(invalid("complete-current representation")),
                };
                let validate = if matches!(
                    h.transport_source,
                    NativeMaterialTransportSource::HomogeneousMoment
                        | NativeMaterialTransportSource::Contextual
                        | NativeMaterialTransportSource::BilinearContextual
                        | NativeMaterialTransportSource::OperativeContextual
                ) {
                    material_transport::moment::validate_state
                } else {
                    material_transport::complete::validate_state
                };
                validate(state, n, grain, h.history.len(), coefficient_error)?;
            } else {
                point_section(state, 1, transport_width)?;
                let values = packed(state)?;
                if values.last().copied() != Some(coefficient_error)
                    || (h.history.is_empty() && values.iter().any(|v| *v != 0))
                {
                    return Err(invalid("material transport standing/error"));
                }
            }
        }
        if h.transport_source==NativeMaterialTransportSource::OperativeContextual && h.operative.as_ref().is_none_or(|o|o.activated_at!=0) {return Err(invalid("operative material requires its complete current history"));}
        if h.operative.is_some()!=self.operative.is_some(){return Err(invalid("operative state presence"));}
        if let Some(wire)=&h.operative {
            if wire.activated_at>h.history.len() || h.junction.as_ref().is_none_or(|j|!matches!(j.representation,NativeFieldJunctionRepresentation::EnclosedDyadic{..})) {
                return Err(invalid("operative activation or representation"));
            }
            let births=h.history.iter().enumerate().filter_map(|(receiving,e)|e.lineage.received_from.map(|source|NativeOperativeContactBirth{source,receiving})).collect::<Vec<_>>();
            if wire.births!=births {return Err(invalid("operative birth lineage"));}
            self.operative.as_ref().unwrap().validate(wire,n)?;
            if wire.return_frames.iter().any(|r|r.at_cut>h.history.len()){return Err(invalid("operative return beyond field cut"));}
            if let Some(last)=self.history.last().and_then(|h|h.operative.as_ref()) {
                let current=&self.operative.as_ref().unwrap().current;
                if current[1]!=last.b || material_transport::wides(&current[2].intervals)?[1]!=material_transport::wides(&last.bounds.intervals)?[1] {return Err(invalid("operative current/history boundary"));}
            }

        }
        let mut contacts=0;
        for (at,(event,rest)) in h.history.iter().zip(&self.history).enumerate(){
            contacts+=usize::from(event.lineage.received_from.is_some());
            if rest.operative.is_some()!=h.operative.as_ref().is_some_and(|o|at>=o.activated_at){return Err(invalid("operative historical presence"));}
            if let Some(op)=&rest.operative{op.validate(dimension,contacts)?;}
        }
        let mut supplied = vec![false; h.history.len()];
        for source in h.source_slots.iter().flatten() {
            if *source >= h.history.len() || h.history[*source].returned || supplied[*source] {
                return Err(invalid("absent, consumed or duplicated linear capability"));
            }
            supplied[*source] = true;
        }
        if h.anchor_slots
            .iter()
            .flatten()
            .any(|source| *source >= h.history.len())
        {
            return Err(invalid("absent shared source"));
        }
        Ok(())
    }
    pub fn write(&self, out: &mut impl Write) -> Result<(), Error> {
        self.validate()?;
        out.write_all(MAGIC).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        let mut section = |s: &ResidentSectionRest| blob(out, &point_bytes(s)?);
        section(&self.seed)?;
        section(&self.memory)?;
        section(&self.basis)?;
        if let Some(s) = &self.covariance {
            section(s)?;
        }
        if let Some(s) = &self.initial_junction {
            section(s)?;
        }
        if let Some(s) = &self.transport {
            section(s)?;
        }
        if let Some(op)=&self.operative {op.write(&mut section)?;}
        for h in &self.history {
            section(&h.source)?;
            if let Some(s) = &h.junction {
                section(s)?;
            }
            if let Some(s) = &h.transport {
                section(s)?;
            }
            if let Some(s) = &h.incoming {
                section(s)?;
            }
            if let Some(op)=&h.operative{op.write(&mut section)?;}
        }
        out.write_all(END).map_err(invalid)
    }
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, Error> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let mut section = || read_point(&read_blob(&mut input)?);
        let seed = section()?;
        let memory = section()?;
        let basis = section()?;
        let covariance = header.junction.as_ref().map(|_| section()).transpose()?;
        let initial_junction = (header.junction.is_some() && header.history.is_empty())
            .then(&mut section)
            .transpose()?;
        let transport = header.transport.then(&mut section).transpose()?;
        let operative=header.operative.as_ref().map(|w|OperativeRest::read(w,&mut section)).transpose()?;
        let mut history = Vec::new();
        for (at,event) in header.history.iter().enumerate() {
            history.push(HeldRest {
                source: section()?,
                junction: header.junction.as_ref().map(|_| section()).transpose()?,
                transport: header.transport.then(&mut section).transpose()?,
                incoming: event
                    .lineage
                    .incoming
                    .is_resident()
                    .then(&mut section)
                    .transpose()?,
                operative:header.operative.as_ref().is_some_and(|o|at>=o.activated_at).then(||OperativeHistoryRest::read(&mut section)).transpose()?,
            });
        }
        expect(&mut input, END)?;
        if input.limit() != 0 {
            return Err(invalid("trailing field rest bytes"));
        }
        let rest = Self {
            operative,
            header,
            seed,
            memory,
            basis,
            covariance,
            initial_junction,
            transport,
            history,
        };
        rest.validate()?;
        Ok(rest)
    }
}

impl<'chart> NativeConstitutiveField<'chart> {
    pub fn rest(
        &self,
        sources: &[Option<&NativeFieldEmission>],
        anchors: &[Option<&NativeFieldSourceAnchor>],
    ) -> Result<NativeFieldRest, Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        let root = self
            .recharts
            .first()
            .map_or(&self.frame.view, |r| &r.before);
        let frames = std::iter::once(root)
            .chain(self.recharts.iter().map(|r| &r.after))
            .map(|f| FrameWire {
                ordinal: f.ordinal,
                root_to_local: f.root_to_local.clone(),
            })
            .collect();
        let source_slots = sources
            .iter()
            .map(|s| {
                s.map(|s| {
                    if !Rc::ptr_eq(&s.owner, &self.owner) {
                        return Err(Error::ForeignOccurrence);
                    }
                    Ok(s.occurrence)
                })
                .transpose()
            })
            .collect::<Result<_, _>>()?;
        let anchor_slots = anchors
            .iter()
            .map(|s| {
                s.map(|s| {
                    if !Rc::ptr_eq(&s.owner, &self.owner) {
                        return Err(Error::ForeignOccurrence);
                    }
                    Ok(s.occurrence)
                })
                .transpose()
            })
            .collect::<Result<_, _>>()?;
        let section = |s: &ResidentSection<'chart>| {
            self.relation
                .surface
                .detach_section(s, 64)
                .map_err(Error::from)
        };
        let rest = NativeFieldRest {
            header: Header {
                nodes: self.nodes(),
                material: self.material.clone(),
                frames,
                recharts: self
                    .recharts
                    .iter()
                    .map(|r| RechartWire {
                        before: r.before.ordinal as usize,
                        after: r.after.ordinal as usize,
                        at_state: r.at_state,
                        gauges: r.gauges.clone(),
                    })
                    .collect(),
                changes: self
                    .incidence_changes
                    .iter()
                    .map(|c| ChangeWire {
                        at_state: c.at_state,
                        frame: c.frame.ordinal as usize,
                        node: c.node,
                        before: c.before,
                        after: c.after,
                    })
                    .collect(),
                history: self
                    .history
                    .iter()
                    .map(|h| EmissionWire {
                        lineage: h.lineage.clone(),
                        returned: h.returned,
                        frame: h.frame.view.ordinal as usize,
                    })
                    .collect(),
                junction: self.junction.as_ref().map(|j| JunctionWire {
                    representation: j.representation,
                    solver: j.solver,
                }),
                transport: self.transport.is_some(),
                transport_source: self.material_transport_source().unwrap_or_default(),
                transport_target: self.material_target().unwrap_or_default(),
                operative:self.junction.as_ref().and_then(|j|j.operative.as_ref()).map(|o|o.wire()),
                source_slots,
                anchor_slots,
            },
            operative:self.junction.as_ref().and_then(|j|j.operative.as_ref()).map(|o|o.rest(self.relation.surface)).transpose()?,
            seed: section(&self.seed)?,
            memory: section(&self.memory)?,
            basis: section(&self.relation.basis)?,
            covariance: self
                .junction
                .as_ref()
                .map(|j| section(&j.covariance))
                .transpose()?,
            initial_junction: if self.history.is_empty() {
                self.junction
                    .as_ref()
                    .map(|j| section(&j.current))
                    .transpose()?
            } else {
                None
            },
            transport: self
                .transport
                .as_ref()
                .map(|t| section(&t.state))
                .transpose()?,
            history: self
                .history
                .iter()
                .map(|h| h.rest(self.relation.surface))
                .collect::<Result<_, Error>>()?,
        };
        rest.validate()?;
        Ok(rest)
    }
    pub fn remount(
        surface: &'chart ResidentSurface<'chart>,
        rest: NativeFieldRest,
    ) -> Result<
        (
            Self,
            Vec<Option<NativeFieldEmission>>,
            Vec<Option<NativeFieldSourceAnchor>>,
        ),
        Error,
    > {
        Self::remount_placed(surface, rest, None)
    }
    /// Mount current standing and the newest source on the device, with all older numerical
    /// carriers in a fresh exterior archive. This consumes the same complete cold rest; it does
    /// not replay history or require the prior backing file.
    pub fn remount_with_history_archive(
        surface: &'chart ResidentSurface<'chart>,
        rest: NativeFieldRest,
        path: impl AsRef<std::path::Path>,
    ) -> Result<
        (
            Self,
            Vec<Option<NativeFieldEmission>>,
            Vec<Option<NativeFieldSourceAnchor>>,
        ),
        Error,
    > {
        rest.validate()?;
        let archive = FieldArchive::create(path.as_ref())?;
        Self::remount_placed(surface, rest, Some(archive))
    }
    fn remount_placed(
        surface: &'chart ResidentSurface<'chart>,
        rest: NativeFieldRest,
        mut archive: Option<FieldArchive>,
    ) -> Result<
        (
            Self,
            Vec<Option<NativeFieldEmission>>,
            Vec<Option<NativeFieldSourceAnchor>>,
        ),
        Error,
    > {
        rest.validate()?;
        let scratch = rest
            .nodes()
            .checked_mul(24)
            .and_then(|v| v.checked_mul(16))
            .ok_or(Error::Shape)?;
        let available = surface.declaration().max_sectiond_bytes;
        if scratch > available as usize {
            return Err(Error::ScratchAperture {
                required: scratch,
                available,
            });
        }
        let NativeFieldRest {
            header: h,
            operative,
            seed,
            memory,
            basis,
            covariance,
            initial_junction,
            transport,
            history,
        } = rest;
        let frames = h
            .frames
            .into_iter()
            .map(|f| {
                let words = f
                    .root_to_local
                    .iter()
                    .flat_map(|p| p.words())
                    .map(|v| (v, v))
                    .collect();
                Ok(Rc::new(HeldCurrentFrame {
                    native: surface.mount_section_rest(
                        &ResidentSectionRest::found(h.nodes, 3, ResidentGrain(0), 64, words)
                            .map_err(invalid)?,
                    )?,
                    view: Rc::new(NativeCurrentFrame {
                        ordinal: f.ordinal,
                        root_to_local: f.root_to_local,
                    }),
                }))
            })
            .collect::<Result<Vec<_>, Error>>()?;
        let owner = Rc::new(());
        let sources = h
            .source_slots
            .into_iter()
            .map(|at| {
                at.map(|occurrence| NativeFieldEmission {
                    owner: Rc::clone(&owner),
                    occurrence,
                })
            })
            .collect();
        let anchors = h
            .anchor_slots
            .into_iter()
            .map(|at| {
                at.map(|occurrence| NativeFieldSourceAnchor {
                    owner: Rc::clone(&owner),
                    occurrence,
                })
            })
            .collect();
        let occurrences = h.history.len() as u64;
        let history = h
            .history
            .into_iter()
            .zip(history)
            .enumerate()
            .map(|(at, (event, rest))| {
                let (resident, archived) = if let Some(archive) =
                    archive.as_mut().filter(|_| at + 1 < occurrences as usize)
                {
                    (None, Some(archive.append(&rest)?))
                } else {
                    (Some(ResidentFieldHistory::mount(surface, rest)?), None)
                };
                Ok(HeldField {
                    resident,
                    archived,
                    lineage: event.lineage,
                    returned: event.returned,
                    frame: Rc::clone(&frames[event.frame]),
                })
            })
            .collect::<Result<Vec<_>, Error>>()?;
        if let Some(archive) = &mut archive {
            archive.sync()?;
            archive.note_archived_prefix(history.len().saturating_sub(1));
        }
        let junction = if let Some(j) = h.junction {
            let current = if let Some(last) = history.last() {
                Rc::clone(
                    last.resident()?
                        .junction
                        .as_ref()
                        .expect("validated junction"),
                )
            } else {
                Rc::new(surface.mount_section_rest(&initial_junction.expect("initial junction"))?)
            };
            Some(PairedJunction {
                representation: j.representation,
                solver: j.solver,
                covariance: surface.mount_section_rest(&covariance.expect("covariance"))?,
                current,
                operative: match (h.operative,operative) {
                    (Some(wire),Some(rest))=>Some(OperativeState::remount(surface,wire,rest,match j.representation {NativeFieldJunctionRepresentation::EnclosedDyadic{fractional_bits}=>fractional_bits,_=>return Err(invalid("operative representation"))})?),
                    (None,None)=>None,_=>return Err(invalid("operative state presence")),
                },
            })
        } else {
            None
        };
        let body = Self {
            seed: surface.mount_section_rest(&seed)?,
            memory: surface.mount_section_rest(&memory)?,
            relation: ResidentConstitutiveFibre {
                source_chart: ConstitutiveSourceChart::Linear,
                basis: surface.mount_section_rest(&basis)?,
                surface,
                source_width: 4 * h.nodes,
                target_width: 2 * h.nodes,
                occurrences,
                usable: true,
            },
            material: h.material,
            frame: Rc::clone(frames.last().expect("frames")),
            recharts: h
                .recharts
                .into_iter()
                .map(|r| NativeRechartReceipt {
                    before: Rc::clone(&frames[r.before].view),
                    after: Rc::clone(&frames[r.after].view),
                    at_state: r.at_state,
                    gauges: r.gauges,
                })
                .collect(),
            incidence_changes: h
                .changes
                .into_iter()
                .map(|c| NativeIncidenceChange {
                    at_state: c.at_state,
                    frame: Rc::clone(&frames[c.frame].view),
                    node: c.node,
                    before: c.before,
                    after: c.after,
                })
                .collect(),
            owner,
            history,
            archive,
            pending: None,
            junction,
            pending_junction: None,
            transport: transport
                .map(|s| {
                    surface
                        .mount_section_rest(&s)
                        .map(|state| MaterialTransport {
                            state,
                            source: h.transport_source,
                            target: h.transport_target,
                        })
                })
                .transpose()?,
            pending_transport: None,
        };
        Ok((body, sources, anchors))
    }
}

#[cfg(test)]
mod tests;
