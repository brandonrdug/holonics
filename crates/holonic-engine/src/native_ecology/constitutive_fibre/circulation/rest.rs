//! Complete cold chart of this ecology and its actually supplied linear boundary handles.
//! It is not Clone, a relation-only model, or an event log to replay. Remount consumes this
//! representation and installs its exact sections in one new owner. No native deed is replayed.

use super::*;
use serde::{Deserialize, Serialize};
use std::io::{Read, Take, Write};

const MAGIC: &[u8] = b"HNA-NATIVE-PHASE-REST\x01";
const END: &[u8] = b"HNA-NATIVE-PHASE-END\x01";
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
struct EmissionWire {
    lineage: NativeCurrentLineage,
    returned: bool,
    material: usize,
    frame: usize,
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
struct Header {
    nodes: usize,
    current_material: usize,
    materials: Vec<Vec<NativeJunctionSeed>>,
    frames: Vec<FrameWire>,
    history: Vec<EmissionWire>,
    recharts: Vec<RechartWire>,
    changes: Vec<ChangeWire>,
    // An exterior slot maps to a native occurrence only through a supplied actual handle.
    // Missing/dropped handles are not regenerated from the unreturned history population.
    source_slots: Vec<Option<usize>>,
}

#[derive(Debug, PartialEq, Eq)]
pub struct NativeEcologyRest {
    header: Header,
    seed: ResidentSectionRest,
    memory: ResidentSectionRest,
    basis: ResidentSectionRest,
    emissions: Vec<ResidentSectionRest>,
}

fn point_section(rest: &ResidentSectionRest, rows: usize, width: usize) -> Result<(), Error> {
    rest.validate().map_err(invalid)?;
    if rest.rows != rows
        || rest.width != width
        || rest.grain != ResidentGrain(0)
        || rest.bound_octaves != 64
        || rest.intervals.iter().any(|(l, h)| l != h)
    {
        return Err(invalid("section shape, grain, aperture or point endpoints"));
    }
    Ok(())
}

impl NativeEcologyRest {
    pub fn occurrences(&self) -> usize {
        self.header.history.len()
    }
    pub fn nodes(&self) -> usize {
        self.header.nodes
    }
    pub fn source_slots(&self) -> &[Option<usize>] {
        &self.header.source_slots
    }
    pub fn rank(&self) -> usize {
        (0..self.basis.width)
            .filter(|p| self.basis.intervals[p * self.basis.width + p].0 > 0)
            .count()
    }

    /// Structural carrier/lineage validation at the cold boundary. This is not a proof that
    /// an arbitrary externally authored file has a true developmental history.
    pub fn validate(&self) -> Result<(), Error> {
        let h = &self.header;
        let width = h
            .nodes
            .checked_mul(2)
            .and_then(|n| n.checked_add(2))
            .ok_or_else(|| invalid("node extent overflow"))?;
        let emission_width = h
            .nodes
            .checked_mul(6)
            .and_then(|n| n.checked_add(13))
            .ok_or_else(|| invalid("emission extent overflow"))?;
        if h.nodes == 0
            || h.materials.is_empty()
            || h.current_material >= h.materials.len()
            || h.frames.len()
                != h.recharts
                    .len()
                    .checked_add(1)
                    .ok_or_else(|| invalid("frames"))?
            || self.emissions.len() != h.history.len()
        {
            return Err(invalid("native populations do not reconstruct"));
        }
        for m in &h.materials {
            if m.len() != h.nodes {
                return Err(invalid("material population"));
            }
            for seed in m {
                seed.validate()?;
            }
        }
        for (i, f) in h.frames.iter().enumerate() {
            if f.ordinal != i as u64
                || f.root_to_local.len() != h.nodes
                || f.root_to_local.iter().any(|p| !p.is_unit())
            {
                return Err(invalid("frame occurrence or unit-phase population"));
            }
        }
        if h.frames[0]
            .root_to_local
            .iter()
            .any(|p| *p != NativePhaseCurrent::unit())
        {
            return Err(invalid("root frame is not the original boundary chart"));
        }
        let state_count = |at: Option<usize>| -> Result<usize, Error> {
            match at {
                None => Ok(0),
                Some(i) if i < h.history.len() => Ok(i + 1),
                _ => Err(invalid("event refers to an absent held state")),
            }
        };
        let mut last_rechart = 0;
        for (i, r) in h.recharts.iter().enumerate() {
            let at = state_count(r.at_state)?;
            if r.before != i
                || r.after != i + 1
                || r.gauges.len() != h.nodes
                || at < last_rechart
                || r.gauges.iter().any(|p| !p.is_unit())
            {
                return Err(invalid("rechart chronology or phase"));
            }
            last_rechart = at;
            for node in 0..h.nodes {
                if r.gauges[node]
                    .current()
                    .multiply(&h.frames[i].root_to_local[node].current())
                    != h.frames[i + 1].root_to_local[node].current()
                {
                    return Err(invalid("frame does not reconstruct its gauge passage"));
                }
            }
        }
        let mut last_change = (0, 0);
        for c in &h.changes {
            let at = state_count(c.at_state)?;
            if c.frame >= h.frames.len()
                || c.node >= h.nodes
                || !c.before.is_unit()
                || !c.after.is_unit()
                || (at, c.frame) < last_change
                || (c.frame > 0 && state_count(h.recharts[c.frame - 1].at_state)? > at)
                || (c.frame < h.recharts.len() && state_count(h.recharts[c.frame].at_state)? < at)
            {
                return Err(invalid("physical incidence chronology or boundary"));
            }
            last_change = (at, c.frame);
        }
        point_section(&self.seed, h.nodes, 5)?;
        point_section(&self.memory, h.nodes, 3)?;
        point_section(&self.basis, width, width)?;
        for (node, seed) in h.materials[h.current_material].iter().enumerate() {
            let expected = [
                seed.incoming_admittance,
                seed.held_admittance,
                seed.incoming_transport.real,
                seed.incoming_transport.imaginary,
                seed.incoming_transport.denominator,
            ];
            if self.seed.intervals[node * 5..node * 5 + 5]
                .iter()
                .map(|p| p.0)
                .ne(expected)
            {
                return Err(invalid(
                    "resident seed and retained constitutive material differ",
                ));
            }
            let m = &self.memory.intervals[node * 3..node * 3 + 3];
            if NativePhaseCurrent::new(m[0].0, m[1].0, m[2].0)?.words() != [m[0].0, m[1].0, m[2].0]
            {
                return Err(invalid("held phase is not its normalized exact chart"));
            }
        }
        for p in 0..width {
            let row = &self.basis.intervals[p * width..(p + 1) * width];
            if row[p].0 < 0
                || row[..p].iter().any(|v| v.0 != 0)
                || (row[p].0 == 0 && row.iter().any(|v| v.0 != 0))
            {
                return Err(invalid(
                    "paired basis is not the native positive-pivot echelon chart",
                ));
            }
        }
        let mut received = vec![false; h.history.len()];
        let mut used_material = vec![false; h.materials.len()];
        used_material[h.current_material] = true;
        let mut preceding_rank = 0;
        let mut frame_at = 0;
        for (i, (event, section)) in h.history.iter().zip(&self.emissions).enumerate() {
            while frame_at < h.recharts.len()
                && h.recharts[frame_at].at_state.map_or(0, |s| s + 1) <= i
            {
                frame_at += 1;
            }
            if event.lineage.occurrence != i
                || event.lineage.predecessor_state != i.checked_sub(1)
                || event.material >= h.materials.len()
                || event.frame != frame_at
                || event.lineage.frame != event.frame as u64
            {
                return Err(invalid("emitted occurrence/frame/material lineage"));
            }
            used_material[event.material] = true;
            if let Some(source) = event.lineage.received_from {
                if source >= i || received[source] {
                    return Err(invalid("nonlinear or future receiving handle"));
                }
                received[source] = true;
            }
            point_section(section, 1, emission_width)?;
            let words = &section.intervals;
            let source_width = width - 2;
            let current_at = source_width + 1;
            let prior_at = current_at + width + 4;
            let pivot = words[current_at + width + 2].0;
            let current_rank = words[current_at + width + 3].0;
            let prior_status = words[prior_at + width + 1].0;
            if words[source_width].0 <= 0
                || words[current_at + width].0 <= 0
                || words[prior_at + width].0 <= 0
                || !(0..=2).contains(&words[current_at + width + 1].0)
                || pivot < -1
                || pivot >= width as i64
                || current_rank < 0
                || current_rank > width as i64
                || current_rank != preceding_rank + i64::from(pivot >= 0)
                || (event.lineage.received_from.is_some()
                    && words[prior_at + width + 3].0 != preceding_rank)
                || (event.lineage.received_from.is_some() && !(0..=2).contains(&prior_status))
                || (event.lineage.received_from.is_none() && (prior_status != 3 || pivot != -1))
            {
                return Err(invalid("emitted current/receiver section"));
            }
            preceding_rank = current_rank;
        }
        if self.rank() as i64 != preceding_rank {
            return Err(invalid(
                "current relation rank and last native successor disagree",
            ));
        }
        if used_material.iter().any(|used| !used) {
            return Err(invalid("material table contains an unclaimed allocation"));
        }
        if h.history.iter().zip(received).any(|(e, r)| e.returned != r) {
            return Err(invalid(
                "returned-source flags do not reconstruct the actual receiving edges",
            ));
        }
        let mut supplied = vec![false; h.history.len()];
        for source in h.source_slots.iter().flatten() {
            if *source >= h.history.len() || h.history[*source].returned || supplied[*source] {
                return Err(invalid("saved handle is absent, returned or duplicated"));
            }
            supplied[*source] = true;
        }
        Ok(())
    }

    pub fn write(&self, out: &mut impl Write) -> Result<(), Error> {
        self.validate()?;
        out.write_all(MAGIC).map_err(invalid)?;
        blob(out, &serde_json::to_vec(&self.header).map_err(invalid)?)?;
        for section in [&self.seed, &self.memory, &self.basis]
            .into_iter()
            .chain(self.emissions.iter())
        {
            blob(out, &section.canonical_bytes().map_err(invalid)?)?;
        }
        out.write_all(END).map_err(invalid)
    }
    /// `octets` is the containing wire's actual bounded extent, not a semantic capacity.
    pub fn read(input: &mut impl Read, octets: u64) -> Result<Self, Error> {
        let mut input = input.take(octets);
        expect(&mut input, MAGIC)?;
        let header: Header = serde_json::from_slice(&read_blob(&mut input)?).map_err(invalid)?;
        let mut section = || ResidentSectionRest::read(&read_blob(&mut input)?).map_err(invalid);
        let seed = section()?;
        let memory = section()?;
        let basis = section()?;
        let mut emissions = Vec::new();
        for _ in &header.history {
            emissions.push(section()?);
        }
        expect(&mut input, END)?;
        if input.limit() != 0 {
            return Err(invalid("trailing native rest bytes"));
        }
        let rest = Self {
            header,
            seed,
            memory,
            basis,
            emissions,
        };
        rest.validate()?;
        Ok(rest)
    }
}

fn blob(out: &mut impl Write, bytes: &[u8]) -> Result<(), Error> {
    out.write_all(&(bytes.len() as u64).to_le_bytes())
        .map_err(invalid)?;
    out.write_all(bytes).map_err(invalid)
}
fn expect(input: &mut impl Read, expected: &[u8]) -> Result<(), Error> {
    let mut bytes = vec![0; expected.len()];
    input.read_exact(&mut bytes).map_err(invalid)?;
    if bytes != expected {
        return Err(invalid("native rest magic or end marker"));
    }
    Ok(())
}
fn read_blob(input: &mut Take<impl Read>) -> Result<Vec<u8>, Error> {
    let mut length = [0; 8];
    input.read_exact(&mut length).map_err(invalid)?;
    let mut remaining = u64::from_le_bytes(length);
    if remaining > input.limit() {
        return Err(invalid("blob exceeds containing wire"));
    }
    let mut bytes = Vec::new();
    let mut chunk = [0u8; 65536];
    while remaining > 0 {
        let n = remaining.min(chunk.len() as u64) as usize;
        input.read_exact(&mut chunk[..n]).map_err(invalid)?;
        bytes.try_reserve(n).map_err(invalid)?;
        bytes.extend_from_slice(&chunk[..n]);
        remaining -= n as u64;
    }
    Ok(bytes)
}

impl<'chart> NativeConstitutiveEcology<'chart> {
    /// Cold inspection retains actual state without cloning the live ecology. Handles not
    /// supplied here remain absent after remount, even if their emitted source was never received.
    pub fn rest(
        &self,
        handles: &[Option<&NativeEmissionHandle>],
    ) -> Result<NativeEcologyRest, Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        let mut materials: Vec<Rc<[NativeJunctionSeed]>> = Vec::new();
        let mut material_at = |m: &Rc<[NativeJunctionSeed]>| {
            if let Some(at) = materials.iter().position(|old| Rc::ptr_eq(old, m)) {
                at
            } else {
                materials.push(Rc::clone(m));
                materials.len() - 1
            }
        };
        let history = self
            .history
            .iter()
            .map(|h| EmissionWire {
                lineage: h.lineage.clone(),
                returned: h.returned,
                material: material_at(&h.material),
                frame: h.frame.view.ordinal as usize,
            })
            .collect();
        let current_material = material_at(&self.material);
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
        let source_slots = handles
            .iter()
            .map(|h| {
                h.map(|h| {
                    if !Rc::ptr_eq(&h.owner, &self.owner) {
                        return Err(Error::ForeignOccurrence);
                    }
                    Ok(h.occurrence)
                })
                .transpose()
            })
            .collect::<Result<_, _>>()?;
        let rest = NativeEcologyRest {
            header: Header {
                nodes: self.material.len(),
                current_material,
                materials: materials.iter().map(|m| m.to_vec()).collect(),
                frames,
                history,
                source_slots,
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
            },
            seed: self.relation.surface.detach_section(&self.seed, 64)?,
            memory: self.inspect_held()?,
            basis: self.inspect_relation()?,
            emissions: self
                .history
                .iter()
                .map(|h| {
                    self.relation
                        .surface
                        .detach_section(&h.section, 64)
                        .map_err(Error::from)
                })
                .collect::<Result<_, _>>()?,
        };
        rest.validate()?;
        Ok(rest)
    }

    /// Consume one complete cold chart into one newly scoped runtime owner. Old live-owner
    /// handles never authenticate against this owner. No exposure, current or formation repeats.
    pub fn remount(
        surface: &'chart ResidentSurface<'chart>,
        rest: NativeEcologyRest,
    ) -> Result<(Self, Vec<Option<NativeEmissionHandle>>), Error> {
        rest.validate()?;
        // The same apparatus scratch law as founding, before any native state allocation.
        let scratch =
            ResidentSurface::constitutive_circulation_scratch(rest.nodes()).ok_or(Error::Shape)?;
        let available = surface.declaration().max_sectiond_bytes;
        if scratch > available as usize {
            return Err(Error::ScratchAperture {
                required: scratch,
                available,
            });
        }
        let NativeEcologyRest {
            header: h,
            seed,
            memory,
            basis,
            emissions,
        } = rest;
        let materials = h
            .materials
            .into_iter()
            .map(Rc::<[NativeJunctionSeed]>::from)
            .collect::<Vec<_>>();
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
                let native = surface.mount_section_rest(
                    &ResidentSectionRest::found(h.nodes, 3, ResidentGrain(0), 64, words)
                        .map_err(invalid)?,
                )?;
                Ok(Rc::new(HeldCurrentFrame {
                    native,
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
                at.map(|occurrence| NativeEmissionHandle {
                    owner: Rc::clone(&owner),
                    occurrence,
                })
            })
            .collect();
        let occurrences = h.history.len() as u64;
        let history = h
            .history
            .into_iter()
            .zip(emissions)
            .map(|(h, s)| {
                Ok(HeldEmission {
                    section: surface.mount_section_rest(&s)?,
                    lineage: h.lineage,
                    returned: h.returned,
                    frame: Rc::clone(&frames[h.frame]),
                    material: Rc::clone(&materials[h.material]),
                })
            })
            .collect::<Result<_, Error>>()?;
        let body = Self {
            seed: surface.mount_section_rest(&seed)?,
            memory: surface.mount_section_rest(&memory)?,
            relation: ResidentConstitutiveFibre {
                basis: surface.mount_section_rest(&basis)?,
                surface,
                source_width: 2 * h.nodes,
                target_width: 2,
                occurrences,
                usable: true,
            },
            material: Rc::clone(&materials[h.current_material]),
            frame: Rc::clone(frames.last().expect("validated frames")),
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
            pending: None,
        };
        Ok((body, sources))
    }
}

#[cfg(test)]
mod tests;
