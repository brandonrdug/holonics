//! Exact composition of independently closed source cuts into one co-present boundary.
//!
//! Every source organ has already decided which of its material boundaries actually closed. This
//! module only rebases row references so those populations can meet one immutable Soma before-face
//! and commit one successor. It adds no separator atom, modality marker, cross-source edge,
//! priority, score, or storage-order cause.

use std::sync::Arc;

use soma_abi::active::{CurrentSpan, CutSpan, DirectedIncidence, EventSpan, Incidence};

use crate::{ActiveCut, ActiveCutError};

#[derive(Clone)]
pub struct SelectedCut {
    pub active: Arc<ActiveCut>,
    pub closed_cut: u64,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RowRange {
    offset: u64,
    extent: u64,
}

impl RowRange {
    pub const fn offset(self) -> u64 {
        self.offset
    }

    pub const fn extent(self) -> u64 {
        self.extent
    }

    pub fn contains(self, ordinal: u64) -> bool {
        ordinal >= self.offset
            && ordinal
                < self
                    .offset
                    .checked_add(self.extent)
                    .expect("a composed range was checked before construction")
    }
}

/// Exact reversible placement of one selected source population inside the composed cut.
#[derive(Clone)]
pub struct CutEmbedding {
    source: Arc<ActiveCut>,
    source_cut: u64,
    atoms: RowRange,
    events: RowRange,
    currents: RowRange,
    source_incidence_offset: u64,
    incidences: RowRange,
    source_directed_offset: u64,
    directed: RowRange,
}

impl CutEmbedding {
    pub fn source(&self) -> &Arc<ActiveCut> {
        &self.source
    }

    pub const fn source_cut(&self) -> u64 {
        self.source_cut
    }

    pub const fn atoms(&self) -> RowRange {
        self.atoms
    }

    pub const fn events(&self) -> RowRange {
        self.events
    }

    pub const fn currents(&self) -> RowRange {
        self.currents
    }

    pub const fn incidences(&self) -> RowRange {
        self.incidences
    }

    pub const fn directed(&self) -> RowRange {
        self.directed
    }

    pub fn composite_atom(&self, local: u64) -> Option<u64> {
        (local < self.atoms.extent).then(|| self.atoms.offset + local)
    }

    pub fn composite_event(&self, local: u64) -> Option<u64> {
        (local < self.events.extent).then(|| self.events.offset + local)
    }

    pub fn composite_current(&self, local: u64) -> Option<u64> {
        (local < self.currents.extent).then(|| self.currents.offset + local)
    }

    pub fn composite_incidence(&self, source_ordinal: u64) -> Option<u64> {
        let local = source_ordinal.checked_sub(self.source_incidence_offset)?;
        (local < self.incidences.extent).then(|| self.incidences.offset + local)
    }

    pub fn composite_directed(&self, source_ordinal: u64) -> Option<u64> {
        let local = source_ordinal.checked_sub(self.source_directed_offset)?;
        (local < self.directed.extent).then(|| self.directed.offset + local)
    }

    pub fn source_atom(&self, composite: u64) -> Option<u64> {
        composite
            .checked_sub(self.atoms.offset)
            .filter(|local| *local < self.atoms.extent)
    }

    pub fn source_event(&self, composite: u64) -> Option<u64> {
        composite
            .checked_sub(self.events.offset)
            .filter(|local| *local < self.events.extent)
    }

    pub fn source_current(&self, composite: u64) -> Option<u64> {
        composite
            .checked_sub(self.currents.offset)
            .filter(|local| *local < self.currents.extent)
    }

    pub fn source_incidence(&self, composite: u64) -> Option<u64> {
        let local = composite.checked_sub(self.incidences.offset)?;
        (local < self.incidences.extent).then(|| self.source_incidence_offset + local)
    }

    pub fn source_directed(&self, composite: u64) -> Option<u64> {
        let local = composite.checked_sub(self.directed.offset)?;
        (local < self.directed.extent).then(|| self.source_directed_offset + local)
    }
}

pub struct CoPresentCut {
    pub active: Arc<ActiveCut>,
    /// The composed population has exactly one actual receiving cut.
    pub closed_cut: u64,
    pub embeddings: Vec<CutEmbedding>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ComposeCutError {
    EmptyPopulation,
    CutAbsent { part: u64, cut: u64 },
    SelectedCutIncomplete { part: u64, cut: u64 },
    ResourceExtent,
    ResourceReservation,
    Active { part: u64, error: ActiveCutError },
    Composed(ActiveCutError),
}

impl ComposeCutError {
    /// Source-part ordinal when the refusal belongs to one selected contribution. The ordinal is
    /// only a compositor-local row; a frontier maps it back to material ownership.
    pub const fn part(self) -> Option<u64> {
        match self {
            Self::CutAbsent { part, .. }
            | Self::SelectedCutIncomplete { part, .. }
            | Self::Active { part, .. } => Some(part),
            Self::EmptyPopulation
            | Self::ResourceExtent
            | Self::ResourceReservation
            | Self::Composed(_) => None,
        }
    }
}

fn add(a: u64, b: u64) -> Result<u64, ComposeCutError> {
    a.checked_add(b).ok_or(ComposeCutError::ResourceExtent)
}

fn range(offset: u64, extent: u64) -> Result<RowRange, ComposeCutError> {
    let _ = add(offset, extent)?;
    Ok(RowRange { offset, extent })
}

fn selected_cut_complete(active: &ActiveCut, cut: CutSpan) -> Result<bool, ComposeCutError> {
    let event_extent =
        usize::try_from(active.header.events()).map_err(|_| ComposeCutError::ResourceExtent)?;
    let current_extent =
        usize::try_from(active.header.currents()).map_err(|_| ComposeCutError::ResourceExtent)?;
    let event_scratch = event_extent
        .checked_add(1)
        .ok_or(ComposeCutError::ResourceExtent)?;
    let mut coverage = Vec::new();
    coverage
        .try_reserve_exact(event_scratch)
        .map_err(|_| ComposeCutError::ResourceReservation)?;
    coverage.resize(event_scratch, 0i64);
    let mut currents = Vec::new();
    currents
        .try_reserve_exact(current_extent)
        .map_err(|_| ComposeCutError::ResourceReservation)?;
    currents.resize(current_extent, false);

    let after = add(cut.incidence_offset(), cut.incidences())?;
    for ordinal in cut.incidence_offset()..after {
        let incidence = active
            .incidences
            .get(usize::try_from(ordinal).map_err(|_| ComposeCutError::ResourceExtent)?)
            .copied()
            .ok_or(ComposeCutError::ResourceExtent)?;
        let current_index =
            usize::try_from(incidence.current()).map_err(|_| ComposeCutError::ResourceExtent)?;
        let current = active
            .currents
            .get(current_index)
            .copied()
            .ok_or(ComposeCutError::ResourceExtent)?;
        currents[current_index] = true;
        let first = add(current.event_offset(), incidence.current_event_offset())?;
        let after = add(first, incidence.current_events())?;
        let first = usize::try_from(first).map_err(|_| ComposeCutError::ResourceExtent)?;
        let after = usize::try_from(after).map_err(|_| ComposeCutError::ResourceExtent)?;
        coverage[first] = coverage[first]
            .checked_add(1)
            .ok_or(ComposeCutError::ResourceExtent)?;
        coverage[after] = coverage[after]
            .checked_sub(1)
            .ok_or(ComposeCutError::ResourceExtent)?;
    }
    if currents.iter().any(|covered| !covered) {
        return Ok(false);
    }
    let mut live = 0i64;
    for delta in &coverage[..event_extent] {
        live = live
            .checked_add(*delta)
            .ok_or(ComposeCutError::ResourceExtent)?;
        if live <= 0 {
            return Ok(false);
        }
    }
    Ok(live
        .checked_add(coverage[event_extent])
        .ok_or(ComposeCutError::ResourceExtent)?
        == 0)
}

/// Compose every selected complete cut into one co-present population.
///
/// Source order is a row-layout gauge. Callers which need byte-identical layout across readiness
/// enumeration provide a stable non-semantic port order before this function; no row order is used
/// by this function to add a causal edge.
pub fn compose_selected_cuts(parts: Vec<SelectedCut>) -> Result<CoPresentCut, ComposeCutError> {
    if parts.is_empty() {
        return Err(ComposeCutError::EmptyPopulation);
    }

    let mut atoms = Vec::new();
    let mut events = Vec::new();
    let mut actions = Vec::new();
    let mut origins = Vec::new();
    let mut currents = Vec::new();
    let mut incidences = Vec::new();
    let mut directed = Vec::new();
    let mut embeddings = Vec::new();
    embeddings
        .try_reserve_exact(parts.len())
        .map_err(|_| ComposeCutError::ResourceReservation)?;

    for (part_index, part) in parts.into_iter().enumerate() {
        part.active
            .validate()
            .map_err(|error| ComposeCutError::Active {
                part: part_index as u64,
                error,
            })?;
        let source_cut = part
            .active
            .cuts
            .get(
                usize::try_from(part.closed_cut).map_err(|_| ComposeCutError::CutAbsent {
                    part: part_index as u64,
                    cut: part.closed_cut,
                })?,
            )
            .copied()
            .ok_or(ComposeCutError::CutAbsent {
                part: part_index as u64,
                cut: part.closed_cut,
            })?;
        if !selected_cut_complete(&part.active, source_cut)? {
            return Err(ComposeCutError::SelectedCutIncomplete {
                part: part_index as u64,
                cut: part.closed_cut,
            });
        }

        let atom_offset =
            u64::try_from(atoms.len()).map_err(|_| ComposeCutError::ResourceExtent)?;
        let event_offset =
            u64::try_from(events.len()).map_err(|_| ComposeCutError::ResourceExtent)?;
        let current_offset =
            u64::try_from(currents.len()).map_err(|_| ComposeCutError::ResourceExtent)?;
        let incidence_offset =
            u64::try_from(incidences.len()).map_err(|_| ComposeCutError::ResourceExtent)?;
        let directed_offset =
            u64::try_from(directed.len()).map_err(|_| ComposeCutError::ResourceExtent)?;

        atoms
            .try_reserve(part.active.atoms.len())
            .map_err(|_| ComposeCutError::ResourceReservation)?;
        events
            .try_reserve(part.active.events.len())
            .map_err(|_| ComposeCutError::ResourceReservation)?;
        actions
            .try_reserve(part.active.actions.len())
            .map_err(|_| ComposeCutError::ResourceReservation)?;
        origins
            .try_reserve(part.active.origins.len())
            .map_err(|_| ComposeCutError::ResourceReservation)?;
        currents
            .try_reserve(part.active.currents.len())
            .map_err(|_| ComposeCutError::ResourceReservation)?;
        incidences
            .try_reserve(
                usize::try_from(source_cut.incidences())
                    .map_err(|_| ComposeCutError::ResourceExtent)?,
            )
            .map_err(|_| ComposeCutError::ResourceReservation)?;
        directed
            .try_reserve(
                usize::try_from(source_cut.directed())
                    .map_err(|_| ComposeCutError::ResourceExtent)?,
            )
            .map_err(|_| ComposeCutError::ResourceReservation)?;

        atoms.extend_from_slice(&part.active.atoms);
        for event in &part.active.events {
            events.push(
                EventSpan::new(add(atom_offset, event.atom_offset())?, event.atoms())
                    .ok_or(ComposeCutError::ResourceExtent)?,
            );
        }
        actions.extend_from_slice(&part.active.actions);
        origins.extend_from_slice(&part.active.origins);
        for current in &part.active.currents {
            currents.push(
                CurrentSpan::new(
                    add(event_offset, current.event_offset())?,
                    current.events(),
                    add(atom_offset, current.atom_offset())?,
                    current.atoms(),
                )
                .ok_or(ComposeCutError::ResourceExtent)?,
            );
        }

        let source_incidence_after = add(source_cut.incidence_offset(), source_cut.incidences())?;
        for source in source_cut.incidence_offset()..source_incidence_after {
            let incidence = part.active.incidences
                [usize::try_from(source).map_err(|_| ComposeCutError::ResourceExtent)?];
            incidences.push(
                Incidence::new(
                    add(current_offset, incidence.current())?,
                    incidence.current_event_offset(),
                    incidence.current_events(),
                )
                .ok_or(ComposeCutError::ResourceExtent)?,
            );
        }

        let source_directed_offset = if source_cut.directed() == 0 {
            0
        } else {
            source_cut.directed_offset()
        };
        let source_directed_after = add(source_directed_offset, source_cut.directed())?;
        for source in source_directed_offset..source_directed_after {
            let edge = part.active.directed
                [usize::try_from(source).map_err(|_| ComposeCutError::ResourceExtent)?];
            let from_local = edge
                .from_incidence()
                .checked_sub(source_cut.incidence_offset())
                .ok_or(ComposeCutError::ResourceExtent)?;
            let to_local = edge
                .to_incidence()
                .checked_sub(source_cut.incidence_offset())
                .ok_or(ComposeCutError::ResourceExtent)?;
            directed.push(DirectedIncidence::new(
                add(incidence_offset, from_local)?,
                add(incidence_offset, to_local)?,
            ));
        }

        embeddings.push(CutEmbedding {
            source: part.active.clone(),
            source_cut: part.closed_cut,
            atoms: range(atom_offset, part.active.header.atoms())?,
            events: range(event_offset, part.active.header.events())?,
            currents: range(current_offset, part.active.header.currents())?,
            source_incidence_offset: source_cut.incidence_offset(),
            incidences: range(incidence_offset, source_cut.incidences())?,
            source_directed_offset,
            directed: range(directed_offset, source_cut.directed())?,
        });
    }

    let incidence_extent =
        u64::try_from(incidences.len()).map_err(|_| ComposeCutError::ResourceExtent)?;
    let directed_extent =
        u64::try_from(directed.len()).map_err(|_| ComposeCutError::ResourceExtent)?;
    let active = ActiveCut::new(
        atoms,
        events,
        actions,
        origins,
        currents,
        vec![CutSpan::new(0, incidence_extent, 0, directed_extent)
            .ok_or(ComposeCutError::ResourceExtent)?],
        incidences,
        directed,
    )
    .map_err(ComposeCutError::Composed)?;
    Ok(CoPresentCut {
        active: Arc::new(active),
        closed_cut: 0,
        embeddings,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::num::Cog;
    use soma_abi::active::{ActionCurrent, OriginRef, RelationAtom};

    fn source(organ: u64, first: i64, reverse: bool) -> Arc<ActiveCut> {
        let edge = if reverse {
            DirectedIncidence::new(1, 0)
        } else {
            DirectedIncidence::new(0, 1)
        };
        Arc::new(
            ActiveCut::new(
                vec![
                    RelationAtom::new(Cog::lit(first)).unwrap(),
                    RelationAtom::new(Cog::lit(first + 1)).unwrap(),
                ],
                vec![EventSpan::new(0, 1).unwrap(), EventSpan::new(1, 1).unwrap()],
                vec![
                    ActionCurrent::new(Cog::lit(3)).unwrap(),
                    ActionCurrent::new(Cog::lit(5)).unwrap(),
                ],
                vec![OriginRef::new(organ, 17), OriginRef::new(organ, 23)],
                vec![CurrentSpan::new(0, 2, 0, 2).unwrap()],
                vec![CutSpan::new(0, 2, 0, 1).unwrap()],
                vec![
                    Incidence::new(0, 0, 1).unwrap(),
                    Incidence::new(0, 1, 1).unwrap(),
                ],
                vec![edge],
            )
            .unwrap(),
        )
    }

    fn repeated_complete_cuts(organ: u64) -> Arc<ActiveCut> {
        Arc::new(
            ActiveCut::new(
                vec![
                    RelationAtom::new(Cog::lit(11)).unwrap(),
                    RelationAtom::new(Cog::lit(13)).unwrap(),
                ],
                vec![EventSpan::new(0, 1).unwrap(), EventSpan::new(1, 1).unwrap()],
                vec![
                    ActionCurrent::new(Cog::lit(17)).unwrap(),
                    ActionCurrent::new(Cog::lit(19)).unwrap(),
                ],
                vec![OriginRef::new(organ, 101), OriginRef::new(organ, 103)],
                vec![CurrentSpan::new(0, 2, 0, 2).unwrap()],
                vec![
                    CutSpan::new(0, 2, 0, 1).unwrap(),
                    CutSpan::new(2, 2, 1, 1).unwrap(),
                ],
                vec![
                    Incidence::new(0, 0, 1).unwrap(),
                    Incidence::new(0, 1, 1).unwrap(),
                    Incidence::new(0, 0, 1).unwrap(),
                    Incidence::new(0, 1, 1).unwrap(),
                ],
                vec![DirectedIncidence::new(0, 1), DirectedIncidence::new(2, 3)],
            )
            .unwrap(),
        )
    }

    fn partial_cuts() -> Arc<ActiveCut> {
        Arc::new(
            ActiveCut::new(
                vec![
                    RelationAtom::new(Cog::lit(2)).unwrap(),
                    RelationAtom::new(Cog::lit(3)).unwrap(),
                ],
                vec![EventSpan::new(0, 1).unwrap(), EventSpan::new(1, 1).unwrap()],
                vec![
                    ActionCurrent::new(Cog::lit(1)).unwrap(),
                    ActionCurrent::new(Cog::lit(1)).unwrap(),
                ],
                vec![OriginRef::new(5, 0), OriginRef::new(5, 1)],
                vec![
                    CurrentSpan::new(0, 1, 0, 1).unwrap(),
                    CurrentSpan::new(1, 1, 1, 1).unwrap(),
                ],
                vec![
                    CutSpan::new(0, 1, 0, 0).unwrap(),
                    CutSpan::new(1, 1, 0, 0).unwrap(),
                ],
                vec![
                    Incidence::new(0, 0, 1).unwrap(),
                    Incidence::new(1, 0, 1).unwrap(),
                ],
                Vec::new(),
            )
            .unwrap(),
        )
    }

    #[test]
    fn selected_populations_share_one_cut_without_cross_source_edges() {
        let a = source(11, 2, false);
        let b = source(29, 7, true);
        let composed = compose_selected_cuts(vec![
            SelectedCut {
                active: a.clone(),
                closed_cut: 0,
            },
            SelectedCut {
                active: b.clone(),
                closed_cut: 0,
            },
        ])
        .unwrap();
        assert_eq!(composed.active.header.currents(), 2);
        assert_eq!(composed.active.header.events(), 4);
        assert_eq!(composed.active.header.cuts(), 1);
        assert_eq!(composed.active.header.incidences(), 4);
        assert_eq!(composed.active.header.directed(), 2);
        assert_eq!(composed.active.directed[0], DirectedIncidence::new(0, 1));
        assert_eq!(composed.active.directed[1], DirectedIncidence::new(3, 2));
        assert!(Arc::ptr_eq(composed.embeddings[0].source(), &a));
        assert!(Arc::ptr_eq(composed.embeddings[1].source(), &b));
        assert_eq!(composed.embeddings[1].composite_event(0), Some(2));
        assert_eq!(composed.embeddings[1].composite_current(0), Some(1));
        assert_eq!(composed.embeddings[1].composite_incidence(0), Some(2));
        assert_eq!(composed.embeddings[1].composite_directed(0), Some(1));
    }

    #[test]
    fn nonzero_source_cut_offsets_rebase_and_reverse_exactly() {
        let first = source(7, 23, false);
        let second = repeated_complete_cuts(41);
        let composed = compose_selected_cuts(vec![
            SelectedCut {
                active: first,
                closed_cut: 0,
            },
            SelectedCut {
                active: second.clone(),
                closed_cut: 1,
            },
        ])
        .unwrap();
        let map = &composed.embeddings[1];
        assert_eq!(
            map.atoms(),
            RowRange {
                offset: 2,
                extent: 2
            }
        );
        assert_eq!(
            map.events(),
            RowRange {
                offset: 2,
                extent: 2
            }
        );
        assert_eq!(
            map.currents(),
            RowRange {
                offset: 1,
                extent: 1
            }
        );
        assert_eq!(
            map.incidences(),
            RowRange {
                offset: 2,
                extent: 2
            }
        );
        assert_eq!(
            map.directed(),
            RowRange {
                offset: 1,
                extent: 1
            }
        );
        assert_eq!(map.composite_atom(1), Some(3));
        assert_eq!(map.source_atom(3), Some(1));
        assert_eq!(map.composite_event(1), Some(3));
        assert_eq!(map.source_event(3), Some(1));
        assert_eq!(map.composite_current(0), Some(1));
        assert_eq!(map.source_current(1), Some(0));
        assert_eq!(map.composite_incidence(2), Some(2));
        assert_eq!(map.composite_incidence(3), Some(3));
        assert_eq!(map.source_incidence(2), Some(2));
        assert_eq!(map.source_incidence(3), Some(3));
        assert_eq!(map.composite_directed(1), Some(1));
        assert_eq!(map.source_directed(1), Some(1));
        assert_eq!(composed.active.directed[1], DirectedIncidence::new(2, 3));
        assert_eq!(composed.active.actions[2], second.actions[0]);
        assert_eq!(composed.active.origins[3], second.origins[1]);
    }

    #[test]
    fn a_selected_cut_must_carry_the_complete_source_population() {
        let active = partial_cuts();
        for cut in 0..2 {
            assert!(matches!(
                compose_selected_cuts(vec![SelectedCut {
                    active: active.clone(),
                    closed_cut: cut,
                }]),
                Err(ComposeCutError::SelectedCutIncomplete { part: 0, cut: actual })
                    if actual == cut
            ));
        }
    }
}
