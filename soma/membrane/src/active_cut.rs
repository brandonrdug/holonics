//! Allocation-owning host surface for [`soma_abi::active`].
//!
//! This owner retains an active cut as typed row populations.  Its optional word wire is durable
//! testimony and a parity instrument; live conduct uses the rows directly and never feeds that
//! serialization to Soma.

use body::num::COG_WORDS;
use soma_abi::active::{
    ActionCurrent, CutSpan, DirectedIncidence, EventSpan, Header, Incidence, OriginRef,
    RelationAtom, ValidationError, View,
};
use soma_abi::active::{CurrentSpan, CUT_WORDS, DIRECTED_WORDS, EVENT_WORDS, HEADER_WORDS};
use soma_abi::active::{INCIDENCE_WORDS, ORIGIN_WORDS};
use std::ops::Deref;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RowFamily {
    RelationAtom,
    Event,
    Action,
    Origin,
    Current,
    Cut,
    Incidence,
    Directed,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ActiveCutError {
    EmptyPopulation,
    Structural(ValidationError),
    ResourceExtent,
    ResourceReservation,
    WireExtent,
    Header,
    Row { family: RowFamily, ordinal: u64 },
}

impl From<ValidationError> for ActiveCutError {
    fn from(error: ValidationError) -> Self {
        Self::Structural(error)
    }
}

/// One complete, typed active-cut population.  Origin rows are listener provenance paired one to
/// one with events; every other row is the topology admitted to the execution boundary.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActiveCut {
    pub header: Header,
    pub atoms: Vec<RelationAtom>,
    pub events: Vec<EventSpan>,
    pub actions: Vec<ActionCurrent>,
    pub origins: Vec<OriginRef>,
    pub currents: Vec<CurrentSpan>,
    pub cuts: Vec<CutSpan>,
    pub incidences: Vec<Incidence>,
    pub directed: Vec<DirectedIncidence>,
}

/// Lifetime-bound proof that one immutable active cut has passed complete host validation.  The
/// borrow prevents row mutation while a passage is being prepared, so downstream membrane layers
/// can share the proof rather than rescanning the entire population at every current and fold.
#[derive(Clone, Copy)]
pub struct ValidatedActiveCut<'a>(&'a ActiveCut);

impl<'a> ValidatedActiveCut<'a> {
    pub fn active(self) -> &'a ActiveCut {
        self.0
    }
}

impl<'a> Deref for ValidatedActiveCut<'a> {
    type Target = ActiveCut;

    fn deref(&self) -> &Self::Target {
        self.0
    }
}

impl ActiveCut {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        atoms: Vec<RelationAtom>,
        events: Vec<EventSpan>,
        actions: Vec<ActionCurrent>,
        origins: Vec<OriginRef>,
        currents: Vec<CurrentSpan>,
        cuts: Vec<CutSpan>,
        incidences: Vec<Incidence>,
        directed: Vec<DirectedIncidence>,
    ) -> Result<Self, ActiveCutError> {
        let header = Header::new(
            atoms.len() as u64,
            events.len() as u64,
            currents.len() as u64,
            cuts.len() as u64,
            incidences.len() as u64,
            directed.len() as u64,
        )
        .ok_or(ActiveCutError::EmptyPopulation)?;
        let active = Self {
            header,
            atoms,
            events,
            actions,
            origins,
            currents,
            cuts,
            incidences,
            directed,
        };
        active.validate()?;
        Ok(active)
    }

    pub fn view(&self) -> View<'_> {
        View {
            header: self.header,
            atoms: &self.atoms,
            events: &self.events,
            actions: &self.actions,
            origins: &self.origins,
            currents: &self.currents,
            cuts: &self.cuts,
            incidences: &self.incidences,
            directed: &self.directed,
        }
    }

    pub fn validate(&self) -> Result<(), ActiveCutError> {
        let view = self.view();
        let extent = view
            .coverage_scratch_len()
            .ok_or(ActiveCutError::ResourceExtent)?;
        let mut scratch = Vec::new();
        scratch
            .try_reserve_exact(extent)
            .map_err(|_| ActiveCutError::ResourceReservation)?;
        scratch.resize(extent, 0i64);
        view.validate_with_scratch(&mut scratch).map_err(Into::into)
    }

    pub fn validated(&self) -> Result<ValidatedActiveCut<'_>, ActiveCutError> {
        self.validate()?;
        Ok(ValidatedActiveCut(self))
    }

    fn wire_extent(header: Header) -> Option<usize> {
        let families = [
            (header.atoms(), COG_WORDS),
            (header.events(), EVENT_WORDS),
            (header.events(), COG_WORDS),
            (header.events(), ORIGIN_WORDS),
            (header.currents(), soma_abi::active::CURRENT_WORDS),
            (header.cuts(), CUT_WORDS),
            (header.incidences(), INCIDENCE_WORDS),
            (header.directed(), DIRECTED_WORDS),
        ];
        let mut words = HEADER_WORDS;
        for (rows, width) in families {
            let rows = usize::try_from(rows).ok()?;
            words = words.checked_add(rows.checked_mul(width)?)?;
        }
        Some(words)
    }

    /// Canonical durable testimony.  This is never a source-current constructor.
    pub fn wire_words(&self) -> Vec<u32> {
        let mut words = Vec::with_capacity(
            Self::wire_extent(self.header).expect("a validated active cut has a host-sized wire"),
        );
        words.extend_from_slice(&self.header.words());
        for row in &self.atoms {
            words.extend_from_slice(&row.words());
        }
        for row in &self.events {
            words.extend_from_slice(&row.words());
        }
        for row in &self.actions {
            words.extend_from_slice(&row.words());
        }
        for row in &self.origins {
            words.extend_from_slice(&row.words());
        }
        for row in &self.currents {
            words.extend_from_slice(&row.words());
        }
        for row in &self.cuts {
            words.extend_from_slice(&row.words());
        }
        for row in &self.incidences {
            words.extend_from_slice(&row.words());
        }
        for row in &self.directed {
            words.extend_from_slice(&row.words());
        }
        words
    }

    pub fn from_wire_words(words: &[u32]) -> Result<Self, ActiveCutError> {
        let header_words = words
            .get(..HEADER_WORDS)
            .ok_or(ActiveCutError::WireExtent)?;
        let header = Header::from_words(
            header_words
                .try_into()
                .map_err(|_| ActiveCutError::Header)?,
        )
        .ok_or(ActiveCutError::Header)?;
        if Self::wire_extent(header) != Some(words.len()) {
            return Err(ActiveCutError::WireExtent);
        }
        let mut cursor = HEADER_WORDS;

        macro_rules! rows {
            ($count:expr, $width:expr, $family:expr, $parse:expr) => {{
                let mut out = Vec::with_capacity($count as usize);
                let mut ordinal = 0u64;
                while ordinal < $count {
                    let end = cursor
                        .checked_add($width)
                        .ok_or(ActiveCutError::WireExtent)?;
                    let row = words.get(cursor..end).ok_or(ActiveCutError::WireExtent)?;
                    cursor = end;
                    let row = row.try_into().map_err(|_| ActiveCutError::Row {
                        family: $family,
                        ordinal,
                    })?;
                    out.push(($parse)(row).ok_or(ActiveCutError::Row {
                        family: $family,
                        ordinal,
                    })?);
                    ordinal += 1;
                }
                out
            }};
        }

        let atoms = rows!(
            header.atoms(),
            COG_WORDS,
            RowFamily::RelationAtom,
            RelationAtom::from_words
        );
        let events = rows!(
            header.events(),
            EVENT_WORDS,
            RowFamily::Event,
            EventSpan::from_words
        );
        let actions = rows!(
            header.events(),
            COG_WORDS,
            RowFamily::Action,
            ActionCurrent::from_words
        );

        let mut origins = Vec::with_capacity(header.events() as usize);
        let mut origin = 0u64;
        while origin < header.events() {
            let end = cursor
                .checked_add(ORIGIN_WORDS)
                .ok_or(ActiveCutError::WireExtent)?;
            let row = words.get(cursor..end).ok_or(ActiveCutError::WireExtent)?;
            cursor = end;
            let row = row.try_into().map_err(|_| ActiveCutError::Row {
                family: RowFamily::Origin,
                ordinal: origin,
            })?;
            origins.push(OriginRef::from_words(row));
            origin += 1;
        }

        let currents = rows!(
            header.currents(),
            soma_abi::active::CURRENT_WORDS,
            RowFamily::Current,
            CurrentSpan::from_words
        );
        let cuts = rows!(
            header.cuts(),
            CUT_WORDS,
            RowFamily::Cut,
            CutSpan::from_words
        );
        let incidences = rows!(
            header.incidences(),
            INCIDENCE_WORDS,
            RowFamily::Incidence,
            Incidence::from_words
        );

        let mut directed = Vec::with_capacity(header.directed() as usize);
        let mut edge = 0u64;
        while edge < header.directed() {
            let end = cursor
                .checked_add(DIRECTED_WORDS)
                .ok_or(ActiveCutError::WireExtent)?;
            let row = words.get(cursor..end).ok_or(ActiveCutError::WireExtent)?;
            cursor = end;
            let row = row.try_into().map_err(|_| ActiveCutError::Row {
                family: RowFamily::Directed,
                ordinal: edge,
            })?;
            directed.push(DirectedIncidence::from_words(row));
            edge += 1;
        }

        if cursor != words.len() {
            return Err(ActiveCutError::WireExtent);
        }
        let active = Self {
            header,
            atoms,
            events,
            actions,
            origins,
            currents,
            cuts,
            incidences,
            directed,
        };
        active.validate()?;
        Ok(active)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::num::Cog;

    fn relation_cut(origins: [OriginRef; 2]) -> ActiveCut {
        ActiveCut::new(
            vec![
                RelationAtom::new(Cog::lit(3)).unwrap(),
                RelationAtom::new(Cog::lit(-5).turn_up(2)).unwrap(),
                RelationAtom::new(Cog::lit(11).turned(1)).unwrap(),
            ],
            vec![EventSpan::new(0, 2).unwrap(), EventSpan::new(2, 1).unwrap()],
            vec![
                ActionCurrent::new(Cog::lit(29)).unwrap(),
                ActionCurrent::new(Cog::lit(31).turn_up(1)).unwrap(),
            ],
            origins.to_vec(),
            vec![
                CurrentSpan::new(0, 1, 0, 2).unwrap(),
                CurrentSpan::new(1, 1, 2, 1).unwrap(),
            ],
            vec![CutSpan::new(0, 2, 0, 1).unwrap()],
            vec![
                Incidence::new(0, 0, 1).unwrap(),
                Incidence::new(1, 0, 1).unwrap(),
            ],
            vec![DirectedIncidence::new(0, 1)],
        )
        .unwrap()
    }

    #[test]
    fn typed_active_cut_round_trips_without_becoming_source_light() {
        let active = relation_cut([OriginRef::new(2, 3), OriginRef::new(5, 8)]);
        let wire = active.wire_words();
        assert_eq!(ActiveCut::from_wire_words(&wire).unwrap(), active);

        let mut truncated = wire.clone();
        truncated.pop();
        assert_eq!(
            ActiveCut::from_wire_words(&truncated),
            Err(ActiveCutError::WireExtent)
        );
    }

    #[test]
    fn provenance_changes_without_changing_relation_topology() {
        let left = relation_cut([OriginRef::new(1, 13), OriginRef::new(1, 21)]);
        let right = relation_cut([OriginRef::new(144, 233), OriginRef::new(144, 377)]);
        assert_ne!(left.origins, right.origins);
        assert_eq!(left.atoms, right.atoms);
        assert_eq!(left.events, right.events);
        assert_eq!(left.actions, right.actions);
        assert_eq!(left.currents, right.currents);
        assert_eq!(left.cuts, right.cuts);
        assert_eq!(left.incidences, right.incidences);
        assert_eq!(left.directed, right.directed);
    }
}
