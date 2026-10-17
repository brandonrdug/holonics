//! Borrowed reverse operands for the actual Word and its same-cut response columns (F2).
//!
//! A column shares the producing operators, clock and overwrite schedule, not the actual
//! trajectory's waves. This view owns no motion or retained history and opens no Word. Shape
//! admission is not a proof of execution: only the native column producer may supply its waves.
//! The reverse-core consumer is joined after the passage-frame (F1) integration.

use super::{Passage, Resonance, SourceWaveReturn, Word};
use crate::hnn::propagation::Operands;
use crate::hnn::{Field, HnnError};

/// A temporary view used by one reverse sweep. The producing Word pins the field, operators,
/// physical tick origin, terminal-junction convention and held exterior overwrite schedule.
/// Only the waves and loaded-port steps vary between the actual and column trajectories.
pub(crate) struct TrajectoryView<'a, 'c> {
    producing: &'a Word<'c>,
    records: &'a [Passage],
    resonances: &'a [Option<Resonance>],
    response: bool,
}

impl<'a, 'c> TrajectoryView<'a, 'c> {
    pub(crate) fn actual(word: &'a Word<'c>) -> Self {
        Self {
            producing: word,
            records: word.recorded(),
            resonances: word.resonances(),
            response: false,
        }
    }

    /// Admit column operands on exactly the producing Word's crossings and loaded-port phases.
    /// An exterior overwrite's response is zero when its reflected wave is held; the matching
    /// reverse schedule below kills that storage covector. A responsive exterior needs its own
    /// linearized boundary operator and is not implied by this view.
    pub(crate) fn column(
        producing: &'a Word<'c>,
        records: &'a [Passage],
        resonances: &'a [Option<Resonance>],
    ) -> Result<Self, HnnError> {
        let refuse = || HnnError::Unadmitted {
            reason: "a response trajectory keeps its producing Word's complete shape and crossing schedule",
        };
        let ops = producing.operands();
        let widths: Vec<_> = producing
            .field()
            .rings()
            .iter()
            .map(|r| r.width())
            .collect();
        let waves = |values: &[Vec<_>]| {
            values.len() == widths.len() && values.iter().zip(&widths).all(|(v, &w)| v.len() == w)
        };
        if records.len() != producing.recorded().len() || resonances.len() != widths.len() {
            return Err(refuse());
        }
        for (at, record) in records.iter().enumerate() {
            let full = at + 1 < records.len() || !producing.is_ended();
            if !waves(&record.storage)
                || !waves(&record.anchors)
                || record.arrivals.len() != ops.contacts().len()
                || record.states.len() != ops.contacts().len()
                || record
                    .arrivals
                    .iter()
                    .zip(ops.contacts())
                    .any(|(pair, contact)| {
                        let (a, b) = contact.ends();
                        pair[0].len() != widths[a] || pair[1].len() != widths[b]
                    })
                || record
                    .states
                    .iter()
                    .zip(ops.contacts())
                    .any(|(pair, contact)| pair.iter().any(|v| v.len() != contact.width()))
                || (full
                    && (!waves(&record.midpoints)
                        || record.rates.len() != ops.contacts().len()
                        || record
                            .rates
                            .iter()
                            .zip(ops.contacts())
                            .any(|(v, c)| v.len() != c.width())))
                || (!full && (!record.midpoints.is_empty() || !record.rates.is_empty()))
            {
                return Err(refuse());
            }
        }
        let full_ticks = records
            .len()
            .saturating_sub(usize::from(producing.is_ended()));
        for (ring, (column, actual)) in resonances.iter().zip(producing.resonances()).enumerate() {
            match (column, actual) {
                (None, None) => {}
                (Some(column), Some(actual)) => {
                    if column.steps.len() != full_ticks
                        || actual.steps.len() != full_ticks
                        || column.state.iter().any(|v| v.len() != widths[ring])
                        || column.steps.iter().zip(&actual.steps).any(|(a, b)| {
                            a.phase != b.phase
                                || a.input
                                    .iter()
                                    .chain(&a.state)
                                    .any(|v| v.len() != widths[ring])
                                || [&a.drive, &a.right, &a.output, &a.rate]
                                    .iter()
                                    .any(|v| v.len() != widths[ring])
                        })
                    {
                        return Err(refuse());
                    }
                }
                _ => return Err(refuse()),
            }
        }
        Ok(Self {
            producing,
            records,
            resonances,
            response: true,
        })
    }

    pub(crate) fn is_response(&self) -> bool {
        self.response
    }

    pub(crate) fn field(&self) -> &'c Field {
        self.producing.field()
    }
    pub(crate) fn operands(&self) -> &Operands {
        self.producing.operands()
    }
    pub(crate) fn recorded(&self) -> &[Passage] {
        self.records
    }
    pub(crate) fn resonances(&self) -> &[Option<Resonance>] {
        self.resonances
    }
    pub(crate) fn is_ended(&self) -> bool {
        self.producing.is_ended()
    }
    pub(crate) fn opened_at(&self) -> usize {
        self.producing.opened_at()
    }
    pub(crate) fn source_returns(&self) -> &[SourceWaveReturn] {
        self.producing.source_returns()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    use crate::hnn::{Constitution, Current, FieldDeclaration};
    use crate::ratio::integer;

    fn field() -> Field {
        let mut d = FieldDeclaration::campaign_one(1024);
        d.rings.truncate(2);
        for (ring, n) in d.rings.iter_mut().zip([2u64, 3]) {
            ring.period = n;
            ring.placements = (0..n)
                .map(|i| FieldDeclaration::quarter_turn(i, n))
                .collect();
            ring.reflector = (0..n).map(|i| ((n - i) % n) as usize).collect();
        }
        d.contacts.truncate(1);
        d.contacts[0].channel = vec![(0, 0), (1, 1)];
        d.loops.clear();
        d.alphabet = 2;
        d.receivers[0].ring = 1;
        d.receivers[0].depth = 2;
        d.crib.window = 2;
        d.lattice.clear();
        Field::declare(d.by_lattice_rule()).unwrap()
    }

    #[test]
    fn response_trajectory_borrows_operators_but_keeps_its_own_waves() {
        let field = field();
        let theta = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let storage = field
            .rings()
            .iter()
            .map(|r| vec![integer(0); r.width()])
            .collect();
        let mut word = Word::open_on(&field, &theta, &Current::at_rest(&field), storage).unwrap();
        word.tick().unwrap();
        word.last_junction().unwrap();
        let actual = TrajectoryView::actual(&word);
        let mut records = word.recorded().to_vec();
        records[0].anchors[0][0] = integer(7);
        let view = TrajectoryView::column(&word, &records, word.resonances()).unwrap();
        assert!(std::ptr::eq(view.operands(), actual.operands()));
        assert!(std::ptr::eq(view.field(), actual.field()));
        assert_eq!(view.recorded()[0].anchors[0][0], integer(7));
        assert_eq!(actual.recorded()[0].anchors[0][0], integer(0));
        assert_eq!(view.opened_at(), actual.opened_at());
        assert_eq!(view.source_returns(), actual.source_returns());
        assert!(view.is_ended());
        assert_eq!(view.resonances(), actual.resonances());
        // Shape checks never replace the column producer's execution/provenance guarantee.
        assert!(TrajectoryView::column(&word, &records[..1], word.resonances()).is_err());
        let mut truncated = records.clone();
        truncated[0].arrivals[0][1].pop();
        assert!(TrajectoryView::column(&word, &truncated, word.resonances()).is_err());
        let mut wrong_final = records.clone();
        wrong_final[1].midpoints = records[0].midpoints.clone();
        assert!(TrajectoryView::column(&word, &wrong_final, word.resonances()).is_err());
        assert!(TrajectoryView::column(&word, &records, &[]).is_err());
    }
}
