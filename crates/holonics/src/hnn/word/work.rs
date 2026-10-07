//! Exterior program work at the actual native owners, including declaring-basis Words.
//! Counts belong to the calling thread and never enter material, motion, clock or retention.
//! The notebook's one-thread interaction reads deltas after all indexed ring/contact work joins.
//! This vector counts named owner calls, not arithmetic operations, energy or device work.

use std::cell::Cell;

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct WorkRead {
    pub material_cut_attempts: u64,
    pub material_cuts: u64,
    pub word_open_attempts: u64,
    pub words_opened: u64,
    pub junction_attempts: u64,
    pub junctions: u64,
    pub full_ticks: u64,
    pub return_attempts: u64,
    pub returns: u64,
    /// A counter overflow makes the exterior reading unusable; it changes no native law.
    pub overflowed: bool,
}

thread_local! {
    static WORK: Cell<WorkRead> = Cell::new(WorkRead::default());
}

pub fn read() -> WorkRead {
    WORK.with(Cell::get)
}

impl WorkRead {
    /// Exact monotone difference, with no reset or snapshot of a native state.
    pub fn since(self, before: Self) -> Option<Self> {
        if self.overflowed || before.overflowed {
            return None;
        }
        Some(Self {
            material_cut_attempts: self
                .material_cut_attempts
                .checked_sub(before.material_cut_attempts)?,
            material_cuts: self.material_cuts.checked_sub(before.material_cuts)?,
            word_open_attempts: self
                .word_open_attempts
                .checked_sub(before.word_open_attempts)?,
            words_opened: self.words_opened.checked_sub(before.words_opened)?,
            junction_attempts: self
                .junction_attempts
                .checked_sub(before.junction_attempts)?,
            junctions: self.junctions.checked_sub(before.junctions)?,
            full_ticks: self.full_ticks.checked_sub(before.full_ticks)?,
            return_attempts: self.return_attempts.checked_sub(before.return_attempts)?,
            returns: self.returns.checked_sub(before.returns)?,
            overflowed: false,
        })
    }
}

pub(crate) enum Event {
    MaterialCutAttempt,
    MaterialCut,
    WordOpenAttempt,
    WordOpen,
    JunctionAttempt,
    Junction,
    FullTick,
    ReturnAttempt,
    Return,
}

pub(crate) fn reached(event: Event) {
    WORK.with(|cell| {
        let mut reading = cell.get();
        let counter = match event {
            Event::MaterialCutAttempt => &mut reading.material_cut_attempts,
            Event::MaterialCut => &mut reading.material_cuts,
            Event::WordOpenAttempt => &mut reading.word_open_attempts,
            Event::WordOpen => &mut reading.words_opened,
            Event::JunctionAttempt => &mut reading.junction_attempts,
            Event::Junction => &mut reading.junctions,
            Event::FullTick => &mut reading.full_ticks,
            Event::ReturnAttempt => &mut reading.return_attempts,
            Event::Return => &mut reading.returns,
        };
        match counter.checked_add(1) {
            Some(next) => *counter = next,
            None => reading.overflowed = true,
        }
        cell.set(reading);
    });
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::constitution::CAMPAIGN_ONE_BUDGET;
    use crate::hnn::tests::support::{contact, small_field};
    use crate::hnn::{Constitution, Current};

    #[test]
    fn work_read_includes_the_actual_declaring_basis_words_and_typed_failed_open() {
        let field = small_field(&[2, 3], vec![contact(0, 1, 2, 0)], 0);
        let material = Constitution::initial(&field, CAMPAIGN_ONE_BUDGET).unwrap();
        let current = Current::at_rest(&field);
        let before = read();
        let mut declaring = crate::hnn::receiving::DeclaringFace::new(&field);
        let (phases, reused) = declaring
            .declare(&material, &current, &field.receivers()[0])
            .unwrap();
        assert!(!reused);
        let work = read().since(before).unwrap();
        let basis = field
            .sources()
            .iter()
            .map(|&g| field.ring(g).width() as u64)
            .sum::<u64>();
        assert_eq!(work.words_opened, basis);
        assert_eq!(work.word_open_attempts, basis);
        assert_eq!(work.material_cuts, 1);
        assert_eq!(work.junctions, basis * phases.junction_steps() as u64);
        assert_eq!(
            work.full_ticks,
            basis * (phases.junction_steps() - 1) as u64
        );
        assert_eq!(work.returns, 0);
        let selected = read();
        assert!(
            declaring
                .declare(&material, &current, &field.receivers()[0])
                .unwrap()
                .1
        );
        assert_eq!(read().since(selected).unwrap(), WorkRead::default());
        let operands =
            crate::hnn::propagation::Operands::exact_at_cut(&field, &material, &current).unwrap();
        let failed = read();
        let malformed = crate::hnn::word::EndChange {
            storage: vec![],
            ..crate::hnn::word::EndChange::rest(&field, &operands)
        };
        assert!(matches!(
            crate::hnn::word::Word::continuing(&field, operands, &malformed, &[], 0),
            Err(crate::hnn::HnnError::Shape { .. })
        ));
        let refused = read().since(failed).unwrap();
        assert_eq!(refused.word_open_attempts, 1);
        assert_eq!(refused.words_opened, 0);
        assert_eq!(refused.junctions, 0);
    }
}
