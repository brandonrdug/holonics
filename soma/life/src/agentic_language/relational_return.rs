use holonic_structure::{LocalRelations, LocalSequence, LocalSet};

use crate::relational_language::{RelationalThoughtCurrent, RelationalThoughtFiber};

/// The exact pre-answer current selected by the language receiver, together with the other
/// co-present currents which the same deed retained. This is a typed boundary face; callers do
/// not receive the deed-indexed standing which owns it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct AnswerSelectedRelationalCurrent {
    pub current: RelationalThoughtCurrent,
    pub minimal_closed_witness_family: LocalSet<String>,
    pub alternatives: LocalSequence<RelationalThoughtCurrent>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct DeedRelationalReturn {
    fibers: LocalSequence<RelationalThoughtFiber>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct AnswerRelationalSelection {
    deed: String,
    selected: RelationalThoughtCurrent,
    minimal_closed_witness_family: Option<LocalSet<String>>,
    alternatives: LocalSequence<RelationalThoughtCurrent>,
}

/// Exact observer receipt for native-rest equality. Its standing remains opaque: the public
/// language surface cannot use this receipt as a deed/fiber lookup atlas.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AgenticRelationalReturnRestReceipt {
    deeds: LocalRelations<String, DeedRelationalReturn>,
    answers: LocalRelations<String, AnswerRelationalSelection>,
}

/// One domain owner for research-deed fibers and the answer-relative selection they caused.
///
/// `LocalRelations` supplies the bounded, stable identity membrane. The owner retains every
/// current, but only exposes the exact current selected before the answer entered standing and
/// the remaining currents as typed alternatives.
#[derive(Debug, PartialEq, Eq)]
pub(super) struct AgenticRelationalReturnOwner {
    deeds: LocalRelations<String, DeedRelationalReturn>,
    answers: LocalRelations<String, AnswerRelationalSelection>,
}

impl AgenticRelationalReturnOwner {
    pub const fn new() -> Self {
        Self {
            deeds: LocalRelations::new(),
            answers: LocalRelations::new(),
        }
    }

    pub fn receive_deed(
        &mut self,
        deed: &str,
        fibers: &[RelationalThoughtFiber],
    ) -> Result<(), ()> {
        if deed.trim().is_empty() || fibers.is_empty() {
            return Err(());
        }
        let received = DeedRelationalReturn {
            fibers: LocalSequence::from_iter(fibers.iter().cloned()),
        };
        if let Some(existing) = self.deeds.get(&deed.to_owned()) {
            return (existing == &received).then_some(()).ok_or(());
        }
        self.deeds
            .try_insert(deed.to_owned(), received)
            .map_err(|_| ())?;
        Ok(())
    }

    pub fn bind_answer(
        &mut self,
        answer_episode: &str,
        deed: &str,
        selected: &RelationalThoughtCurrent,
    ) -> Result<(), ()> {
        if answer_episode.trim().is_empty() || deed.trim().is_empty() {
            return Err(());
        }
        let returned = self.deeds.get(&deed.to_owned()).ok_or(())?;
        if !returned
            .fibers
            .iter()
            .any(|fiber| fiber.currents.iter().any(|current| current == selected))
        {
            return Err(());
        }

        let minimal = minimal_closed_witness_families(&returned.fibers);
        let minimal_closed_witness_family = minimal
            .iter()
            .find(|family| {
                family.len() == selected.passage_witnesses.len()
                    && family
                        .iter()
                        .all(|witness| selected.passage_witnesses.contains(witness))
            })
            .cloned();
        let mut alternatives = LocalSequence::new();
        for current in returned
            .fibers
            .iter()
            .flat_map(|fiber| fiber.currents.iter())
        {
            if current != selected && !alternatives.contains(current) {
                alternatives.push(current.to_owned());
            }
        }
        let selection = AnswerRelationalSelection {
            deed: deed.to_owned(),
            selected: selected.to_owned(),
            minimal_closed_witness_family,
            alternatives,
        };
        if let Some(existing) = self.answers.get(&answer_episode.to_owned()) {
            return (existing == &selection).then_some(()).ok_or(());
        }
        self.answers
            .try_insert(answer_episode.to_owned(), selection)
            .map_err(|_| ())?;
        Ok(())
    }

    pub fn can_bind_answer(&self, deed: &str, selected: &RelationalThoughtCurrent) -> bool {
        self.deeds.get(&deed.to_owned()).is_some_and(|returned| {
            returned
                .fibers
                .iter()
                .any(|fiber| fiber.currents.iter().any(|current| current == selected))
        })
    }

    pub fn selected_for_answer(
        &self,
        answer_episode: &str,
    ) -> Option<AnswerSelectedRelationalCurrent> {
        let selection = self.answers.get(&answer_episode.to_owned())?;
        let minimal_closed_witness_family = selection.minimal_closed_witness_family.to_owned()?;
        selection
            .selected
            .is_closed()
            .then(|| AnswerSelectedRelationalCurrent {
                current: selection.selected.to_owned(),
                minimal_closed_witness_family,
                alternatives: selection.alternatives.to_owned(),
            })
    }

    pub fn rest_receipt(&self) -> AgenticRelationalReturnRestReceipt {
        AgenticRelationalReturnRestReceipt {
            deeds: self.deeds.to_owned(),
            answers: self.answers.to_owned(),
        }
    }
}

fn minimal_closed_witness_families(
    fibers: &[RelationalThoughtFiber],
) -> LocalSequence<LocalSet<String>> {
    let mut candidates = fibers
        .iter()
        .flat_map(RelationalThoughtFiber::closed)
        .map(|current| LocalSet::from_iter(current.passage_witnesses.iter().cloned()))
        .collect::<LocalSequence<_>>();
    candidates.sort_by(|left, right| left.len().cmp(&right.len()).then_with(|| left.cmp(right)));
    candidates.dedup();
    let mut minimal = LocalSequence::new();
    for candidate in candidates {
        if minimal.iter().any(|existing: &LocalSet<String>| {
            existing.iter().all(|member| candidate.contains(member))
        }) {
            continue;
        }
        minimal.push(candidate);
    }
    minimal
}
