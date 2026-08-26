use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId,
};

use super::types::LongHorizonBoundaryError;

/// The finite source cover of addressed historical interiors by continuing boundary states.
///
/// Every interior owns one realization at every continuing state.  Generators move the state and
/// retain the interior lineage.  Thus histories may compactify across interiors only when every
/// receiver and successor word agrees; the complete historical distinction remains recoverable.
#[derive(Debug)]
pub struct AddressedHistorySystem {
    interiors: usize,
    states: usize,
    generators: usize,
    generator_table: Vec<u32>,
    observations: Vec<Vec<Observation>>,
}

impl AddressedHistorySystem {
    pub fn found(
        interiors: usize,
        states: usize,
        generator_table: Vec<u32>,
        observations: Vec<Vec<Observation>>,
    ) -> Result<Self, LongHorizonBoundaryError> {
        if interiors < 2
            || states < 2
            || generator_table.is_empty()
            || generator_table.len() % states != 0
            || observations.is_empty()
            || observations.iter().any(|row| row.len() != states)
            || generator_table
                .iter()
                .any(|state| *state as usize >= states)
        {
            return Err(LongHorizonBoundaryError::System);
        }
        let generators = generator_table.len() / states;
        let source_population = interiors
            .checked_mul(states)
            .ok_or(LongHorizonBoundaryError::System)?;
        if source_population > u32::MAX as usize
            || generators > u32::MAX as usize
            || observations.len() > u32::MAX as usize
        {
            return Err(LongHorizonBoundaryError::System);
        }
        Ok(Self {
            interiors,
            states,
            generators,
            generator_table,
            observations,
        })
    }

    pub fn interiors(&self) -> usize {
        self.interiors
    }

    pub fn states(&self) -> usize {
        self.states
    }

    pub fn generators(&self) -> usize {
        self.generators
    }

    pub fn generator_table(&self) -> &[u32] {
        &self.generator_table
    }

    pub fn source_item(&self, interior: usize, state: u32) -> Option<ItemId> {
        (interior < self.interiors && (state as usize) < self.states).then(|| {
            ItemId(
                u64::try_from(interior * self.states + state as usize)
                    .expect("the admitted source population crosses u32"),
            )
        })
    }

    pub fn coordinates(&self, item: ItemId) -> Option<(usize, u32)> {
        let at = usize::try_from(item.0).ok()?;
        (at < self.interiors * self.states).then_some((at / self.states, (at % self.states) as u32))
    }

    pub fn base_observations(&self, state: u32) -> Option<Vec<Observation>> {
        ((state as usize) < self.states).then(|| {
            self.observations
                .iter()
                .map(|row| row[state as usize])
                .collect()
        })
    }

    /// The uncondensed source action, row-major `[generator][source item]`.
    pub fn source_generator_table(&self) -> Vec<u32> {
        let source_states = self.interiors * self.states;
        let mut table = Vec::with_capacity(self.generators * source_states);
        for generator in 0..self.generators {
            for interior in 0..self.interiors {
                for state in 0..self.states {
                    let target = self.generator_table[generator * self.states + state] as usize;
                    table.push((interior * self.states + target) as u32);
                }
            }
        }
        table
    }
}

impl ObservedSystem for AddressedHistorySystem {
    fn items(&self) -> Vec<ItemId> {
        (0..self.interiors * self.states)
            .map(|item| ItemId(item as u64))
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        (0..self.observations.len())
            .map(|receiver| ReceiverId(receiver as u64))
            .collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        (0..self.generators)
            .map(|input| InputId(input as u64))
            .collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let (_, state) = self
            .coordinates(item)
            .expect("receiver_exact_compression asks only admitted items");
        self.observations[receiver.0 as usize][state as usize]
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let (interior, state) = self.coordinates(item)?;
        let target = *self
            .generator_table
            .get(input.0 as usize * self.states + state as usize)?;
        self.source_item(interior, target)
    }

    fn admitted(&self, input: InputId) -> Option<Vec<(ItemId, ItemId)>> {
        Some(
            self.items()
                .into_iter()
                .map(|item| {
                    let next = self
                        .successor(item, input)
                        .expect("the addressed history action is total");
                    (item, next)
                })
                .collect(),
        )
    }
}
