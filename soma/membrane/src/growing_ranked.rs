//! Ceiling-free current-local OWN storage for the production membrane.
//!
//! The body owns the chart transition. This substrate retains exact rank-qualified addresses,
//! founding constructions, regional forms, and an arbitrary-width occupancy population. Every
//! fallible recast is built completely before installation, so a physical refusal poisons only
//! the disposable current and never leaves a partially transformed store.

use std::vec::Vec;

use body::manifold::{
    RankedFoundEdge, RankedOwnCellFace, RankedOwnError, RankedOwnStorage, SparseOwnCell,
};
use body::medium::RegionalForm;
use body::place::Place;

use crate::ChartAddress;

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ExactCount {
    /// Canonical little-endian limbs; zero has no limbs.
    words: Vec<u64>,
}

impl ExactCount {
    pub(crate) fn from_usize(value: usize) -> Self {
        if value == 0 {
            Self::default()
        } else {
            Self {
                words: vec![value as u64],
            }
        }
    }

    fn bit(&self, bit: u64) -> Result<bool, RankedOwnError> {
        let word = usize::try_from(bit / 64).map_err(|_| RankedOwnError::ResourceExtent)?;
        Ok(self
            .words
            .get(word)
            .is_some_and(|value| value & (1u64 << (bit & 63)) != 0))
    }

    pub(crate) fn incremented(&self) -> Result<Self, RankedOwnError> {
        let mut words = Vec::new();
        words
            .try_reserve_exact(self.words.len().saturating_add(1))
            .map_err(|_| RankedOwnError::ResourceReservation)?;
        words.extend_from_slice(&self.words);
        let mut at = 0usize;
        loop {
            if at == words.len() {
                words.push(1);
                break;
            }
            let (next, carry) = words[at].overflowing_add(1);
            words[at] = next;
            if !carry {
                break;
            }
            at = at.checked_add(1).ok_or(RankedOwnError::ResourceExtent)?;
        }
        Ok(Self { words })
    }

    pub(crate) fn entered_bit(&self, after: &Self, bit: u64) -> Result<bool, RankedOwnError> {
        Ok(!self.bit(bit)? && after.bit(bit)?)
    }

    fn decrement(&mut self) -> Result<(), RankedOwnError> {
        if self.words.is_empty() {
            return Err(RankedOwnError::Topology);
        }
        let mut at = 0usize;
        loop {
            let (next, borrow) = self.words[at].overflowing_sub(1);
            self.words[at] = next;
            if !borrow {
                break;
            }
            at += 1;
            if at == self.words.len() {
                return Err(RankedOwnError::Topology);
            }
        }
        while self.words.last() == Some(&0) {
            self.words.pop();
        }
        Ok(())
    }

    fn below_bit(&self, bit: u64) -> Result<bool, RankedOwnError> {
        let word = usize::try_from(bit / 64).map_err(|_| RankedOwnError::ResourceExtent)?;
        if self
            .words
            .iter()
            .skip(word.saturating_add(1))
            .any(|limb| *limb != 0)
        {
            return Ok(false);
        }
        let Some(&at) = self.words.get(word) else {
            return Ok(true);
        };
        let within = (bit & 63) as u32;
        if within == 0 {
            Ok(at == 0)
        } else {
            Ok(at & !((1u64 << within) - 1) == 0)
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RankedOwnCell {
    address: ChartAddress,
    founder: Place,
    form: RegionalForm,
}

impl RankedOwnCell {
    /// Lift one exact flat-device OWN cell into the live ranked address species. This is a
    /// representation change at the substrate return; founder and regional form remain whole.
    pub fn from_flat_at_rank(
        rank: u64,
        cell: SparseOwnCell,
    ) -> Result<Self, crate::ChartAddressError> {
        if rank > 16 {
            return Err(crate::ChartAddressError::FlatGripExtent);
        }
        let axis = 1u32 << rank;
        Ok(Self {
            address: ChartAddress::from_flat_grip(cell.grip(), axis)?,
            founder: cell.position(),
            form: cell.form(),
        })
    }

    pub fn address(&self) -> &ChartAddress {
        &self.address
    }

    pub fn founder(&self) -> Place {
        self.founder
    }

    pub fn form(&self) -> RegionalForm {
        self.form
    }
}

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GrowingRankedOwn {
    cells: Vec<RankedOwnCell>,
    occupancy: ExactCount,
}

impl GrowingRankedOwn {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn cells(&self) -> &[RankedOwnCell] {
        &self.cells
    }

    pub fn occupancy_words(&self) -> &[u64] {
        &self.occupancy.words
    }

    fn grounded(rank: u64, position: Place) -> Result<ChartAddress, RankedOwnError> {
        ChartAddress::ground(position, rank).map_err(|error| match error {
            crate::ChartAddressError::ResourceReservation => RankedOwnError::ResourceReservation,
            crate::ChartAddressError::ResourceExtent | crate::ChartAddressError::RankExtent => {
                RankedOwnError::ResourceExtent
            }
            _ => RankedOwnError::Geometry,
        })
    }

    fn find(&self, address: &ChartAddress) -> Result<usize, usize> {
        self.cells
            .binary_search_by(|cell| cell.address.cmp(address))
    }

    fn hand_bit(rank: u64) -> Result<u64, RankedOwnError> {
        if rank == 0 {
            Ok(0)
        } else {
            rank.checked_mul(2)
                .and_then(|value| value.checked_sub(1))
                .ok_or(RankedOwnError::ResourceExtent)
        }
    }

    fn transformed(
        &self,
        old_rank: u64,
        new_rank: u64,
        narrow: bool,
    ) -> Result<Vec<RankedOwnCell>, RankedOwnError> {
        let mut transformed = Vec::new();
        transformed
            .try_reserve_exact(self.cells.len())
            .map_err(|_| RankedOwnError::ResourceReservation)?;
        for cell in &self.cells {
            if cell.address.rank() != old_rank {
                return Err(RankedOwnError::Topology);
            }
            let address = if narrow {
                cell.address
                    .zero_section_source(new_rank)
                    .map_err(|_| RankedOwnError::Geometry)?
            } else {
                cell.address
                    .zero_extend(new_rank)
                    .map_err(|error| match error {
                        crate::ChartAddressError::ResourceReservation => {
                            RankedOwnError::ResourceReservation
                        }
                        crate::ChartAddressError::ResourceExtent
                        | crate::ChartAddressError::RankExtent => RankedOwnError::ResourceExtent,
                        _ => RankedOwnError::Geometry,
                    })?
            };
            transformed.push(RankedOwnCell {
                address,
                founder: cell.founder,
                form: cell.form,
            });
        }
        transformed.sort_unstable_by(|left, right| left.address.cmp(&right.address));
        if transformed
            .windows(2)
            .any(|pair| pair[0].address == pair[1].address)
        {
            return Err(RankedOwnError::Topology);
        }
        Ok(transformed)
    }
}

impl RankedOwnStorage for GrowingRankedOwn {
    fn reset(&mut self) -> Result<(), RankedOwnError> {
        self.cells.clear();
        self.occupancy.words.clear();
        Ok(())
    }

    fn form_at_position(&self, rank: u64, position: Place) -> Result<RegionalForm, RankedOwnError> {
        let address = Self::grounded(rank, position)?;
        Ok(self
            .find(&address)
            .ok()
            .map(|at| self.cells[at].form)
            .unwrap_or(RegionalForm::UNBORN))
    }

    fn try_found(
        &mut self,
        rank: u64,
        position: Place,
        form: RegionalForm,
    ) -> Result<RankedFoundEdge, RankedOwnError> {
        if !form.occupied() {
            return Err(RankedOwnError::Topology);
        }
        let address = Self::grounded(rank, position)?;
        let at = match self.find(&address) {
            Ok(_) => return Err(RankedOwnError::Topology),
            Err(at) => at,
        };
        let trial = self.occupancy.incremented()?;
        let hand = Self::hand_bit(rank)?;
        if self.occupancy.entered_bit(&trial, hand)? {
            return Ok(RankedFoundEdge::Carry);
        }
        self.cells
            .try_reserve(1)
            .map_err(|_| RankedOwnError::ResourceReservation)?;
        self.cells.insert(
            at,
            RankedOwnCell {
                address,
                founder: position,
                form,
            },
        );
        self.occupancy = trial;
        Ok(RankedFoundEdge::Inserted)
    }

    fn replace(
        &mut self,
        rank: u64,
        position: Place,
        expected: RegionalForm,
        replacement: RegionalForm,
    ) -> Result<(), RankedOwnError> {
        if !replacement.occupied() {
            return Err(RankedOwnError::Topology);
        }
        let address = Self::grounded(rank, position)?;
        let at = self.find(&address).map_err(|_| RankedOwnError::Topology)?;
        if self.cells[at].form != expected {
            return Err(RankedOwnError::Topology);
        }
        self.cells[at].form = replacement;
        Ok(())
    }

    fn release(
        &mut self,
        rank: u64,
        position: Place,
        expected: RegionalForm,
    ) -> Result<(), RankedOwnError> {
        let address = Self::grounded(rank, position)?;
        let at = self.find(&address).map_err(|_| RankedOwnError::Topology)?;
        if self.cells[at].form != expected {
            return Err(RankedOwnError::Topology);
        }
        self.occupancy.decrement()?;
        self.cells.remove(at);
        Ok(())
    }

    fn zero_extend(&mut self, old_rank: u64, new_rank: u64) -> Result<(), RankedOwnError> {
        if new_rank <= old_rank {
            return Err(RankedOwnError::Geometry);
        }
        let transformed = self.transformed(old_rank, new_rank, false)?;
        self.cells = transformed;
        Ok(())
    }

    fn occupancy_below_hand(&self, retiring_rank: u64) -> Result<bool, RankedOwnError> {
        self.occupancy.below_bit(Self::hand_bit(retiring_rank)?)
    }

    fn founders_in_zero_section(
        &self,
        old_rank: u64,
        new_rank: u64,
    ) -> Result<bool, RankedOwnError> {
        if old_rank
            != new_rank
                .checked_add(1)
                .ok_or(RankedOwnError::ResourceExtent)?
        {
            return Err(RankedOwnError::Geometry);
        }
        for cell in &self.cells {
            if cell.address.rank() != old_rank {
                return Err(RankedOwnError::Topology);
            }
            let Ok(source) = cell.address.zero_section_source(new_rank) else {
                return Ok(false);
            };
            if source != Self::grounded(new_rank, cell.founder)? {
                return Ok(false);
            }
        }
        Ok(true)
    }

    fn zero_section(&mut self, old_rank: u64, new_rank: u64) -> Result<(), RankedOwnError> {
        if old_rank
            != new_rank
                .checked_add(1)
                .ok_or(RankedOwnError::ResourceExtent)?
        {
            return Err(RankedOwnError::Geometry);
        }
        let transformed = self.transformed(old_rank, new_rank, true)?;
        self.cells = transformed;
        Ok(())
    }

    fn occupancy_words(&self) -> &[u64] {
        &self.occupancy.words
    }

    fn cell_count(&self) -> usize {
        self.cells.len()
    }

    fn cell_face(&self, at: usize) -> Option<RankedOwnCellFace> {
        self.cells.get(at).map(|cell| RankedOwnCellFace {
            founder: cell.founder,
            form: cell.form,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::channel::WindingQuantum;
    use body::medium::FeltTerm;
    use body::num::Cog;
    use body::soul::Chi;

    fn form(same: i64, other: i64) -> RegionalForm {
        RegionalForm::UNBORN.deposit(FeltTerm {
            chi: Chi {
                same: Cog::lit(same),
                other: Cog::lit(other),
            },
            winding: WindingQuantum::None,
        })
    }

    #[test]
    fn the_exact_population_crosses_hands_past_one_machine_word() {
        let cases = [
            (
                63,
                ExactCount {
                    words: vec![(1u64 << 63) - 1],
                },
            ),
            (
                64,
                ExactCount {
                    words: vec![u64::MAX],
                },
            ),
            (
                127,
                ExactCount {
                    words: vec![u64::MAX, (1u64 << 63) - 1],
                },
            ),
        ];
        for (bit, before) in cases {
            let after = before.incremented().unwrap();
            assert!(before.entered_bit(&after, bit).unwrap());
            assert!(!before.entered_bit(&after, bit + 1).unwrap());
        }
    }

    #[test]
    fn rank_eighty_and_rank_one_thirty_seven_retain_whole_addresses() {
        let founder = (Cog::lit(257).turn_up(3), Cog::lit(-65_537).turn_down(2));
        let mut storage = GrowingRankedOwn::new();
        storage.reset().unwrap();
        storage.zero_extend(0, 80).unwrap();
        assert_eq!(
            storage.try_found(80, founder, form(3, 5)).unwrap(),
            RankedFoundEdge::Inserted
        );
        assert_eq!(storage.cells.len(), 1);
        assert_eq!(storage.cells[0].address.rank(), 80);
        assert_eq!(storage.cells[0].address.try_flat_grip(), None);
        assert_eq!(storage.occupancy_words(), &[1]);

        let at_eighty = storage.cells[0].address.clone();
        storage.zero_extend(80, 137).unwrap();
        assert_eq!(storage.cells[0].address.rank(), 137);
        assert_eq!(storage.cells[0].address.try_flat_grip(), None);
        assert_eq!(
            storage.cells[0].address.zero_section_source(80).unwrap(),
            at_eighty
        );
        assert_eq!(storage.cells[0].founder, founder);
        assert_eq!(storage.cells[0].form, form(3, 5));
    }
}
