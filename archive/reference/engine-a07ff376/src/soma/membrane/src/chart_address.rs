//! Rank-qualified sparse chart addresses.
//!
//! The historical [`body::place::Grip`] is a flat `u32` quotient.  It is an exact compatibility
//! face only while both dyadic coordinates fit that word.  A live sparse ecology instead keeps
//! the chart rank and the two coordinate bit paths independently.  Widening appends the actually
//! enacted zero section; it never re-grounds an old founder or allocates an `axis²` plane.

use core::cmp::Ordering;

use body::num::Cog;
use body::place::{self, Place};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ChartAddressError {
    RankExtent,
    FlatGripExtent,
    ResourceExtent,
    ResourceReservation,
    MalformedRank,
    NarrowSectionAbsent,
}

/// One coordinate in a dyadic chart, least-significant word first.  Only the words required by
/// `rank` exist.  The physical word partition is storage gauge; equality is the represented bit
/// path, not a page identity.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct DyadicCoordinate {
    words: Vec<u64>,
}

fn coordinate_word_extent(rank: u64) -> Result<usize, ChartAddressError> {
    let words = rank
        .checked_add(63)
        .ok_or(ChartAddressError::ResourceExtent)?
        / 64;
    usize::try_from(words).map_err(|_| ChartAddressError::RankExtent)
}

impl DyadicCoordinate {
    fn zeroed(rank: u64) -> Result<Self, ChartAddressError> {
        let words = coordinate_word_extent(rank)?;
        let mut out = Vec::new();
        out.try_reserve_exact(words)
            .map_err(|_| ChartAddressError::ResourceReservation)?;
        out.resize(words, 0);
        Ok(Self { words: out })
    }

    fn mask_to_rank(&mut self, rank: u64) {
        let tail = (rank & 63) as u32;
        if tail != 0 {
            if let Some(last) = self.words.last_mut() {
                *last &= (1u64 << tail) - 1;
            }
        }
    }

    fn grounded(cog: Cog, rank: u64) -> Result<Self, ChartAddressError> {
        let source =
            place::ground_coordinate_words(cog, rank).ok_or(ChartAddressError::MalformedRank)?;
        let words = usize::try_from(source.words()).map_err(|_| ChartAddressError::RankExtent)?;
        let mut out = Vec::new();
        out.try_reserve_exact(words)
            .map_err(|_| ChartAddressError::ResourceReservation)?;
        out.extend(source);
        Ok(Self { words: out })
    }

    fn cmp_grounded(&self, cog: Cog, rank: u64) -> Result<Ordering, ChartAddressError> {
        let source =
            place::ground_coordinate_words(cog, rank).ok_or(ChartAddressError::MalformedRank)?;
        let words = usize::try_from(source.words()).map_err(|_| ChartAddressError::RankExtent)?;
        match self.words.len().cmp(&words) {
            Ordering::Equal => {}
            ordering => return Ok(ordering),
        }
        for (stored, grounded) in self.words.iter().copied().zip(source) {
            match stored.cmp(&grounded) {
                Ordering::Equal => {}
                ordering => return Ok(ordering),
            }
        }
        Ok(Ordering::Equal)
    }

    fn shifted_left(&self, by: u64, rank: u64) -> Result<Self, ChartAddressError> {
        let mut out = Self::zeroed(rank)?;
        let word_shift = usize::try_from(by / 64).map_err(|_| ChartAddressError::RankExtent)?;
        let bit_shift = (by & 63) as u32;
        for (source, &value) in self.words.iter().enumerate() {
            let target = source
                .checked_add(word_shift)
                .ok_or(ChartAddressError::ResourceExtent)?;
            if target >= out.words.len() {
                break;
            }
            out.words[target] |= value << bit_shift;
            if bit_shift != 0 && target + 1 < out.words.len() {
                out.words[target + 1] |= value >> (64 - bit_shift);
            }
        }
        out.mask_to_rank(rank);
        Ok(out)
    }

    fn low_bits_are_zero(&self, bits: u64) -> Result<bool, ChartAddressError> {
        let whole = usize::try_from(bits / 64).map_err(|_| ChartAddressError::RankExtent)?;
        if self.words.iter().take(whole).any(|word| *word != 0) {
            return Ok(false);
        }
        let tail = (bits & 63) as u32;
        if tail == 0 {
            return Ok(true);
        }
        Ok(self
            .words
            .get(whole)
            .is_none_or(|word| word & ((1u64 << tail) - 1) == 0))
    }

    fn shifted_right(&self, by: u64, rank: u64) -> Result<Self, ChartAddressError> {
        let mut out = Self::zeroed(rank)?;
        let word_shift = usize::try_from(by / 64).map_err(|_| ChartAddressError::RankExtent)?;
        let bit_shift = (by & 63) as u32;
        for target in 0..out.words.len() {
            let source = target
                .checked_add(word_shift)
                .ok_or(ChartAddressError::ResourceExtent)?;
            let Some(&lo) = self.words.get(source) else {
                break;
            };
            out.words[target] = lo >> bit_shift;
            if bit_shift != 0 {
                if let Some(&hi) = self.words.get(source + 1) {
                    out.words[target] |= hi << (64 - bit_shift);
                }
            }
        }
        out.mask_to_rank(rank);
        Ok(out)
    }

    fn low_u64(&self) -> u64 {
        self.words.first().copied().unwrap_or(0)
    }
}

/// A chart position is the pair of dyadic coordinate paths at one explicit rank.  `rank = r`
/// means side axis `2^r`; the axis itself is never materialized.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ChartAddress {
    rank: u64,
    x: DyadicCoordinate,
    y: DyadicCoordinate,
}

impl ChartAddress {
    /// Lift one exact historical flat grip into the rank-qualified address.  This is a storage
    /// conversion only; it does not claim the grip was the founder's absolute identity.
    pub fn from_flat_grip(grip: u32, axis: u32) -> Result<Self, ChartAddressError> {
        if axis == 0 || !axis.is_power_of_two() {
            return Err(ChartAddressError::MalformedRank);
        }
        if axis > 1 << 16 {
            return Err(ChartAddressError::FlatGripExtent);
        }
        let rank = axis.trailing_zeros() as u64;
        let x = (grip / axis) as u64;
        let y = (grip - (grip / axis) * axis) as u64;
        if x >= axis as u64 || y >= axis as u64 {
            return Err(ChartAddressError::MalformedRank);
        }
        let mut x_words = DyadicCoordinate::zeroed(rank)?;
        let mut y_words = DyadicCoordinate::zeroed(rank)?;
        if let Some(word) = x_words.words.first_mut() {
            *word = x;
        }
        if let Some(word) = y_words.words.first_mut() {
            *word = y;
        }
        Ok(Self {
            rank,
            x: x_words,
            y: y_words,
        })
    }

    /// Ground a new founder at the receiving rank.  This is the arbitrary-rank lift of
    /// `body::place::ground`: mantissa, turn, rank, and the centered chart hand all remain in the
    /// same sum, but the result is retained as two bit paths instead of flattened into `u32`.
    pub fn ground(place: Place, rank: u64) -> Result<Self, ChartAddressError> {
        Ok(Self {
            rank,
            x: DyadicCoordinate::grounded(place.0, rank)?,
            y: DyadicCoordinate::grounded(place.1, rank)?,
        })
    }

    /// Compare this retained address with the body-owned grounding of one construction without
    /// allocating a temporary address.  Storage ordering remains the receiver's gauge; the
    /// coordinate limbs themselves come only from `body::place`.
    pub(crate) fn cmp_grounded(&self, place: Place) -> Result<Ordering, ChartAddressError> {
        match self.x.cmp_grounded(place.0, self.rank)? {
            Ordering::Equal => self.y.cmp_grounded(place.1, self.rank),
            ordering => Ok(ordering),
        }
    }

    pub fn rank(&self) -> u64 {
        self.rank
    }

    /// Apply an enacted dyadic chart digit.  Existing construction occupies the zero section of
    /// the wider chart, exactly `(x,y) -> (2^d x, 2^d y)`.
    pub fn zero_extend(&self, new_rank: u64) -> Result<Self, ChartAddressError> {
        let by = new_rank
            .checked_sub(self.rank)
            .ok_or(ChartAddressError::NarrowSectionAbsent)?;
        Ok(Self {
            rank: new_rank,
            x: self.x.shifted_left(by, new_rank)?,
            y: self.y.shifted_left(by, new_rank)?,
        })
    }

    /// Exact inverse section of [`Self::zero_extend`].  An address with live low digits has no
    /// source in the narrower chart and refuses rather than rounding.
    pub fn zero_section_source(&self, old_rank: u64) -> Result<Self, ChartAddressError> {
        let by = self
            .rank
            .checked_sub(old_rank)
            .ok_or(ChartAddressError::NarrowSectionAbsent)?;
        if !self.x.low_bits_are_zero(by)? || !self.y.low_bits_are_zero(by)? {
            return Err(ChartAddressError::NarrowSectionAbsent);
        }
        Ok(Self {
            rank: old_rank,
            x: self.x.shifted_right(by, old_rank)?,
            y: self.y.shifted_right(by, old_rank)?,
        })
    }

    /// Exact native persistence extent for one address at `rank`. Each coordinate limb is a
    /// least-significant-word-first `u64` path, split into little-endian `u32` words. The rank is
    /// carried once by the owning standing surface rather than repeated in every cell.
    pub(crate) fn native_word_extent(rank: u64) -> Result<usize, ChartAddressError> {
        coordinate_word_extent(rank)?
            .checked_mul(4)
            .ok_or(ChartAddressError::ResourceExtent)
    }

    /// Write one exact address into an already-bounded native row. Storage-word partition is a
    /// gauge only; no flat grip or founder coordinate is reconstructed.
    pub(crate) fn write_native_words(&self, words: &mut [u32]) -> Result<(), ChartAddressError> {
        if words.len() != Self::native_word_extent(self.rank)? {
            return Err(ChartAddressError::MalformedRank);
        }
        let mut at = 0usize;
        for coordinate in [&self.x, &self.y] {
            for value in coordinate.words.iter().copied() {
                words[at] = value as u32;
                words[at + 1] = (value >> 32) as u32;
                at += 2;
            }
        }
        debug_assert_eq!(at, words.len());
        Ok(())
    }

    /// Reopen one exact rank-qualified address. Nonzero bits above the declared rank refuse;
    /// truncation and trailing words refuse as a whole before an address exists.
    pub(crate) fn from_native_words(rank: u64, words: &[u32]) -> Result<Self, ChartAddressError> {
        let coordinate_words = coordinate_word_extent(rank)?;
        if words.len() != Self::native_word_extent(rank)? {
            return Err(ChartAddressError::MalformedRank);
        }
        let read_coordinate = |start: usize| -> Result<DyadicCoordinate, ChartAddressError> {
            let mut decoded = Vec::new();
            decoded
                .try_reserve_exact(coordinate_words)
                .map_err(|_| ChartAddressError::ResourceReservation)?;
            for word in 0..coordinate_words {
                let at = start
                    .checked_add(
                        word.checked_mul(2)
                            .ok_or(ChartAddressError::ResourceExtent)?,
                    )
                    .ok_or(ChartAddressError::ResourceExtent)?;
                decoded.push(words[at] as u64 | ((words[at + 1] as u64) << 32));
            }
            let tail = (rank & 63) as u32;
            if tail != 0
                && decoded
                    .last()
                    .is_some_and(|value| value & !((1u64 << tail) - 1) != 0)
            {
                return Err(ChartAddressError::MalformedRank);
            }
            Ok(DyadicCoordinate { words: decoded })
        };
        let y_at = coordinate_words
            .checked_mul(2)
            .ok_or(ChartAddressError::ResourceExtent)?;
        Ok(Self {
            rank,
            x: read_coordinate(0)?,
            y: read_coordinate(y_at)?,
        })
    }

    /// Compatibility quotient for the historical flat `Grip`.  The pair fits exactly only while
    /// two coordinate ranks fit 32 bits; no truncating cast is offered beyond that boundary.
    pub fn try_flat_grip(&self) -> Option<u32> {
        if self.rank > 16 {
            return None;
        }
        let axis = 1u64 << self.rank;
        let grip = self.x.low_u64().checked_mul(axis)? + self.y.low_u64();
        u32::try_from(grip).ok()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use body::chart;

    fn fixtures() -> [Place; 6] {
        [
            (Cog::ZERO, Cog::ZERO),
            (Cog::lit(1), Cog::lit(-1)),
            (Cog::lit(257).turn_up(3), Cog::lit(-65_537).turn_down(1)),
            (Cog::lit(13).turned(1), Cog::lit(17).turned(3)),
            (Cog::lit(i64::MAX), Cog::lit(i64::MIN + 1)),
            (Cog::lit(144).turn_down(5), Cog::lit(233).turn_up(9)),
        ]
    }

    #[test]
    fn every_flat_fit_address_is_the_historical_grip_exactly() {
        for rank in 0..=16u64 {
            let axis = 1i64 << rank;
            for place in fixtures() {
                let address = ChartAddress::ground(place, rank).unwrap();
                assert_eq!(
                    address.try_flat_grip(),
                    Some(body::place::ground(place, axis))
                );
            }
        }
    }

    #[test]
    fn zero_extension_is_the_existing_composing_section_without_a_flat_ceiling() {
        for rank in 0..=15u64 {
            for place in fixtures() {
                let source = ChartAddress::ground(place, rank).unwrap();
                let extended = source.zero_extend(rank + 1).unwrap();
                assert_eq!(
                    extended.try_flat_grip(),
                    Some(chart::zero_extend_grip(
                        source.try_flat_grip().unwrap(),
                        1u32 << rank,
                        1u32 << (rank + 1),
                    ))
                );
                assert_eq!(extended.zero_section_source(rank).unwrap(), source);
            }
        }

        let deep = ChartAddress::ground(fixtures()[2], 80).unwrap();
        assert_eq!(deep.try_flat_grip(), None);
        let wider = deep.zero_extend(137).unwrap();
        assert_eq!(wider.zero_section_source(80).unwrap(), deep);
    }

    #[test]
    fn a_new_founder_off_the_zero_section_cannot_be_rounded_back() {
        let mut witness = None;
        for value in 1..4096i64 {
            let candidate =
                ChartAddress::ground((Cog::lit(value), Cog::lit(value + 1)), 18).unwrap();
            if candidate.zero_section_source(17).is_err() {
                witness = Some(candidate);
                break;
            }
        }
        assert!(witness.is_some());
    }

    #[test]
    fn the_historical_flat_constructor_stops_before_axis_squared_aliases_u32() {
        assert!(ChartAddress::from_flat_grip(u32::MAX, 1 << 16).is_ok());
        assert_eq!(
            ChartAddress::from_flat_grip(0, 1 << 17),
            Err(ChartAddressError::FlatGripExtent)
        );
        assert!(ChartAddress::ground(fixtures()[0], 17).is_ok());
    }

    #[test]
    fn the_native_address_wire_preserves_deep_coordinate_paths_without_a_flat_grip() {
        for rank in [0, 1, 16, 17, 80, 137] {
            let address = ChartAddress::ground(fixtures()[2], rank).unwrap();
            let mut words = vec![0u32; ChartAddress::native_word_extent(rank).unwrap()];
            address.write_native_words(&mut words).unwrap();
            assert_eq!(
                ChartAddress::from_native_words(rank, &words).unwrap(),
                address
            );
        }

        let rank = 65;
        let mut words = vec![0u32; ChartAddress::native_word_extent(rank).unwrap()];
        // The second u64 limb word has only one live bit at rank 65.
        words[3] = 2;
        assert_eq!(
            ChartAddress::from_native_words(rank, &words),
            Err(ChartAddressError::MalformedRank)
        );
    }
}
