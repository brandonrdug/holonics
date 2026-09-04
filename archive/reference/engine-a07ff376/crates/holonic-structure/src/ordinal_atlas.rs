use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt;

const PAGE_BITS: u32 = 6;
const PAGE_LEN: usize = 1usize << PAGE_BITS;
const PAGE_MASK: u64 = PAGE_LEN as u64 - 1;

/// Failure to grow or restore an exact ordinal population.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum OrdinalAtlasError {
    Extent,
    Occupied(u64),
    Reservation,
}

impl fmt::Display for OrdinalAtlasError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Extent => formatter.write_str("ordinal atlas extent is invalid"),
            Self::Occupied(ordinal) => {
                write!(
                    formatter,
                    "ordinal atlas position {ordinal} is already occupied"
                )
            }
            Self::Reservation => formatter.write_str("ordinal atlas could not reserve storage"),
        }
    }
}

impl core::error::Error for OrdinalAtlasError {}

#[derive(Clone, Debug, PartialEq, Eq)]
struct OrdinalPage<T> {
    number: u64,
    occupancy: u64,
    slots: Box<[Option<T>]>,
}

impl<T> OrdinalPage<T> {
    fn try_new(number: u64) -> Result<Self, OrdinalAtlasError> {
        let mut slots = Vec::new();
        slots
            .try_reserve_exact(PAGE_LEN)
            .map_err(|_| OrdinalAtlasError::Reservation)?;
        slots.resize_with(PAGE_LEN, || None);
        Ok(Self {
            number,
            occupancy: 0,
            slots: slots.into_boxed_slice(),
        })
    }

    fn get(&self, offset: usize) -> Option<&T> {
        self.slots.get(offset)?.as_ref()
    }

    fn get_mut(&mut self, offset: usize) -> Option<&mut T> {
        self.slots.get_mut(offset)?.as_mut()
    }

    fn insert(&mut self, offset: usize, value: T) -> Option<T> {
        let prior = self.slots[offset].replace(value);
        self.occupancy |= 1u64 << offset;
        prior
    }

    fn remove(&mut self, offset: usize) -> Option<T> {
        let prior = self.slots[offset].take();
        if prior.is_some() {
            self.occupancy &= !(1u64 << offset);
        }
        prior
    }
}

/// Sparse, canonically traversed population addressed by apparatus-local ordinals.
///
/// Equal ordinals have meaning only inside the owner which minted them. The atlas groups nearby
/// ordinals into fixed physical pages, retains tombstones after departure, never reuses an
/// ordinal, and exposes neither its directory nor a flattened slice. Sparse event identifiers and
/// monotone live-lineage identifiers therefore use the same owner without becoming the same
/// semantic identity.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseOrdinalAtlas<T> {
    pages: Vec<OrdinalPage<T>>,
    extent: u64,
    occupied: usize,
}

impl<T> Default for SparseOrdinalAtlas<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> SparseOrdinalAtlas<T> {
    pub const fn new() -> Self {
        Self {
            pages: Vec::new(),
            extent: 0,
            occupied: 0,
        }
    }

    pub const fn extent(&self) -> u64 {
        self.extent
    }

    pub const fn len(&self) -> usize {
        self.occupied
    }

    pub const fn is_empty(&self) -> bool {
        self.occupied == 0
    }

    pub fn contains(&self, ordinal: u64) -> bool {
        self.get(ordinal).is_some()
    }

    pub fn get(&self, ordinal: u64) -> Option<&T> {
        let (page, offset) = split_ordinal(ordinal);
        let at = self
            .pages
            .binary_search_by_key(&page, |present| present.number)
            .ok()?;
        self.pages[at].get(offset)
    }

    pub fn get_mut(&mut self, ordinal: u64) -> Option<&mut T> {
        let (page, offset) = split_ordinal(ordinal);
        let at = self
            .pages
            .binary_search_by_key(&page, |present| present.number)
            .ok()?;
        self.pages[at].get_mut(offset)
    }

    /// Mint the next never-before-used ordinal and found its body.
    pub fn try_push(&mut self, value: T) -> Result<u64, OrdinalAtlasError> {
        self.try_push_recover(value).map_err(|(error, _)| error)
    }

    /// Mint the next ordinal while returning ownership of a refused body to the caller.
    pub fn try_push_recover(&mut self, value: T) -> Result<u64, (OrdinalAtlasError, T)> {
        let ordinal = self.extent;
        self.try_found_recover(ordinal, value)?;
        Ok(ordinal)
    }

    /// Reserve every physical page needed by the next `additional` sequential foundings without
    /// advancing the logical extent. A later sequence of [`Self::try_push_recover`] calls within
    /// this horizon therefore cannot fail for page allocation.
    pub fn try_reserve_pushes(&mut self, additional: usize) -> Result<(), OrdinalAtlasError> {
        if additional == 0 {
            return Ok(());
        }
        let additional = u64::try_from(additional).map_err(|_| OrdinalAtlasError::Extent)?;
        let final_exclusive = self
            .extent
            .checked_add(additional)
            .ok_or(OrdinalAtlasError::Extent)?;
        let first_page = self.extent >> PAGE_BITS;
        let final_page = (final_exclusive - 1) >> PAGE_BITS;
        let missing = (first_page..=final_page)
            .filter(|page| {
                self.pages
                    .binary_search_by_key(page, |present| present.number)
                    .is_err()
            })
            .count();
        self.pages
            .try_reserve(missing)
            .map_err(|_| OrdinalAtlasError::Reservation)?;
        for page_number in first_page..=final_page {
            if let Err(at) = self
                .pages
                .binary_search_by_key(&page_number, |present| present.number)
            {
                let page = OrdinalPage::try_new(page_number)?;
                self.pages.insert(at, page);
            }
        }
        Ok(())
    }

    /// Found a supplied local ordinal, rejecting replacement.
    ///
    /// This is used for exact remount and for source-declared event identifiers. It may cross
    /// tombstones, but it cannot overwrite a presently occupied body.
    pub fn try_found(&mut self, ordinal: u64, value: T) -> Result<(), OrdinalAtlasError> {
        self.try_found_recover(ordinal, value)
            .map_err(|(error, _)| error)
    }

    /// Found a supplied ordinal while preserving a refused body's ownership.
    pub fn try_found_recover(
        &mut self,
        ordinal: u64,
        value: T,
    ) -> Result<(), (OrdinalAtlasError, T)> {
        if self.contains(ordinal) {
            return Err((OrdinalAtlasError::Occupied(ordinal), value));
        }
        let Some(next_extent) = ordinal.checked_add(1) else {
            return Err((OrdinalAtlasError::Extent, value));
        };
        let Some(next_occupied) = self.occupied.checked_add(1) else {
            return Err((OrdinalAtlasError::Extent, value));
        };
        let (page_number, offset) = split_ordinal(ordinal);
        match self
            .pages
            .binary_search_by_key(&page_number, |present| present.number)
        {
            Ok(at) => {
                let prior = self.pages[at].insert(offset, value);
                debug_assert!(prior.is_none());
            }
            Err(at) => {
                if self.pages.try_reserve(1).is_err() {
                    return Err((OrdinalAtlasError::Reservation, value));
                }
                let mut page = match OrdinalPage::try_new(page_number) {
                    Ok(page) => page,
                    Err(error) => return Err((error, value)),
                };
                let prior = page.insert(offset, value);
                debug_assert!(prior.is_none());
                self.pages.insert(at, page);
            }
        }
        self.extent = self.extent.max(next_extent);
        self.occupied = next_occupied;
        Ok(())
    }

    /// Preserve a larger minting horizon while remounting a population with departed ordinals.
    pub fn try_set_extent(&mut self, extent: u64) -> Result<(), OrdinalAtlasError> {
        let minimum = self
            .maximum_ordinal()
            .map(|ordinal| ordinal + 1)
            .unwrap_or(0);
        if extent < minimum {
            return Err(OrdinalAtlasError::Extent);
        }
        self.extent = extent;
        Ok(())
    }

    /// Depart a body without making its ordinal available for reuse.
    pub fn remove(&mut self, ordinal: u64) -> Option<T> {
        let (page_number, offset) = split_ordinal(ordinal);
        let at = self
            .pages
            .binary_search_by_key(&page_number, |present| present.number)
            .ok()?;
        let removed = self.pages[at].remove(offset)?;
        self.occupied -= 1;
        if self.pages[at].occupancy == 0 {
            self.pages.remove(at);
        }
        Some(removed)
    }

    pub fn iter(&self) -> OrdinalAtlasIter<'_, T> {
        OrdinalAtlasIter {
            pages: &self.pages,
            page: 0,
            offset: 0,
        }
    }

    pub fn values(&self) -> OrdinalAtlasValues<'_, T> {
        OrdinalAtlasValues { inner: self.iter() }
    }

    pub fn memory(&self) -> OrdinalAtlasMemory {
        OrdinalAtlasMemory {
            logical_extent: self.extent,
            occupied: self.occupied,
            resident_pages: self.pages.len(),
            resident_slots: self.pages.len().saturating_mul(PAGE_LEN),
        }
    }

    fn maximum_ordinal(&self) -> Option<u64> {
        let page = self.pages.iter().rev().find(|page| page.occupancy != 0)?;
        let offset = (u64::BITS - 1 - page.occupancy.leading_zeros()) as u64;
        Some(page.number * PAGE_LEN as u64 + offset)
    }
}

/// Substrate receipt only; none of these values enters causal identity or rest.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OrdinalAtlasMemory {
    pub logical_extent: u64,
    pub occupied: usize,
    pub resident_pages: usize,
    pub resident_slots: usize,
}

pub struct OrdinalAtlasIter<'a, T> {
    pages: &'a [OrdinalPage<T>],
    page: usize,
    offset: usize,
}

impl<'a, T> Iterator for OrdinalAtlasIter<'a, T> {
    type Item = (u64, &'a T);

    fn next(&mut self) -> Option<Self::Item> {
        while self.page < self.pages.len() {
            let page = &self.pages[self.page];
            while self.offset < PAGE_LEN {
                let offset = self.offset;
                self.offset += 1;
                if let Some(value) = page.get(offset) {
                    let ordinal = page.number * PAGE_LEN as u64 + offset as u64;
                    return Some((ordinal, value));
                }
            }
            self.page += 1;
            self.offset = 0;
        }
        None
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, None)
    }
}

pub struct OrdinalAtlasValues<'a, T> {
    inner: OrdinalAtlasIter<'a, T>,
}

impl<'a, T> Iterator for OrdinalAtlasValues<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, value)| value)
    }
}

const fn split_ordinal(ordinal: u64) -> (u64, usize) {
    (ordinal >> PAGE_BITS, (ordinal & PAGE_MASK) as usize)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeMap;

    #[test]
    fn sparse_population_matches_ordered_reference_without_reusing_departed_ordinals() {
        let mut atlas = SparseOrdinalAtlas::new();
        let mut reference = BTreeMap::new();
        for ordinal in [129, 2, 64, 65, 4097, 0, 130] {
            atlas.try_found(ordinal, ordinal * 3).unwrap();
            reference.insert(ordinal, ordinal * 3);
        }
        assert_eq!(
            atlas
                .iter()
                .map(|(key, value)| (key, *value))
                .collect::<Vec<_>>(),
            reference.into_iter().collect::<Vec<_>>()
        );
        assert_eq!(atlas.remove(65), Some(195));
        assert_eq!(atlas.remove(65), None);
        let extent = atlas.extent();
        let next = atlas.try_push(7).unwrap();
        assert_eq!(next, extent);
        assert!(next > 65);
    }

    #[test]
    fn remounted_horizon_may_retain_only_sparse_survivors() {
        let mut atlas = SparseOrdinalAtlas::new();
        atlas.try_found(3, "three").unwrap();
        atlas.try_set_extent(1000).unwrap();
        assert_eq!(atlas.try_push("next").unwrap(), 1000);
        assert_eq!(atlas.get(3), Some(&"three"));
        assert_eq!(atlas.get(1000), Some(&"next"));
    }
}
