//! Receiver-local set and queue owners.
//!
//! These carriers deliberately expose the operation the causal law needs rather than the
//! substrate container which happens to realize it.  Their allocation, ordering, and growth are
//! apparatus details.  In particular, callers cannot acquire an entry API, hash policy, tree
//! node, or deque layout and accidentally promote that implementation into domain ontology.

use alloc::vec::Vec;
use core::{cmp::Ordering, fmt, iter::FromIterator};
use serde::{Deserialize, Serialize};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum LocalStructureError {
    Reservation,
    Extent,
}

impl fmt::Display for LocalStructureError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Reservation => formatter.write_str("local structure could not reserve storage"),
            Self::Extent => formatter.write_str("local structure extent is invalid"),
        }
    }
}

impl core::error::Error for LocalStructureError {}

/// A sorted receiver-local population with one occurrence of each exact member.
///
/// `LocalSet` is intentionally not a global registry.  It is appropriate for one aperture,
/// incidence row, antichain, or bounded return.  Stable identity remains owned by the enclosing
/// ecology.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(transparent)]
pub struct LocalSet<T> {
    members: Vec<T>,
}

impl<T> Default for LocalSet<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> LocalSet<T> {
    pub const fn new() -> Self {
        Self {
            members: Vec::new(),
        }
    }

    pub const fn len(&self) -> usize {
        self.members.len()
    }

    pub const fn is_empty(&self) -> bool {
        self.members.is_empty()
    }

    pub fn iter(&self) -> LocalSetIter<'_, T> {
        LocalSetIter {
            inner: self.members.iter(),
        }
    }

    pub fn first(&self) -> Option<&T> {
        self.members.first()
    }

    pub fn get(&self, at: usize) -> Option<&T> {
        self.members.get(at)
    }

    pub fn clear(&mut self) {
        self.members.clear();
    }
}

impl<T: Ord> LocalSet<T> {
    pub fn contains(&self, member: &T) -> bool {
        self.members.binary_search(member).is_ok()
    }

    pub fn try_insert(&mut self, member: T) -> Result<bool, LocalStructureError> {
        match self.members.binary_search(&member) {
            Ok(_) => Ok(false),
            Err(at) => {
                self.members
                    .try_reserve(1)
                    .map_err(|_| LocalStructureError::Reservation)?;
                self.members.insert(at, member);
                Ok(true)
            }
        }
    }

    /// Convenience for already-reserved or physically bounded local populations.
    ///
    /// Production laws which must report allocation refusal use [`Self::try_insert`].
    pub fn insert(&mut self, member: T) -> bool {
        match self.members.binary_search(&member) {
            Ok(_) => false,
            Err(at) => {
                self.members.insert(at, member);
                true
            }
        }
    }

    pub fn remove(&mut self, member: &T) -> bool {
        let Ok(at) = self.members.binary_search(member) else {
            return false;
        };
        self.members.remove(at);
        true
    }

    pub fn intersection<'a>(&'a self, other: &'a Self) -> LocalSetIntersection<'a, T> {
        LocalSetIntersection {
            left: &self.members,
            right: &other.members,
            left_at: 0,
            right_at: 0,
        }
    }

    pub fn union<'a>(&'a self, other: &'a Self) -> LocalSetUnion<'a, T> {
        LocalSetUnion {
            left: &self.members,
            right: &other.members,
            left_at: 0,
            right_at: 0,
        }
    }

    pub fn is_disjoint(&self, other: &Self) -> bool {
        self.intersection(other).next().is_none()
    }
}

impl<T: Ord> FromIterator<T> for LocalSet<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut set = Self::new();
        for member in iter {
            set.insert(member);
        }
        set
    }
}

impl<T: Ord> Extend<T> for LocalSet<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for member in iter {
            self.insert(member);
        }
    }
}

impl<T: Ord, const N: usize> From<[T; N]> for LocalSet<T> {
    fn from(members: [T; N]) -> Self {
        members.into_iter().collect()
    }
}

impl<'a, T> IntoIterator for &'a LocalSet<T> {
    type Item = &'a T;
    type IntoIter = LocalSetIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> IntoIterator for LocalSet<T> {
    type Item = T;
    type IntoIter = alloc::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.members.into_iter()
    }
}

pub struct LocalSetIter<'a, T> {
    inner: core::slice::Iter<'a, T>,
}

impl<'a, T> Iterator for LocalSetIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.inner.size_hint()
    }
}

impl<T> ExactSizeIterator for LocalSetIter<'_, T> {}

pub struct LocalSetIntersection<'a, T> {
    left: &'a [T],
    right: &'a [T],
    left_at: usize,
    right_at: usize,
}

pub struct LocalSetUnion<'a, T> {
    left: &'a [T],
    right: &'a [T],
    left_at: usize,
    right_at: usize,
}

impl<'a, T: Ord> Iterator for LocalSetUnion<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.left_at >= self.left.len() {
            let member = self.right.get(self.right_at)?;
            self.right_at += 1;
            return Some(member);
        }
        if self.right_at >= self.right.len() {
            let member = self.left.get(self.left_at)?;
            self.left_at += 1;
            return Some(member);
        }
        match self.left[self.left_at].cmp(&self.right[self.right_at]) {
            Ordering::Less => {
                let member = &self.left[self.left_at];
                self.left_at += 1;
                Some(member)
            }
            Ordering::Greater => {
                let member = &self.right[self.right_at];
                self.right_at += 1;
                Some(member)
            }
            Ordering::Equal => {
                let member = &self.left[self.left_at];
                self.left_at += 1;
                self.right_at += 1;
                Some(member)
            }
        }
    }
}

impl<'a, T: Ord> Iterator for LocalSetIntersection<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        while self.left_at < self.left.len() && self.right_at < self.right.len() {
            match self.left[self.left_at].cmp(&self.right[self.right_at]) {
                Ordering::Less => self.left_at += 1,
                Ordering::Greater => self.right_at += 1,
                Ordering::Equal => {
                    let member = &self.left[self.left_at];
                    self.left_at += 1;
                    self.right_at += 1;
                    return Some(member);
                }
            }
        }
        None
    }
}

/// A receiver-local FIFO whose head movement never shifts the remaining population.
///
/// Departed prefix storage is compacted only when the queue becomes empty.  This is sufficient
/// for bounded causal-front construction while keeping the queue's address policy private.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalQueue<T> {
    members: Vec<Option<T>>,
    head: usize,
}

impl<T> Default for LocalQueue<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> LocalQueue<T> {
    pub const fn new() -> Self {
        Self {
            members: Vec::new(),
            head: 0,
        }
    }

    pub fn try_push_back(&mut self, member: T) -> Result<(), LocalStructureError> {
        self.members
            .try_reserve(1)
            .map_err(|_| LocalStructureError::Reservation)?;
        self.members.push(Some(member));
        Ok(())
    }

    /// Reserve a complete caused suffix before any of its members enter the queue.
    pub fn try_reserve_additional(&mut self, additional: usize) -> Result<(), LocalStructureError> {
        self.members
            .try_reserve(additional)
            .map_err(|_| LocalStructureError::Reservation)
    }

    pub fn push_back(&mut self, member: T) {
        self.members.push(Some(member));
    }

    pub fn pop_front(&mut self) -> Option<T> {
        let member = self.members.get_mut(self.head)?.take()?;
        self.head += 1;
        if self.head == self.members.len() {
            self.members.clear();
            self.head = 0;
        }
        Some(member)
    }

    pub fn front(&self) -> Option<&T> {
        self.members.get(self.head)?.as_ref()
    }

    pub fn front_mut(&mut self) -> Option<&mut T> {
        self.members.get_mut(self.head)?.as_mut()
    }

    pub fn len(&self) -> usize {
        self.members.len().saturating_sub(self.head)
    }

    pub fn is_empty(&self) -> bool {
        self.head == self.members.len()
    }
}

impl<T> FromIterator<T> for LocalQueue<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            members: iter.into_iter().map(Some).collect(),
            head: 0,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::vec;

    #[test]
    fn local_set_is_canonical_and_intersects_without_materializing() {
        let left = LocalSet::from([7, 1, 3, 3]);
        let right = LocalSet::from([8, 3, 1]);
        assert_eq!(left.iter().copied().collect::<Vec<_>>(), vec![1, 3, 7]);
        assert_eq!(
            left.intersection(&right).copied().collect::<Vec<_>>(),
            vec![1, 3]
        );
    }

    #[test]
    fn local_queue_advances_without_shifting_the_live_suffix() {
        let mut queue = LocalQueue::from_iter([2, 4, 6]);
        assert_eq!(queue.pop_front(), Some(2));
        queue.push_back(8);
        assert_eq!(queue.pop_front(), Some(4));
        assert_eq!(queue.pop_front(), Some(6));
        assert_eq!(queue.pop_front(), Some(8));
        assert!(queue.is_empty());
    }
}
