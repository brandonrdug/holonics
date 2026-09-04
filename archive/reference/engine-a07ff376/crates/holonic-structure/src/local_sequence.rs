//! A receiver-local ordered population with an encapsulated contiguous substrate.
//!
//! Application code owns chronology and incidence, not allocator policy. `LocalSequence` keeps
//! the minimal ordered-body operations behind one laboratory-controlled boundary so a later page,
//! card, or segmented realization can replace the substrate without rewriting every ecology.

use alloc::{boxed::Box, vec::Vec};
use core::{
    iter::FromIterator,
    ops::{Deref, DerefMut},
};

use serde::{Deserialize, Serialize};

use crate::LocalStructureError;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(transparent)]
pub struct LocalSequence<T> {
    members: Vec<T>,
}

impl<T> Default for LocalSequence<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> LocalSequence<T> {
    pub const fn new() -> Self {
        Self {
            members: Vec::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            members: Vec::with_capacity(capacity),
        }
    }

    pub fn try_reserve(&mut self, additional: usize) -> Result<(), LocalStructureError> {
        self.members
            .try_reserve(additional)
            .map_err(|_| LocalStructureError::Reservation)
    }

    pub fn try_reserve_exact(&mut self, additional: usize) -> Result<(), LocalStructureError> {
        self.members
            .try_reserve_exact(additional)
            .map_err(|_| LocalStructureError::Reservation)
    }

    pub fn reserve(&mut self, additional: usize) {
        self.members.reserve(additional);
    }

    pub fn push(&mut self, member: T) {
        self.members.push(member);
    }

    pub fn pop(&mut self) -> Option<T> {
        self.members.pop()
    }

    pub fn clear(&mut self) {
        self.members.clear();
    }

    pub fn remove(&mut self, at: usize) -> T {
        self.members.remove(at)
    }

    pub fn insert(&mut self, at: usize, member: T) {
        self.members.insert(at, member);
    }

    pub fn retain(&mut self, keep: impl FnMut(&T) -> bool) {
        self.members.retain(keep);
    }

    pub fn truncate(&mut self, len: usize) {
        self.members.truncate(len);
    }

    pub fn extend_from_slice(&mut self, members: &[T])
    where
        T: Clone,
    {
        self.members.extend_from_slice(members);
    }

    pub fn dedup(&mut self)
    where
        T: PartialEq,
    {
        self.members.dedup();
    }

    pub fn resize_with(&mut self, new_len: usize, body: impl FnMut() -> T) {
        self.members.resize_with(new_len, body);
    }

    pub fn into_boxed_slice(self) -> Box<[T]> {
        self.members.into_boxed_slice()
    }

    pub fn into_inner(self) -> Vec<T> {
        self.members
    }

    pub fn from_slice(members: &[T]) -> Self
    where
        T: Clone,
    {
        Self {
            members: members.to_vec(),
        }
    }
}

impl<T> AsRef<[T]> for LocalSequence<T> {
    fn as_ref(&self) -> &[T] {
        &self.members
    }
}

impl<T> Deref for LocalSequence<T> {
    type Target = [T];

    fn deref(&self) -> &Self::Target {
        &self.members
    }
}

impl<T> DerefMut for LocalSequence<T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.members
    }
}

impl<T> FromIterator<T> for LocalSequence<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            members: Vec::from_iter(iter),
        }
    }
}

impl<T> Extend<T> for LocalSequence<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.members.extend(iter);
    }
}

impl<T> IntoIterator for LocalSequence<T> {
    type Item = T;
    type IntoIter = alloc::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        self.members.into_iter()
    }
}

impl<'a, T> IntoIterator for &'a LocalSequence<T> {
    type Item = &'a T;
    type IntoIter = core::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.members.iter()
    }
}

impl<'a, T> IntoIterator for &'a mut LocalSequence<T> {
    type Item = &'a mut T;
    type IntoIter = core::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.members.iter_mut()
    }
}

impl<T, const N: usize> From<[T; N]> for LocalSequence<T> {
    fn from(members: [T; N]) -> Self {
        Self {
            members: Vec::from(members),
        }
    }
}
