//! Growing keyed incidence over stable ordinal bodies.
//!
//! The tree is an apparatus-local routing membrane. Keys locate caused bodies; tree position,
//! rotation, height, and page residence never become causal identity. Unlike an application-owned
//! `BTreeMap`, the owner exposes only the operations used by continuing holonic machinery and is
//! deliberately not cloneable.

use core::{cmp::Ordering, fmt};

use crate::{OrdinalAtlasError, SparseOrdinalAtlas};

const MAXIMUM_AVL_DEPTH: usize = 128;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum KeyAtlasError {
    CarrierExtent,
    Storage(OrdinalAtlasError),
}

impl fmt::Display for KeyAtlasError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CarrierExtent => formatter.write_str("keyed atlas carrier extent is invalid"),
            Self::Storage(error) => write!(formatter, "keyed atlas storage refused: {error}"),
        }
    }
}

impl core::error::Error for KeyAtlasError {}

#[derive(Debug, PartialEq, Eq)]
struct KeyNode<K, V> {
    key: K,
    value: V,
    left: Option<u64>,
    right: Option<u64>,
    height: u16,
}

impl<K, V> KeyNode<K, V> {
    const fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            left: None,
            right: None,
            height: 1,
        }
    }
}

/// A dynamically growing exact key-to-body incidence atlas.
///
/// Nodes retain stable apparatus-local ordinals while AVL rotations alter only the routing
/// membrane. The complete atlas cannot be cloned. A caller which needs plurality must either
/// share immutable material above this owner or express a recoverable delta and commit it once.
#[derive(Debug)]
pub struct GrowingKeyAtlas<K, V> {
    nodes: SparseOrdinalAtlas<KeyNode<K, V>>,
    root: Option<u64>,
    len: usize,
}

// The AVL tree is a routing apparatus, not part of the caused keyed body. Two atlases with the
// same canonical key/value incidence are therefore the same standing even when their insertion
// chronologies produced different node ordinals, roots, or rotations.
impl<K: PartialEq, V: PartialEq> PartialEq for GrowingKeyAtlas<K, V> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        let mut left = self.iter();
        let mut right = other.iter();
        loop {
            match (left.next(), right.next()) {
                (Some((left_key, left_value)), Some((right_key, right_value)))
                    if left_key == right_key && left_value == right_value => {}
                (None, None) => return true,
                _ => return false,
            }
        }
    }
}

impl<K: Eq, V: Eq> Eq for GrowingKeyAtlas<K, V> {}

impl<K, V> Default for GrowingKeyAtlas<K, V> {
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> GrowingKeyAtlas<K, V> {
    pub const fn new() -> Self {
        Self {
            nodes: SparseOrdinalAtlas::new(),
            root: None,
            len: 0,
        }
    }

    pub const fn len(&self) -> usize {
        self.len
    }

    pub const fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn memory(&self) -> KeyAtlasMemory {
        let memory = self.nodes.memory();
        KeyAtlasMemory {
            bodies: self.len,
            ordinal_extent: memory.logical_extent,
            resident_pages: memory.resident_pages,
            resident_slots: memory.resident_slots,
        }
    }

    /// Preflight the physical pages for a bounded batch of new keys without changing standing.
    pub fn try_reserve_new_keys(&mut self, additional: usize) -> Result<(), KeyAtlasError> {
        self.len
            .checked_add(additional)
            .ok_or(KeyAtlasError::CarrierExtent)?;
        self.nodes
            .try_reserve_pushes(additional)
            .map_err(KeyAtlasError::Storage)
    }

    pub fn iter(&self) -> KeyAtlasIter<'_, K, V> {
        let mut iter = KeyAtlasIter {
            atlas: self,
            stack: [0; MAXIMUM_AVL_DEPTH],
            depth: 0,
            malformed: false,
        };
        iter.push_left(self.root);
        iter
    }

    pub fn keys(&self) -> KeyAtlasKeys<'_, K, V> {
        KeyAtlasKeys { inner: self.iter() }
    }

    pub fn values(&self) -> KeyAtlasValues<'_, K, V> {
        KeyAtlasValues { inner: self.iter() }
    }
}

impl<K: Ord, V> GrowingKeyAtlas<K, V> {
    pub fn contains(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    pub fn get(&self, key: &K) -> Option<&V> {
        let mut at = self.root;
        while let Some(ordinal) = at {
            let node = self.nodes.get(ordinal)?;
            match key.cmp(&node.key) {
                Ordering::Less => at = node.left,
                Ordering::Greater => at = node.right,
                Ordering::Equal => return Some(&node.value),
            }
        }
        None
    }

    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        let ordinal = self.find_ordinal(key)?;
        Some(&mut self.nodes.get_mut(ordinal)?.value)
    }

    /// Visit one inclusive receiver-local key interval without exposing the backing tree or
    /// materializing a detached population.
    pub fn range_inclusive<'a>(
        &'a self,
        lower: &'a K,
        upper: &'a K,
    ) -> KeyAtlasInclusiveRange<'a, K, V> {
        let mut range = KeyAtlasInclusiveRange {
            atlas: self,
            lower,
            upper,
            stack: [0; MAXIMUM_AVL_DEPTH],
            depth: 0,
            malformed: false,
            exhausted: lower > upper,
        };
        range.push_lower_bound(self.root);
        range
    }

    /// Insert one exact relation while returning both key and value if storage refuses it.
    ///
    /// Replacing an equal key returns the departed value. The already-standing key remains the
    /// canonical key body; the equal incoming key has no independent causal identity here.
    pub fn try_insert_recover(
        &mut self,
        key: K,
        value: V,
    ) -> Result<Option<V>, (KeyAtlasError, K, V)> {
        let mut path = [0u64; MAXIMUM_AVL_DEPTH];
        let mut directions = [false; MAXIMUM_AVL_DEPTH];
        let mut depth = 0usize;
        let mut at = self.root;
        while let Some(ordinal) = at {
            let Some(node) = self.nodes.get(ordinal) else {
                return Err((KeyAtlasError::CarrierExtent, key, value));
            };
            match key.cmp(&node.key) {
                Ordering::Equal => {
                    let node = self
                        .nodes
                        .get_mut(ordinal)
                        .expect("located key node remains standing");
                    return Ok(Some(core::mem::replace(&mut node.value, value)));
                }
                direction => {
                    if depth == MAXIMUM_AVL_DEPTH {
                        return Err((KeyAtlasError::CarrierExtent, key, value));
                    }
                    path[depth] = ordinal;
                    directions[depth] = direction == Ordering::Greater;
                    depth += 1;
                    at = if direction == Ordering::Less {
                        node.left
                    } else {
                        node.right
                    };
                }
            }
        }

        let next_len = match self.len.checked_add(1) {
            Some(next) => next,
            None => return Err((KeyAtlasError::CarrierExtent, key, value)),
        };
        let new_ordinal = match self.nodes.try_push_recover(KeyNode::new(key, value)) {
            Ok(ordinal) => ordinal,
            Err((error, node)) => {
                return Err((KeyAtlasError::Storage(error), node.key, node.value));
            }
        };

        let mut subtree = new_ordinal;
        for path_at in (0..depth).rev() {
            let parent = path[path_at];
            let Some(node) = self.nodes.get_mut(parent) else {
                return Err(self.rollback_unlinked_insert(new_ordinal));
            };
            if directions[path_at] {
                node.right = Some(subtree);
            } else {
                node.left = Some(subtree);
            }
            subtree = match self.rebalance(parent) {
                Some(root) => root,
                None => {
                    return Err(self.rollback_linked_insert(
                        new_ordinal,
                        &path,
                        &directions,
                        depth,
                    ));
                }
            };
        }
        self.root = Some(subtree);
        self.len = next_len;
        Ok(None)
    }

    pub fn try_insert(&mut self, key: K, value: V) -> Result<Option<V>, KeyAtlasError> {
        self.try_insert_recover(key, value)
            .map_err(|(error, _, _)| error)
    }

    fn find_ordinal(&self, key: &K) -> Option<u64> {
        let mut at = self.root;
        while let Some(ordinal) = at {
            let node = self.nodes.get(ordinal)?;
            match key.cmp(&node.key) {
                Ordering::Less => at = node.left,
                Ordering::Greater => at = node.right,
                Ordering::Equal => return Some(ordinal),
            }
        }
        None
    }

    fn node_height(&self, ordinal: Option<u64>) -> Option<u16> {
        match ordinal {
            Some(ordinal) => Some(self.nodes.get(ordinal)?.height),
            None => Some(0),
        }
    }

    fn balance(&self, ordinal: u64) -> Option<i32> {
        let node = self.nodes.get(ordinal)?;
        Some(i32::from(self.node_height(node.left)?) - i32::from(self.node_height(node.right)?))
    }

    fn refresh_height(&mut self, ordinal: u64) -> Option<()> {
        let (left, right) = {
            let node = self.nodes.get(ordinal)?;
            (node.left, node.right)
        };
        let height = self
            .node_height(left)?
            .max(self.node_height(right)?)
            .checked_add(1)?;
        self.nodes.get_mut(ordinal)?.height = height;
        Some(())
    }

    fn rebalance(&mut self, ordinal: u64) -> Option<u64> {
        self.refresh_height(ordinal)?;
        let balance = self.balance(ordinal)?;
        if balance > 1 {
            let left = self.nodes.get(ordinal)?.left?;
            if self.balance(left)? < 0 {
                let rotated = self.rotate_left(left)?;
                self.nodes.get_mut(ordinal)?.left = Some(rotated);
            }
            self.rotate_right(ordinal)
        } else if balance < -1 {
            let right = self.nodes.get(ordinal)?.right?;
            if self.balance(right)? > 0 {
                let rotated = self.rotate_right(right)?;
                self.nodes.get_mut(ordinal)?.right = Some(rotated);
            }
            self.rotate_left(ordinal)
        } else {
            Some(ordinal)
        }
    }

    fn rotate_left(&mut self, root: u64) -> Option<u64> {
        let pivot = self.nodes.get(root)?.right?;
        let middle = self.nodes.get(pivot)?.left;
        self.nodes.get_mut(root)?.right = middle;
        self.nodes.get_mut(pivot)?.left = Some(root);
        self.refresh_height(root)?;
        self.refresh_height(pivot)?;
        Some(pivot)
    }

    fn rotate_right(&mut self, root: u64) -> Option<u64> {
        let pivot = self.nodes.get(root)?.left?;
        let middle = self.nodes.get(pivot)?.right;
        self.nodes.get_mut(root)?.left = middle;
        self.nodes.get_mut(pivot)?.right = Some(root);
        self.refresh_height(root)?;
        self.refresh_height(pivot)?;
        Some(pivot)
    }

    fn rollback_unlinked_insert(&mut self, ordinal: u64) -> (KeyAtlasError, K, V) {
        let node = self
            .nodes
            .remove(ordinal)
            .expect("newly founded unlinked node remains recoverable");
        (KeyAtlasError::CarrierExtent, node.key, node.value)
    }

    fn rollback_linked_insert(
        &mut self,
        ordinal: u64,
        path: &[u64; MAXIMUM_AVL_DEPTH],
        directions: &[bool; MAXIMUM_AVL_DEPTH],
        depth: usize,
    ) -> (KeyAtlasError, K, V) {
        // Rebalancing can fail only if the pre-existing atlas was malformed. Remove the new leaf
        // and restore the direct parent link; no malformed standing is silently committed.
        if depth > 0 {
            if let Some(parent) = self.nodes.get_mut(path[depth - 1]) {
                if directions[depth - 1] {
                    if parent.right == Some(ordinal) {
                        parent.right = None;
                    }
                } else if parent.left == Some(ordinal) {
                    parent.left = None;
                }
            }
        }
        self.rollback_unlinked_insert(ordinal)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct KeyAtlasMemory {
    pub bodies: usize,
    pub ordinal_extent: u64,
    pub resident_pages: usize,
    pub resident_slots: usize,
}

pub struct KeyAtlasIter<'a, K, V> {
    atlas: &'a GrowingKeyAtlas<K, V>,
    stack: [u64; MAXIMUM_AVL_DEPTH],
    depth: usize,
    malformed: bool,
}

impl<'a, K, V> KeyAtlasIter<'a, K, V> {
    fn push_left(&mut self, mut at: Option<u64>) {
        while let Some(ordinal) = at {
            if self.depth == MAXIMUM_AVL_DEPTH {
                self.malformed = true;
                return;
            }
            self.stack[self.depth] = ordinal;
            self.depth += 1;
            at = self.atlas.nodes.get(ordinal).and_then(|node| node.left);
        }
    }
}

impl<'a, K, V> Iterator for KeyAtlasIter<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.malformed || self.depth == 0 {
            return None;
        }
        self.depth -= 1;
        let ordinal = self.stack[self.depth];
        let node = self.atlas.nodes.get(ordinal)?;
        self.push_left(node.right);
        Some((&node.key, &node.value))
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        (0, Some(self.atlas.len))
    }
}

impl<'a, K, V> IntoIterator for &'a GrowingKeyAtlas<K, V> {
    type Item = (&'a K, &'a V);
    type IntoIter = KeyAtlasIter<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

pub struct KeyAtlasKeys<'a, K, V> {
    inner: KeyAtlasIter<'a, K, V>,
}

impl<'a, K, V> Iterator for KeyAtlasKeys<'a, K, V> {
    type Item = &'a K;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(key, _)| key)
    }
}

pub struct KeyAtlasValues<'a, K, V> {
    inner: KeyAtlasIter<'a, K, V>,
}

pub struct KeyAtlasInclusiveRange<'a, K, V> {
    atlas: &'a GrowingKeyAtlas<K, V>,
    lower: &'a K,
    upper: &'a K,
    stack: [u64; MAXIMUM_AVL_DEPTH],
    depth: usize,
    malformed: bool,
    exhausted: bool,
}

impl<'a, K: Ord, V> KeyAtlasInclusiveRange<'a, K, V> {
    fn push_lower_bound(&mut self, mut at: Option<u64>) {
        while let Some(ordinal) = at {
            let Some(node) = self.atlas.nodes.get(ordinal) else {
                self.malformed = true;
                return;
            };
            if node.key < *self.lower {
                at = node.right;
                continue;
            }
            if self.depth == MAXIMUM_AVL_DEPTH {
                self.malformed = true;
                return;
            }
            self.stack[self.depth] = ordinal;
            self.depth += 1;
            at = node.left;
        }
    }

    fn push_left(&mut self, mut at: Option<u64>) {
        while let Some(ordinal) = at {
            if self.depth == MAXIMUM_AVL_DEPTH {
                self.malformed = true;
                return;
            }
            self.stack[self.depth] = ordinal;
            self.depth += 1;
            at = self.atlas.nodes.get(ordinal).and_then(|node| node.left);
        }
    }
}

impl<'a, K: Ord, V> Iterator for KeyAtlasInclusiveRange<'a, K, V> {
    type Item = (&'a K, &'a V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.malformed || self.exhausted || self.depth == 0 {
            return None;
        }
        self.depth -= 1;
        let ordinal = self.stack[self.depth];
        let node = self.atlas.nodes.get(ordinal)?;
        if node.key > *self.upper {
            self.exhausted = true;
            return None;
        }
        self.push_left(node.right);
        Some((&node.key, &node.value))
    }
}

impl<'a, K, V> Iterator for KeyAtlasValues<'a, K, V> {
    type Item = &'a V;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.next().map(|(_, value)| value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{collections::BTreeMap, vec::Vec};

    #[test]
    fn rotations_preserve_exact_keyed_incidence_and_stable_population() {
        let mut atlas = GrowingKeyAtlas::new();
        let mut reference = BTreeMap::new();
        for key in (0..4096u64).map(|at| (at * 7919) % 4096) {
            assert_eq!(
                atlas.try_insert(key, key * 3).unwrap(),
                reference.insert(key, key * 3)
            );
        }
        assert_eq!(atlas.len(), reference.len());
        assert_eq!(atlas.get(&2048), reference.get(&2048));
        assert_eq!(
            atlas.try_insert(2048, 7).unwrap(),
            reference.insert(2048, 7)
        );
        assert_eq!(
            atlas
                .iter()
                .map(|(key, value)| (*key, *value))
                .collect::<Vec<_>>(),
            reference.into_iter().collect::<Vec<_>>()
        );
        assert!(atlas.memory().resident_slots >= atlas.len());
    }

    #[test]
    fn apparatus_topology_is_not_keyed_standing_identity() {
        let mut ascending = GrowingKeyAtlas::new();
        let mut descending = GrowingKeyAtlas::new();
        for key in 0..127u64 {
            ascending.try_insert(key, key * 3).unwrap();
        }
        for key in (0..127u64).rev() {
            descending.try_insert(key, key * 3).unwrap();
        }
        assert_eq!(ascending, descending);
    }
}
