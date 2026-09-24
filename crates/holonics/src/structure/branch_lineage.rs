//! Explicit immutable ancestry for plural causal continuations.

use alloc::sync::Arc;

/// Receipt proving that a new handle shares an already-caused prefix rather than copying it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct BranchForkReceipt {
    pub shared_events: usize,
}

#[derive(Debug, PartialEq, Eq)]
struct BranchNode<T> {
    prior: Option<Arc<BranchNode<T>>>,
    event: T,
    extent: usize,
}

/// One immutable causal lineage handle.
///
/// The handle is intentionally not `Clone`. [`Self::fork`] is the only way to form plurality, so
/// code review and resource receipts can distinguish a causal branch from an accidental body
/// copy. Carrying an event consumes the handle and transfers its prior tip without duplication.
#[derive(Debug, PartialEq, Eq)]
pub struct BranchLineage<T> {
    tip: Option<Arc<BranchNode<T>>>,
}

impl<T> Default for BranchLineage<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> BranchLineage<T> {
    pub const fn new() -> Self {
        Self { tip: None }
    }

    pub fn len(&self) -> usize {
        self.tip.as_ref().map_or(0, |tip| tip.extent)
    }

    pub fn is_empty(&self) -> bool {
        self.tip.is_none()
    }

    pub fn fork(&self) -> (Self, BranchForkReceipt) {
        let shared_events = self.len();
        (
            Self {
                tip: self.tip.as_ref().map(Arc::clone),
            },
            BranchForkReceipt { shared_events },
        )
    }

    pub fn carry(mut self, event: T) -> Option<Self> {
        let extent = self.len().checked_add(1)?;
        self.tip = Some(Arc::new(BranchNode {
            prior: self.tip.take(),
            event,
            extent,
        }));
        Some(self)
    }

    pub fn newest_first(&self) -> BranchLineageIter<'_, T> {
        BranchLineageIter {
            next: self.tip.as_deref(),
        }
    }
}

pub struct BranchLineageIter<'a, T> {
    next: Option<&'a BranchNode<T>>,
}

impl<'a, T> Iterator for BranchLineageIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        let node = self.next?;
        self.next = node.prior.as_deref();
        Some(&node.event)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.next.map_or(0, |node| node.extent);
        (remaining, Some(remaining))
    }
}

impl<T> ExactSizeIterator for BranchLineageIter<'_, T> {}

#[cfg(test)]
mod tests {
    use super::*;
    use std::{vec, vec::Vec};

    #[test]
    fn explicit_fork_shares_history_and_diverges_only_at_the_new_event() {
        let root = BranchLineage::new().carry(2).unwrap().carry(3).unwrap();
        let (left, receipt) = root.fork();
        let right = root.carry(7).unwrap();
        let left = left.carry(5).unwrap();
        assert_eq!(receipt.shared_events, 2);
        assert_eq!(
            left.newest_first().copied().collect::<Vec<_>>(),
            vec![5, 3, 2]
        );
        assert_eq!(
            right.newest_first().copied().collect::<Vec<_>>(),
            vec![7, 3, 2]
        );
    }
}
