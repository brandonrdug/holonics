//! Fallible growable host storage for one disposable current-local sparse body.
//!
//! Growth follows actual accepted topology rather than an exponential worst-case reservation.  A
//! failed host allocation returns `false` through the body storage seam; the enclosing prepared
//! transaction discards this uncommitted current and preserves the prior receiver whole.

use body::manifold::{SparseOwnCell, SparseOwnStorage};

#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct GrowingSparseOwn {
    cells: Vec<SparseOwnCell>,
}

impl GrowingSparseOwn {
    pub fn new() -> Self {
        Self { cells: Vec::new() }
    }

    pub fn cells(&self) -> &[SparseOwnCell] {
        &self.cells
    }

    pub fn into_cells(self) -> Vec<SparseOwnCell> {
        self.cells
    }
}

impl SparseOwnStorage for GrowingSparseOwn {
    fn reset(&mut self) -> bool {
        self.cells.clear();
        true
    }

    fn as_slice(&self) -> &[SparseOwnCell] {
        &self.cells
    }

    fn live_slice_mut(&mut self, live: usize) -> Option<&mut [SparseOwnCell]> {
        (live == self.cells.len()).then_some(self.cells.as_mut_slice())
    }

    fn insert_at(&mut self, live: usize, at: usize, cell: SparseOwnCell) -> bool {
        if live != self.cells.len() || at > live || self.cells.try_reserve(1).is_err() {
            return false;
        }
        self.cells.insert(at, cell);
        true
    }

    fn remove_at(&mut self, live: usize, at: usize) -> bool {
        if live != self.cells.len() || at >= live {
            return false;
        }
        self.cells.remove(at);
        true
    }
}
