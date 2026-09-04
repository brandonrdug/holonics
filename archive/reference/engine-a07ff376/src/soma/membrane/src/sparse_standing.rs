//! Rank-qualified sparse receiver terrain and prepared successor replacement.
//!
//! Standing construction occupies only lived addresses.  The chart is named by dyadic rank, not
//! a materialized side length, and every cell carries the two hierarchical coordinate paths.
//! Flat `u32` grips remain an exact compatibility projection for historical body/card gates.

use std::collections::BTreeMap;
use std::ops::Range;
use std::sync::{Arc, OnceLock};

use body::manifold::{SparseStandingCell as FlatStandingCell, StandingQuery};
use body::medium::RegionalForm;
use body::place::{Grip, Place};

use crate::active_topology::FoldedCut;
use crate::growing_ranked::ExactCount;
use crate::live_constituent::StandingConstituentAccess;
use crate::{ChartAddress, ChartAddressError, LiveConstituent};

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SparseStandingError {
    Geometry,
    GripExtent,
    Topology,
    StandingChanged,
    ResourceExtent,
    ResourceReservation,
    FlatCompatibility,
    Address(ChartAddressError),
}

impl From<ChartAddressError> for SparseStandingError {
    fn from(error: ChartAddressError) -> Self {
        Self::Address(error)
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StandingCell {
    address: ChartAddress,
    form: RegionalForm,
}

impl StandingCell {
    pub fn new(address: ChartAddress, form: RegionalForm) -> Option<Self> {
        form.occupied().then_some(Self { address, form })
    }

    pub fn address(&self) -> &ChartAddress {
        &self.address
    }

    pub fn form(&self) -> RegionalForm {
        self.form
    }
}

/// One event-transient cellular successor factor. `touched` addresses the immutable Standing
/// before-face only; it is validated and consumed during the atomic commit and never enters rest,
/// radiation, or constituent identity.
pub(crate) struct CellularStandingChange {
    touched: Vec<usize>,
    replacement: LiveConstituent,
}

impl CellularStandingChange {
    pub(crate) fn new(
        touched: Vec<usize>,
        replacement: LiveConstituent,
    ) -> Result<Self, SparseStandingError> {
        if touched.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(SparseStandingError::Topology);
        }
        Ok(Self {
            touched,
            replacement,
        })
    }

    pub(crate) fn touched(&self) -> &[usize] {
        &self.touched
    }

    pub(crate) const fn replacement(&self) -> &LiveConstituent {
        &self.replacement
    }
}

/// One canonical structural occurrence class in persistent Standing. Multiplicity remains
/// explicit because equal disconnected constituents are plural physical founders. The body and
/// its exact native key are shared by every immutable successor which did not change this class.
#[derive(Clone, Debug, PartialEq, Eq)]
struct PersistentConstituentEntry {
    key: Arc<[u32]>,
    body: Arc<LiveConstituent>,
    multiplicity: usize,
}

#[derive(Debug, PartialEq, Eq)]
struct PersistentConstituentNode {
    entry: PersistentConstituentEntry,
    left: Option<Arc<PersistentConstituentNode>>,
    right: Option<Arc<PersistentConstituentNode>>,
    height: u32,
    occurrences: usize,
}

struct PersistentConstituentInner {
    root: Option<Arc<PersistentConstituentNode>>,
    occurrences: usize,
    // Compatibility observation only. Production closure and replacement use the tree directly.
    flattened: OnceLock<Vec<LiveConstituent>>,
}

/// Immutable exact multiset used by the production standing transition. A local replacement
/// copies only the balanced-tree paths to the touched structural keys. Untouched constituent
/// bodies, subtrees, and exact keys remain shared; no successor-wide scan or canonical re-sort is
/// part of the transition.
#[derive(Clone)]
pub(crate) struct PersistentConstituentStanding {
    inner: Arc<PersistentConstituentInner>,
}

impl core::fmt::Debug for PersistentConstituentStanding {
    fn fmt(&self, formatter: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        formatter
            .debug_struct("PersistentConstituentStanding")
            .field("occurrences", &self.inner.occurrences)
            .field("root", &self.inner.root)
            .finish()
    }
}

impl PartialEq for PersistentConstituentStanding {
    fn eq(&self, other: &Self) -> bool {
        self.inner.occurrences == other.inner.occurrences
            && (0..self.inner.occurrences)
                .all(|ordinal| self.key_at(ordinal) == other.key_at(ordinal))
    }
}

impl Eq for PersistentConstituentStanding {}

impl PersistentConstituentStanding {
    fn from_constituents(constituents: Vec<LiveConstituent>) -> Result<Self, SparseStandingError> {
        let mut root = None;
        for constituent in constituents {
            let key: Arc<[u32]> = constituent
                .native_words()
                .map_err(|_| SparseStandingError::Topology)?
                .into();
            root = Some(insert_persistent_constituent(
                root.as_ref(),
                key,
                Arc::new(constituent),
            )?);
        }
        Ok(Self::from_root(root))
    }

    fn from_root(root: Option<Arc<PersistentConstituentNode>>) -> Self {
        let occurrences = persistent_occurrences(&root);
        Self {
            inner: Arc::new(PersistentConstituentInner {
                root,
                occurrences,
                flattened: OnceLock::new(),
            }),
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.inner.occurrences
    }

    pub(crate) fn get(&self, ordinal: usize) -> Option<&LiveConstituent> {
        persistent_constituent_at(self.inner.root.as_deref(), ordinal)
            .map(|entry| entry.body.as_ref())
    }

    pub(crate) fn key_at(&self, ordinal: usize) -> Option<Arc<[u32]>> {
        persistent_constituent_at(self.inner.root.as_deref(), ordinal)
            .map(|entry| entry.key.clone())
    }

    pub(crate) fn key_range(&self, key: &[u32]) -> Option<Range<usize>> {
        persistent_key_range(self.inner.root.as_deref(), key)
    }

    fn as_slice(&self) -> &[LiveConstituent] {
        self.inner.flattened.get_or_init(|| {
            let mut flattened = Vec::with_capacity(self.inner.occurrences);
            flatten_persistent_constituents(&self.inner.root, &mut flattened);
            flattened
        })
    }

    fn replace(&self, changes: &[CellularStandingChange]) -> Result<Self, SparseStandingError> {
        if changes.is_empty() {
            return Ok(self.clone());
        }

        // Resolve every transient ordinal against the immutable before-tree before changing any
        // structural range. This is proportional to the actually touched local population.
        let mut touched_ordinals = BTreeMap::new();
        let mut removals: BTreeMap<Arc<[u32]>, usize> = BTreeMap::new();
        for change in changes {
            for ordinal in change.touched() {
                if touched_ordinals.insert(*ordinal, ()).is_some() {
                    return Err(SparseStandingError::Topology);
                }
                let key = self.key_at(*ordinal).ok_or(SparseStandingError::Topology)?;
                let count = removals.entry(key).or_default();
                *count = count
                    .checked_add(1)
                    .ok_or(SparseStandingError::ResourceExtent)?;
            }
        }

        let mut root = self.inner.root.clone();
        for (key, count) in removals {
            root = remove_persistent_constituent(root.as_ref(), &key, count)?;
        }
        for change in changes {
            let replacement = change.replacement().clone();
            let key: Arc<[u32]> = replacement
                .native_words()
                .map_err(|_| SparseStandingError::Topology)?
                .into();
            root = Some(insert_persistent_constituent(
                root.as_ref(),
                key,
                Arc::new(replacement),
            )?);
        }
        Ok(Self::from_root(root))
    }
}

impl StandingConstituentAccess for PersistentConstituentStanding {
    fn standing_len(&self) -> usize {
        self.len()
    }

    fn standing_get(&self, ordinal: usize) -> Option<&LiveConstituent> {
        self.get(ordinal)
    }

    fn standing_key_at(&self, ordinal: usize) -> Result<Arc<[u32]>, crate::LiveConstituentError> {
        self.key_at(ordinal)
            .ok_or(crate::LiveConstituentError::Topology)
    }

    fn standing_key_range(&self, key: &[u32]) -> Result<Range<usize>, crate::LiveConstituentError> {
        self.key_range(key)
            .ok_or(crate::LiveConstituentError::Topology)
    }
}

fn persistent_height(node: &Option<Arc<PersistentConstituentNode>>) -> u32 {
    node.as_ref().map_or(0, |node| node.height)
}

fn persistent_occurrences(node: &Option<Arc<PersistentConstituentNode>>) -> usize {
    node.as_ref().map_or(0, |node| node.occurrences)
}

fn persistent_node(
    entry: PersistentConstituentEntry,
    left: Option<Arc<PersistentConstituentNode>>,
    right: Option<Arc<PersistentConstituentNode>>,
) -> Result<Arc<PersistentConstituentNode>, SparseStandingError> {
    let occurrences = persistent_occurrences(&left)
        .checked_add(entry.multiplicity)
        .and_then(|count| count.checked_add(persistent_occurrences(&right)))
        .ok_or(SparseStandingError::ResourceExtent)?;
    let height = persistent_height(&left)
        .max(persistent_height(&right))
        .checked_add(1)
        .ok_or(SparseStandingError::ResourceExtent)?;
    Ok(Arc::new(PersistentConstituentNode {
        entry,
        height,
        occurrences,
        left,
        right,
    }))
}

fn balance_persistent_node(
    entry: PersistentConstituentEntry,
    mut left: Option<Arc<PersistentConstituentNode>>,
    mut right: Option<Arc<PersistentConstituentNode>>,
) -> Result<Arc<PersistentConstituentNode>, SparseStandingError> {
    let balance = i64::from(persistent_height(&left)) - i64::from(persistent_height(&right));
    if balance > 1 {
        let left_node = left.as_ref().ok_or(SparseStandingError::Topology)?;
        if persistent_height(&left_node.left) < persistent_height(&left_node.right) {
            left = Some(rotate_persistent_left(left_node)?);
        }
        return rotate_persistent_right(entry, left, right);
    }
    if balance < -1 {
        let right_node = right.as_ref().ok_or(SparseStandingError::Topology)?;
        if persistent_height(&right_node.right) < persistent_height(&right_node.left) {
            right = Some(rotate_persistent_right(
                right_node.entry.clone(),
                right_node.left.clone(),
                right_node.right.clone(),
            )?);
        }
        return rotate_persistent_left_parts(entry, left, right);
    }
    persistent_node(entry, left, right)
}

fn rotate_persistent_right(
    entry: PersistentConstituentEntry,
    left: Option<Arc<PersistentConstituentNode>>,
    right: Option<Arc<PersistentConstituentNode>>,
) -> Result<Arc<PersistentConstituentNode>, SparseStandingError> {
    let pivot = left.ok_or(SparseStandingError::Topology)?;
    let carried = persistent_node(entry, pivot.right.clone(), right)?;
    persistent_node(pivot.entry.clone(), pivot.left.clone(), Some(carried))
}

fn rotate_persistent_left(
    node: &PersistentConstituentNode,
) -> Result<Arc<PersistentConstituentNode>, SparseStandingError> {
    rotate_persistent_left_parts(node.entry.clone(), node.left.clone(), node.right.clone())
}

fn rotate_persistent_left_parts(
    entry: PersistentConstituentEntry,
    left: Option<Arc<PersistentConstituentNode>>,
    right: Option<Arc<PersistentConstituentNode>>,
) -> Result<Arc<PersistentConstituentNode>, SparseStandingError> {
    let pivot = right.ok_or(SparseStandingError::Topology)?;
    let carried = persistent_node(entry, left, pivot.left.clone())?;
    persistent_node(pivot.entry.clone(), Some(carried), pivot.right.clone())
}

fn insert_persistent_constituent(
    node: Option<&Arc<PersistentConstituentNode>>,
    key: Arc<[u32]>,
    body: Arc<LiveConstituent>,
) -> Result<Arc<PersistentConstituentNode>, SparseStandingError> {
    let Some(node) = node else {
        return persistent_node(
            PersistentConstituentEntry {
                key,
                body,
                multiplicity: 1,
            },
            None,
            None,
        );
    };
    match key.as_ref().cmp(node.entry.key.as_ref()) {
        core::cmp::Ordering::Less => {
            let left = Some(insert_persistent_constituent(
                node.left.as_ref(),
                key,
                body,
            )?);
            balance_persistent_node(node.entry.clone(), left, node.right.clone())
        }
        core::cmp::Ordering::Greater => {
            let right = Some(insert_persistent_constituent(
                node.right.as_ref(),
                key,
                body,
            )?);
            balance_persistent_node(node.entry.clone(), node.left.clone(), right)
        }
        core::cmp::Ordering::Equal => {
            if node.entry.body.as_ref() != body.as_ref() {
                return Err(SparseStandingError::Topology);
            }
            let mut entry = node.entry.clone();
            entry.multiplicity = entry
                .multiplicity
                .checked_add(1)
                .ok_or(SparseStandingError::ResourceExtent)?;
            persistent_node(entry, node.left.clone(), node.right.clone())
        }
    }
}

fn remove_persistent_constituent(
    node: Option<&Arc<PersistentConstituentNode>>,
    key: &[u32],
    count: usize,
) -> Result<Option<Arc<PersistentConstituentNode>>, SparseStandingError> {
    let node = node.ok_or(SparseStandingError::Topology)?;
    match key.cmp(node.entry.key.as_ref()) {
        core::cmp::Ordering::Less => {
            let left = remove_persistent_constituent(node.left.as_ref(), key, count)?;
            Ok(Some(balance_persistent_node(
                node.entry.clone(),
                left,
                node.right.clone(),
            )?))
        }
        core::cmp::Ordering::Greater => {
            let right = remove_persistent_constituent(node.right.as_ref(), key, count)?;
            Ok(Some(balance_persistent_node(
                node.entry.clone(),
                node.left.clone(),
                right,
            )?))
        }
        core::cmp::Ordering::Equal => {
            if count == 0 || count > node.entry.multiplicity {
                return Err(SparseStandingError::Topology);
            }
            if count < node.entry.multiplicity {
                let mut entry = node.entry.clone();
                entry.multiplicity -= count;
                return Ok(Some(persistent_node(
                    entry,
                    node.left.clone(),
                    node.right.clone(),
                )?));
            }
            match (&node.left, &node.right) {
                (None, None) => Ok(None),
                (Some(left), None) => Ok(Some(left.clone())),
                (None, Some(right)) => Ok(Some(right.clone())),
                (Some(_), Some(right)) => {
                    let (successor, remaining_right) = take_persistent_min(right)?;
                    Ok(Some(balance_persistent_node(
                        successor,
                        node.left.clone(),
                        remaining_right,
                    )?))
                }
            }
        }
    }
}

fn take_persistent_min(
    node: &Arc<PersistentConstituentNode>,
) -> Result<
    (
        PersistentConstituentEntry,
        Option<Arc<PersistentConstituentNode>>,
    ),
    SparseStandingError,
> {
    let Some(left) = &node.left else {
        return Ok((node.entry.clone(), node.right.clone()));
    };
    let (minimum, remaining_left) = take_persistent_min(left)?;
    Ok((
        minimum,
        Some(balance_persistent_node(
            node.entry.clone(),
            remaining_left,
            node.right.clone(),
        )?),
    ))
}

fn persistent_constituent_at(
    mut node: Option<&PersistentConstituentNode>,
    mut ordinal: usize,
) -> Option<&PersistentConstituentEntry> {
    while let Some(current) = node {
        let left = persistent_occurrences(&current.left);
        let current_end = left.checked_add(current.entry.multiplicity)?;
        if ordinal < left {
            node = current.left.as_deref();
        } else if ordinal < current_end {
            return Some(&current.entry);
        } else {
            ordinal = ordinal.checked_sub(current_end)?;
            node = current.right.as_deref();
        }
    }
    None
}

fn persistent_key_range(
    mut node: Option<&PersistentConstituentNode>,
    key: &[u32],
) -> Option<Range<usize>> {
    let mut before = 0usize;
    while let Some(current) = node {
        match key.cmp(current.entry.key.as_ref()) {
            core::cmp::Ordering::Less => node = current.left.as_deref(),
            core::cmp::Ordering::Greater => {
                before = before
                    .checked_add(persistent_occurrences(&current.left))?
                    .checked_add(current.entry.multiplicity)?;
                node = current.right.as_deref();
            }
            core::cmp::Ordering::Equal => {
                let start = before.checked_add(persistent_occurrences(&current.left))?;
                return Some(start..start.checked_add(current.entry.multiplicity)?);
            }
        }
    }
    None
}

fn flatten_persistent_constituents(
    node: &Option<Arc<PersistentConstituentNode>>,
    flattened: &mut Vec<LiveConstituent>,
) {
    let Some(node) = node else {
        return;
    };
    flatten_persistent_constituents(&node.left, flattened);
    for _ in 0..node.entry.multiplicity {
        flattened.push(node.entry.body.as_ref().clone());
    }
    flatten_persistent_constituents(&node.right, flattened);
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SparseStandingSurface {
    rank: u64,
    cells: Vec<StandingCell>,
    constituents: PersistentConstituentStanding,
    flat_axis: Option<u32>,
    flat_cells: Vec<FlatStandingCell>,
}

impl SparseStandingSurface {
    /// Historical flat constructor.  It is retained for parity gates and lifts immediately into
    /// the rank-qualified representation.
    pub fn empty(axis: u32) -> Result<Self, SparseStandingError> {
        let rank = flat_axis_rank(axis)?;
        Self::empty_rank(rank)
    }

    pub fn empty_rank(rank: u64) -> Result<Self, SparseStandingError> {
        Self::from_ranked_cells(rank, Vec::new())
    }

    pub fn from_cells(
        axis: u32,
        cells: Vec<FlatStandingCell>,
    ) -> Result<Self, SparseStandingError> {
        let rank = flat_axis_rank(axis)?;
        let extent = (axis as u64)
            .checked_mul(axis as u64)
            .ok_or(SparseStandingError::ResourceExtent)?;
        let mut ranked = Vec::new();
        ranked
            .try_reserve_exact(cells.len())
            .map_err(|_| SparseStandingError::ResourceReservation)?;
        let mut previous = None;
        for cell in cells {
            if !cell.form().occupied()
                || cell.grip() as u64 >= extent
                || previous.is_some_and(|grip| grip >= cell.grip())
            {
                return Err(SparseStandingError::Topology);
            }
            previous = Some(cell.grip());
            ranked.push(
                StandingCell::new(
                    ChartAddress::from_flat_grip(cell.grip(), axis)?,
                    cell.form(),
                )
                .ok_or(SparseStandingError::Topology)?,
            );
        }
        // Flat grip order and address order are not assumed to be the same storage gauge.
        ranked.sort_unstable_by(|left, right| left.address.cmp(&right.address));
        Self::from_ranked_cells(rank, ranked)
    }

    pub fn from_ranked_cells(
        rank: u64,
        cells: Vec<StandingCell>,
    ) -> Result<Self, SparseStandingError> {
        Self::from_ranked_cells_with_constituents(rank, cells, Vec::new())
    }

    /// Reopen or prepare one exact Standing face whose scalar and cellular terrain have already
    /// crossed the same atomic boundary. Constituents are ordered by their complete native
    /// geometry while retaining multiplicity: equal disconnected bodies are still two actual
    /// co-present founders, not duplicated event history and not one body by value.
    pub fn from_ranked_cells_with_constituents(
        rank: u64,
        cells: Vec<StandingCell>,
        constituents: Vec<LiveConstituent>,
    ) -> Result<Self, SparseStandingError> {
        let constituents = PersistentConstituentStanding::from_constituents(constituents)?;
        Self::from_ranked_cells_with_persistent_constituents(rank, cells, constituents)
    }

    fn from_ranked_cells_with_persistent_constituents(
        rank: u64,
        cells: Vec<StandingCell>,
        constituents: PersistentConstituentStanding,
    ) -> Result<Self, SparseStandingError> {
        let mut previous: Option<&ChartAddress> = None;
        for cell in &cells {
            if !cell.form.occupied()
                || cell.address.rank() != rank
                || previous.is_some_and(|address| address >= &cell.address)
            {
                return Err(SparseStandingError::Topology);
            }
            previous = Some(&cell.address);
        }

        let flat_axis = if rank <= 16 { Some(1u32 << rank) } else { None };
        let mut flat_cells = Vec::new();
        if flat_axis.is_some() {
            flat_cells
                .try_reserve_exact(cells.len())
                .map_err(|_| SparseStandingError::ResourceReservation)?;
            for cell in &cells {
                let grip = cell
                    .address
                    .try_flat_grip()
                    .ok_or(SparseStandingError::FlatCompatibility)?;
                flat_cells.push(
                    FlatStandingCell::new(grip, cell.form).ok_or(SparseStandingError::Topology)?,
                );
            }
            flat_cells.sort_unstable_by_key(|cell| cell.grip());
        }

        Ok(Self {
            rank,
            cells,
            constituents,
            flat_axis,
            flat_cells,
        })
    }

    pub fn rank(&self) -> u64 {
        self.rank
    }

    pub fn cells(&self) -> &[StandingCell] {
        &self.cells
    }

    pub fn constituents(&self) -> &[LiveConstituent] {
        self.constituents.as_slice()
    }

    pub(crate) const fn constituent_standing(&self) -> &PersistentConstituentStanding {
        &self.constituents
    }

    /// Exact higher-grain recurrence read. This is used while the next regional cell is still
    /// borrowed so a receiver can RIDE an already-founded pin rather than allocate a duplicate
    /// direction. It is a local geometric comparison, not provenance or a semantic lookup.
    pub fn contains_pin(&self, pin: crate::LivePin) -> bool {
        (0..self.constituents.len()).any(|ordinal| {
            self.constituents
                .get(ordinal)
                .is_some_and(|constituent| constituent.contains_pin(&pin))
        })
    }

    /// Exact compatibility projection for the existing flat body mouth.  A deep chart has no
    /// flattening; the forthcoming direct standing-query mouth consumes ranked addresses.
    pub fn flat_axis(&self) -> Option<u32> {
        self.flat_axis
    }

    pub fn flat_cells(&self) -> Option<&[FlatStandingCell]> {
        self.flat_axis.map(|_| self.flat_cells.as_slice())
    }

    pub fn form_at_address(&self, address: &ChartAddress) -> RegionalForm {
        self.cells
            .binary_search_by(|cell| cell.address.cmp(address))
            .ok()
            .map(|at| self.cells[at].form)
            .unwrap_or(RegionalForm::UNBORN)
    }

    /// Read this standing surface in an equal or wider dyadic gauge.  Existing construction lies
    /// only on the enacted zero section; an off-section address is genuinely unborn at this cut.
    pub fn form_at_projected(
        &self,
        address: &ChartAddress,
    ) -> Result<RegionalForm, SparseStandingError> {
        if address.rank() < self.rank {
            return Err(SparseStandingError::Geometry);
        }
        if address.rank() == self.rank {
            return Ok(self.form_at_address(address));
        }
        match address.zero_section_source(self.rank) {
            Ok(source) => Ok(self.form_at_address(&source)),
            Err(ChartAddressError::NarrowSectionAbsent) => Ok(RegionalForm::UNBORN),
            Err(error) => Err(error.into()),
        }
    }

    /// Historical flat observer.  It is not used by ranked conduct.
    pub fn form_at(&self, grip: u32) -> RegionalForm {
        self.flat_cells
            .binary_search_by_key(&grip, |cell| cell.grip())
            .ok()
            .map(|at| self.flat_cells[at].form())
            .unwrap_or(RegionalForm::UNBORN)
    }

    /// Materialize the already-integrated after-face without changing this receiver.  The entire
    /// before-face and allocation boundary close before the first successor row is written.
    pub(crate) fn prepare_successor(
        &self,
        folded: &FoldedCut,
    ) -> Result<Self, SparseStandingError> {
        if folded.standing_rank() < self.rank {
            return Err(SparseStandingError::Geometry);
        }
        let base = if folded.standing_rank() == self.rank {
            self.clone()
        } else {
            self.zero_extend(folded.standing_rank())?
        };
        let mut additional = 0usize;
        for cell in folded.cells() {
            if base.form_at_address(cell.address()) != cell.before() {
                return Err(SparseStandingError::StandingChanged);
            }
            if !cell.after().occupied() {
                return Err(SparseStandingError::Topology);
            }
            if base
                .cells
                .binary_search_by(|standing| standing.address.cmp(cell.address()))
                .is_err()
            {
                additional = additional
                    .checked_add(1)
                    .ok_or(SparseStandingError::ResourceExtent)?;
            }
        }

        let capacity = base
            .cells
            .len()
            .checked_add(additional)
            .ok_or(SparseStandingError::ResourceExtent)?;
        let mut cells = Vec::new();
        cells
            .try_reserve_exact(capacity)
            .map_err(|_| SparseStandingError::ResourceReservation)?;
        cells.extend_from_slice(&base.cells);
        for folded in folded.cells() {
            match cells.binary_search_by(|standing| standing.address.cmp(folded.address())) {
                Ok(at) => {
                    cells[at] = StandingCell::new(folded.address().clone(), folded.after())
                        .ok_or(SparseStandingError::Topology)?;
                }
                Err(at) => cells.insert(
                    at,
                    StandingCell::new(folded.address().clone(), folded.after())
                        .ok_or(SparseStandingError::Topology)?,
                ),
            }
        }
        Self::from_ranked_cells_with_persistent_constituents(
            folded.standing_rank(),
            cells,
            base.constituents,
        )
    }

    /// Integrate the complete population which actually arrived at one contemporary event.
    /// Every contribution is a current-local construction already enacted against this same
    /// immutable before-face.  The receiver chooses its next exact grain from that population,
    /// combines collocated forms without imposing an arrival order, and returns a wholly prepared
    /// successor.  No active cut, incidence ledger, journal, or source extent participates.
    pub(crate) fn prepare_contemporary_successor(
        &self,
        contributions: &[(Place, RegionalForm)],
        cellular: &[CellularStandingChange],
    ) -> Result<Self, SparseStandingError> {
        let scalar = self.prepare_scalar_contemporary_successor(contributions)?;
        if cellular.is_empty() {
            return Ok(scalar);
        }

        let constituents = scalar.constituents.replace(cellular)?;
        Self::from_ranked_cells_with_persistent_constituents(
            scalar.rank,
            scalar.cells,
            constituents,
        )
    }

    fn prepare_scalar_contemporary_successor(
        &self,
        contributions: &[(Place, RegionalForm)],
    ) -> Result<Self, SparseStandingError> {
        if contributions.is_empty() {
            return Ok(self.clone());
        }
        if contributions.iter().any(|(_, form)| !form.occupied()) {
            return Err(SparseStandingError::Topology);
        }

        // A receiver digit is caused only by the exact population of genuinely new addresses at
        // this event.  Every wider candidate is retried from the same standing-before surface.
        let mut accepted_rank = self.rank;
        loop {
            let mut distinct = Vec::new();
            distinct
                .try_reserve_exact(contributions.len())
                .map_err(|_| SparseStandingError::ResourceReservation)?;
            for (position, _) in contributions {
                distinct.push(ChartAddress::ground(*position, accepted_rank)?);
            }
            distinct.sort_unstable();
            distinct.dedup();

            let mut occupancy = ExactCount::from_usize(self.cells.len());
            let mut carried = false;
            for address in &distinct {
                if self.form_at_projected(address)?.occupied() {
                    continue;
                }
                let after = occupancy.incremented().map_err(map_ranked_resource)?;
                let tooth = if accepted_rank == 0 {
                    0
                } else {
                    accepted_rank
                        .checked_mul(2)
                        .and_then(|value| value.checked_sub(1))
                        .ok_or(SparseStandingError::ResourceExtent)?
                };
                carried |= occupancy
                    .entered_bit(&after, tooth)
                    .map_err(map_ranked_resource)?;
                occupancy = after;
            }
            if !carried {
                break;
            }
            accepted_rank = accepted_rank
                .checked_add(1)
                .ok_or(SparseStandingError::ResourceExtent)?;
        }

        let mut grounded = Vec::new();
        grounded
            .try_reserve_exact(contributions.len())
            .map_err(|_| SparseStandingError::ResourceReservation)?;
        for (position, form) in contributions {
            grounded.push((ChartAddress::ground(*position, accepted_rank)?, *form));
        }
        grounded.sort_unstable_by(|left, right| left.0.cmp(&right.0));

        let base = self.zero_extend(accepted_rank)?;
        let mut cells = Vec::new();
        cells
            .try_reserve_exact(
                base.cells
                    .len()
                    .checked_add(grounded.len())
                    .ok_or(SparseStandingError::ResourceExtent)?,
            )
            .map_err(|_| SparseStandingError::ResourceReservation)?;
        cells.extend_from_slice(&base.cells);

        let mut forms = Vec::new();
        forms
            .try_reserve_exact(grounded.len().saturating_add(1))
            .map_err(|_| SparseStandingError::ResourceReservation)?;
        let mut at = 0usize;
        while at < grounded.len() {
            let address = grounded[at].0.clone();
            let before = base.form_at_address(&address);
            forms.clear();
            forms.push(before);
            while at < grounded.len() && grounded[at].0 == address {
                forms.push(grounded[at].1);
                at += 1;
            }
            let after = body::medium::integrate(&forms).occupy();
            let replacement =
                StandingCell::new(address.clone(), after).ok_or(SparseStandingError::Topology)?;
            match cells.binary_search_by(|cell| cell.address.cmp(&address)) {
                Ok(cell) => cells[cell] = replacement,
                Err(cell) => cells.insert(cell, replacement),
            }
        }
        Self::from_ranked_cells_with_persistent_constituents(
            accepted_rank,
            cells,
            self.constituents.clone(),
        )
    }

    /// Apply an actual receiver digit without visiting an axis-square plane.  Every occupied
    /// aggregate enters the exact zero section; its form remains whole.
    pub fn zero_extend(&self, new_rank: u64) -> Result<Self, SparseStandingError> {
        if new_rank < self.rank {
            return Err(SparseStandingError::Geometry);
        }
        let mut cells = Vec::new();
        cells
            .try_reserve_exact(self.cells.len())
            .map_err(|_| SparseStandingError::ResourceReservation)?;
        for cell in &self.cells {
            cells.push(
                StandingCell::new(cell.address.zero_extend(new_rank)?, cell.form)
                    .ok_or(SparseStandingError::Topology)?,
            );
        }
        cells.sort_unstable_by(|left, right| left.address.cmp(&right.address));
        Self::from_ranked_cells_with_persistent_constituents(
            new_rank,
            cells,
            self.constituents.clone(),
        )
    }
}

fn map_ranked_resource(error: body::manifold::RankedOwnError) -> SparseStandingError {
    match error {
        body::manifold::RankedOwnError::ResourceReservation => {
            SparseStandingError::ResourceReservation
        }
        body::manifold::RankedOwnError::ResourceExtent => SparseStandingError::ResourceExtent,
        body::manifold::RankedOwnError::Geometry
        | body::manifold::RankedOwnError::Topology
        | body::manifold::RankedOwnError::Poisoned => SparseStandingError::Topology,
    }
}

impl StandingQuery for SparseStandingSurface {
    fn receiver_rank(&self) -> u64 {
        self.rank
    }

    fn form_at_position(&self, position: Place) -> Option<RegionalForm> {
        let mut refused = false;
        let found = self.cells.binary_search_by(|cell| {
            cell.address.cmp_grounded(position).unwrap_or_else(|_| {
                refused = true;
                core::cmp::Ordering::Less
            })
        });
        if refused {
            return None;
        }
        Some(
            found
                .ok()
                .map(|at| self.cells[at].form)
                .unwrap_or(RegionalForm::UNBORN),
        )
    }

    fn form_at_flat_grip(&self, grip: Grip) -> Option<RegionalForm> {
        self.flat_axis.map(|_| self.form_at(grip))
    }
}

fn flat_axis_rank(axis: u32) -> Result<u64, SparseStandingError> {
    if axis == 0 || !axis.is_power_of_two() {
        return Err(SparseStandingError::Geometry);
    }
    if axis > 1 << 16 {
        return Err(SparseStandingError::GripExtent);
    }
    Ok(axis.trailing_zeros() as u64)
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    use body::arrow::Arrow;
    use body::channel::{LineageChannel, WindingQuantum};
    use body::incidence::IncidenceHand;
    use body::manifold::{DirectedEventContact, EventReceiver, Face};
    use body::num::Cog;

    use crate::{
        InterfaceCapability, LiveBoundary, LiveCell, LiveIncidence, LiveIncidenceKind, LivePath,
        LivePathStep, LivePin, LocalAxis,
    };

    fn test_constituent(reach: i64) -> LiveConstituent {
        let meeting = Face {
            arrow: Arrow {
                reach: Cog::lit(reach),
                aim: Cog::lit(3),
                cross: Cog::ZERO,
            },
        };
        let held = Face {
            arrow: Arrow {
                reach: Cog::lit(11),
                aim: Cog::lit(2),
                cross: Cog::ZERO,
            },
        };
        let pin = LivePin::from_interface_contact(
            DirectedEventContact {
                receiver: EventReceiver {
                    channel: LineageChannel::from_located_first_difference((
                        Cog::lit(1),
                        Cog::lit(2),
                    )),
                    held,
                    held_live: true,
                },
                meeting,
                emission: None,
            },
            InterfaceCapability::new(0x5354_414e_4449_4e47, reach as u64),
        );
        let incidences = vec![LiveIncidence::new(
            0,
            1,
            LiveIncidenceKind::Transport,
            IncidenceHand::With,
            0,
        )];
        let pins = vec![pin];
        let path = LivePath::from_steps(
            vec![LivePathStep::new(
                0,
                LocalAxis::new(0),
                WindingQuantum::None,
            )],
            &incidences,
            &pins,
        )
        .unwrap();
        LiveConstituent::new(
            2,
            1,
            vec![
                LiveCell::new(0, 0, 0),
                LiveCell::new(0, 0, 0),
                LiveCell::new(1, 1, 2),
            ],
            incidences,
            pins,
            vec![LiveBoundary::new(IncidenceHand::With, vec![path])],
            vec![0],
        )
        .unwrap()
    }

    fn persistent_node_addresses(
        node: &Option<Arc<PersistentConstituentNode>>,
        addresses: &mut BTreeSet<usize>,
    ) {
        let Some(node) = node else {
            return;
        };
        addresses.insert(Arc::as_ptr(node) as usize);
        persistent_node_addresses(&node.left, addresses);
        persistent_node_addresses(&node.right, addresses);
    }

    #[test]
    fn flat_construction_ends_at_the_last_exact_u32_grip_chart() {
        assert!(SparseStandingSurface::empty(1 << 16).is_ok());
        assert_eq!(
            SparseStandingSurface::empty(1 << 17),
            Err(SparseStandingError::GripExtent)
        );
        assert!(SparseStandingSurface::empty_rank(17).is_ok());
        assert!(SparseStandingSurface::empty_rank(80)
            .unwrap()
            .flat_axis()
            .is_none());
    }

    #[test]
    fn a_local_cellular_successor_reuses_untouched_structural_standing() {
        let bodies = (1..=63).map(test_constituent).collect::<Vec<_>>();
        let before = PersistentConstituentStanding::from_constituents(bodies).unwrap();
        let touched = 31usize;
        let departed = before.key_at(touched).unwrap();
        let replacement = test_constituent(10_001);
        let replacement_key: Arc<[u32]> = replacement.native_words().unwrap().into();
        let change = CellularStandingChange::new(vec![touched], replacement).unwrap();

        let after = before.replace(&[change]).unwrap();

        assert_eq!(before.len(), 63);
        assert_eq!(after.len(), 63);
        assert!(before.inner.flattened.get().is_none());
        assert!(after.inner.flattened.get().is_none());
        assert!(after.key_range(&departed).is_none());
        assert_eq!(after.key_range(&replacement_key).unwrap().len(), 1);
        for ordinal in 1..after.len() {
            assert!(after.key_at(ordinal - 1).unwrap() <= after.key_at(ordinal).unwrap());
        }

        let mut before_nodes = BTreeSet::new();
        let mut after_nodes = BTreeSet::new();
        persistent_node_addresses(&before.inner.root, &mut before_nodes);
        persistent_node_addresses(&after.inner.root, &mut after_nodes);
        let shared = before_nodes.intersection(&after_nodes).count();
        assert!(
            shared >= 48,
            "a one-factor replacement unexpectedly rebuilt the standing tree: {shared} shared"
        );
    }

    #[test]
    fn equal_disconnected_bodies_remain_a_persistent_multiplicity() {
        let body = test_constituent(17);
        let before = PersistentConstituentStanding::from_constituents(vec![
            body.clone(),
            body.clone(),
            body,
        ])
        .unwrap();
        let key = before.key_at(0).unwrap();
        assert_eq!(before.key_range(&key).unwrap(), 0..3);

        let replacement = test_constituent(19);
        let after = before
            .replace(&[CellularStandingChange::new(vec![1], replacement).unwrap()])
            .unwrap();
        assert_eq!(after.len(), 3);
        assert_eq!(after.key_range(&key).unwrap().len(), 2);
    }
}
