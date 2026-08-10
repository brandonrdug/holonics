//! carriage — the substrate-neutral whole lineage stroke (`FORMULA §XXVIII-b` ⊕ `§XXXIII`).
//!
//! One invocation owns one mutable OWN reservation, one complete carrier/K row, and one radiation
//! aperture. The shell carves those disjoint ranges before entering this mouth; standing and raw
//! light remain shared read-only. The single-writer construction is the determinism. Atomicity is
//! only the substrate spelling of the same word store, never an ordering mechanism.
//!
//! The declared unsafe word seam has exactly two operations: unchecked `u32` read and store. It
//! lives below this driver so the canonical packed readers and every explicit scalar path share the
//! same grounding mouth. This file carries every decision that advances lineage time: genesis/K
//! recovery, cursor validation, stroke extent, atom traversal, true-end darkness, complete carrier
//! storage, and the returned term face.

#[path = "carriage/register_chart.rs"]
mod register_chart;

use core::marker::PhantomData;

use crate::boundary;
use crate::channel;
use crate::manifold::{self, Face, Node, TermCounts};
use crate::medium::{self, RegionalForm, FORM_WORDS};
use crate::num;
use crate::place;
use crate::register;
pub use crate::seam::WordSeam;
use crate::soul;

/// A shell-carved, invocation-exclusive range within one substrate binding. SPIR-V cannot form a
/// dynamically ranged Rust slice, so the capability crosses as its checked base and extent. Every
/// coordinate used by the carriage remains local to this span; no sibling invocation can be named.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WordSpan {
    base: usize,
    len: usize,
}

impl WordSpan {
    #[inline(always)]
    pub const fn new(base: usize, len: usize) -> WordSpan {
        WordSpan { base, len }
    }

    #[inline(always)]
    pub const fn empty() -> WordSpan {
        WordSpan { base: 0, len: 0 }
    }
}

/// The immutable face shared by every co-present REGISTER contact of one enclosure arrival.
/// This is invocation-local construction, not carried body state: a substrate may form the
/// contacts together, but their deeds still enter OWN in the lineage's existing ring order.
#[derive(Clone, Copy, Debug)]
pub struct RegisterContactSnapshot {
    pub register_at: usize,
    pub head: usize,
    pub live: usize,
    pub node: Node,
    pub frame: place::Place,
    pub fly: Face,
    pub fly_live: bool,
}

/// A substrate realization of the one genuinely co-present interior surface. `prepare` may form
/// every contact from the immutable snapshot together; `select` exposes one formed face through
/// caller-owned scalar χ arms.
/// The body remains the sole owner of chronological deposit, K, enclosure mutation, and completion.
pub trait RegisterContactSurface<S: WordSeam> {
    fn prepare(&mut self, carriers: &[u32], snapshot: RegisterContactSnapshot);

    fn select(
        &self,
        carriers: &[u32],
        snapshot: RegisterContactSnapshot,
        index: usize,
        same: &mut num::Cog,
        other: &mut num::Cog,
    ) -> bool;
}

/// The ordinary host/SPIR-V realization: form each contact at the carried deed that consumes it.
/// It is the exact inline chronological foil for cooperative substrate surfaces.
pub struct InlineRegisterContactSurface;

impl<S: WordSeam> RegisterContactSurface<S> for InlineRegisterContactSurface {
    #[inline(always)]
    fn prepare(&mut self, _carriers: &[u32], _snapshot: RegisterContactSnapshot) {}

    #[inline(always)]
    fn select(
        &self,
        carriers: &[u32],
        snapshot: RegisterContactSnapshot,
        index: usize,
        same: &mut num::Cog,
        other: &mut num::Cog,
    ) -> bool {
        form_register_contact::<S>(carriers, snapshot, index, same, other)
    }
}

/// Form one REGISTER contact without changing OWN, K, an enclosure, or completion. All live
/// contacts at this arrival call this operation against the same snapshot, so a cooperative card
/// block may evaluate them together before the body commits them oldest-to-newest.
#[inline(never)]
pub fn form_register_contact<S: WordSeam>(
    carriers: &[u32],
    snapshot: RegisterContactSnapshot,
    index: usize,
    same: &mut num::Cog,
    other: &mut num::Cog,
) -> bool {
    *same = num::Cog::ZERO;
    *other = num::Cog::ZERO;
    if !snapshot.fly_live
        || !snapshot.fly.rotor_formed()
        || index >= snapshot.live
        || index >= register::REGISTER as usize
    {
        return false;
    }
    let slot = (snapshot.head + register::REGISTER as usize - snapshot.live + index)
        % register::REGISTER as usize;
    let Some(words) = checked_extent_mul(slot, manifold::NODE_WORDS) else {
        return false;
    };
    let Some(at) = checked_extent_add(snapshot.register_at, words) else {
        return false;
    };
    let co_present = manifold::unpack_node_with::<S>(carriers, at);
    if co_present.len == 0 {
        return false;
    }
    let meeting = manifold::face(co_present.place, snapshot.node.place, snapshot.frame);
    if !meeting.rotor_formed() {
        return false;
    }
    let chi = meeting.chi_against_formed(&snapshot.fly);
    *same = chi.same;
    *other = chi.other;
    true
}

/// A span whose whole base ⊕ extent and required local body have been proved before mutation.
/// Only this private capability enters the hot carriage verb; its local coordinates are justified
/// by the structural carrier layout or by the grip/count guards beside each use.
#[derive(Clone, Copy)]
struct ValidatedSpan {
    base: usize,
    len: usize,
}

impl ValidatedSpan {
    #[inline(never)]
    fn form(words_len: usize, span: WordSpan, required: usize) -> Option<ValidatedSpan> {
        if span.base > words_len || span.len > words_len - span.base || required > span.len {
            None
        } else {
            Some(ValidatedSpan {
                base: span.base,
                len: span.len,
            })
        }
    }

    #[inline(always)]
    fn absolute(self, local: usize) -> usize {
        self.base + local
    }
}

/// Checked boundary extent arithmetic spelled without Rust's `checked_*` intrinsics, which the
/// pinned rust-gpu backend cannot lower. Failure rejects the invocation before body mutation.
#[inline(never)]
pub fn checked_extent_add(left: usize, right: usize) -> Option<usize> {
    if right > usize::MAX - left {
        None
    } else {
        Some(left + right)
    }
}

#[inline(never)]
pub fn checked_extent_mul(left: usize, right: usize) -> Option<usize> {
    if left != 0 && right > usize::MAX / left {
        None
    } else {
        Some(left * right)
    }
}

#[inline(never)]
fn checked_worldline_add(left: u64, right: u64) -> Option<u64> {
    if right > u64::MAX - left {
        None
    } else {
        Some(left + right)
    }
}

/// One world-delivered lineage stroke after a substrate shell has decoded its ABI. Mutable buffer
/// offsets remain outside the law itself: the shell supplies them only as already carved spans.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LineageStroke {
    standing_axis: i64,
    own_axis: i64,
    cells: usize,
    own_cells: usize,
    byte_offset: usize,
    byte_count: usize,
    seed_previous: u32,
    seed_current: u32,
    worldline_base: u64,
    stroke_atoms: usize,
    interior_installment: usize,
    drive: u32,
    radiation_stride: usize,
    completion_stride: usize,
}

impl LineageStroke {
    /// The accepted dense mirror: standing and OWN share one declared chart grain.
    #[allow(clippy::too_many_arguments)]
    pub fn dense(
        axis: i64,
        cells: usize,
        byte_offset: usize,
        byte_count: usize,
        seed_previous: u32,
        seed_current: u32,
        worldline_base: u64,
        stroke_atoms: usize,
        drive: u32,
    ) -> LineageStroke {
        LineageStroke {
            standing_axis: axis,
            own_axis: axis,
            cells,
            own_cells: cells,
            byte_offset,
            byte_count,
            seed_previous,
            seed_current,
            worldline_base,
            stroke_atoms,
            interior_installment: 0,
            drive,
            radiation_stride: 0,
            completion_stride: 0,
        }
    }

    /// The founded-cell species: standing and the lineage's reservation-sized chart declare their
    /// grains independently, and radiation may expose one fixed row per raw atom.
    #[allow(clippy::too_many_arguments)]
    pub fn founded(
        standing_axis: i64,
        own_axis: i64,
        cells: usize,
        own_cells: usize,
        byte_offset: usize,
        byte_count: usize,
        seed_previous: u32,
        seed_current: u32,
        worldline_base: u64,
        stroke_atoms: usize,
        drive: u32,
        radiation_stride: usize,
    ) -> LineageStroke {
        LineageStroke {
            standing_axis,
            own_axis,
            cells,
            own_cells,
            byte_offset,
            byte_count,
            seed_previous,
            seed_current,
            worldline_base,
            stroke_atoms,
            interior_installment: 0,
            drive,
            radiation_stride,
            completion_stride: 0,
        }
    }

    /// The REGISTER carriage species. `own_cells` is only the mounted storage aperture; the
    /// current's active axis is born at one and thereafter crosses in its mutable OWN header.
    /// Neither the aperture nor the light's extent chooses that axis.
    #[allow(clippy::too_many_arguments)]
    pub fn registered(
        standing_axis: i64,
        cells: usize,
        own_cells: usize,
        byte_offset: usize,
        byte_count: usize,
        seed_previous: u32,
        seed_current: u32,
        worldline_base: u64,
        stroke_atoms: usize,
        drive: u32,
        radiation_stride: usize,
    ) -> LineageStroke {
        LineageStroke {
            standing_axis,
            own_axis: 1,
            cells,
            own_cells,
            byte_offset,
            byte_count,
            seed_previous,
            seed_current,
            worldline_base,
            stroke_atoms,
            interior_installment: 0,
            drive,
            radiation_stride,
            completion_stride: 0,
        }
    }

    /// Declare one substrate-derived count of interior continuation moves. Zero is the
    /// uninterrupted comparison gauge; a positive installment suspends only between exact
    /// afferent/efferent/unwind phases and resumes unconditionally before another raw difference.
    pub const fn with_interior_installment(mut self, moves: usize) -> LineageStroke {
        self.interior_installment = moves;
        self
    }

    /// Expose a lineage-owned completion aperture for this invocation. Every exact row-sized span
    /// is formed; carriage fills it in worldline order, yields only when the span is full, and
    /// resumes the carried continuation unconditionally. The span is substrate reservation, never
    /// a cap on construction. Every other stride leaves the completion face absent.
    pub const fn with_completion_stride(mut self, words: usize) -> LineageStroke {
        self.completion_stride = words;
        self
    }
}

/// The boundary face of one completed hardware stroke. Counts remain instruments and are
/// published by the substrate shell; they never return as a body input.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StrokeResult {
    pub cursor: u64,
    pub terms: TermCounts,
}

/// The REGISTER's boundary face. A recast request is a live, frozen construction: the old OWN row
/// and every ordinary caller face remain committed, while the 12-word pending cause crosses in the
/// carrier. The boundary supplies exactly the requested next digit and relaunches the same stroke.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum RegisterStrokeStatus {
    Complete,
    /// The substrate installment ended at an exact carried boundary before the true light end.
    /// The mounted OWN/carrier rows remain the same species and must be relaunched unchanged.
    Continue,
    NeedsOwnRecast {
        old_axis: u32,
        new_axis: u32,
    },
    /// The exact carrier continuation reached the first unmounted enclosure.  The boundary must
    /// enlarge the physical row and resume this same phase/depth/brick before admitting another
    /// event.  This is substrate pressure, not a dark Soma deed or a completed world refusal.
    NeedsCarrierRebase {
        required_depth: u64,
    },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegisterStrokeResult {
    pub cursor: u64,
    pub terms: TermCounts,
    pub status: RegisterStrokeStatus,
}

/// Validate one complete REGISTER OWN row at a boundary read. The reservation extent is
/// apparatus; the row's own header supplies the accepted axis and occupancy.
pub fn registered_own_row_is_canonical(words: &[u32], capacity_cells: usize) -> bool {
    register_chart::row_is_canonical(words, 0, capacity_cells)
}

/// Form one exact next-digit REGISTER row without mutating the old mounting. `fresh` must be all
/// zero and have precisely `header + (2A)^2·OWN_CELL_WORDS` words. The returned row is a transient
/// pending-digit posture and becomes an ordinary canonical row only when the frozen infall lands.
pub fn recast_registered_own_row(old: &[u32], fresh: &mut [u32]) -> Option<(u32, u32)> {
    register_chart::recast_exact(old, fresh)
}

pub fn registered_own_recast_words(new_axis: u32) -> Option<usize> {
    let cells = (new_axis as usize).checked_mul(new_axis as usize)?;
    let cell_words = cells.checked_mul(manifold::OWN_CELL_WORDS)?;
    manifold::OWN_REGISTER_WORDS.checked_add(cell_words)
}

/// Rebase one complete carrier row into a deeper all-zero reservation without changing any lived
/// construction.  Header, mounted enclosures, deferred siblings, continuation, and pending deed
/// retain their exact words; only their reservation-derived physical offsets move.  Newly exposed
/// enclosure/deferred rows remain zero.  `fresh` is a separate disposable boundary allocation so
/// failure can never partially alter `old`.
pub fn rebase_carrier_row(old: &[u32], fresh: &mut [u32]) -> Option<(usize, usize)> {
    if !manifold::carried_frame_is_canonical(old) || fresh.iter().any(|&word| word != 0) {
        return None;
    }
    let old_depth = manifold::carrier_row_depth(old.len());
    let new_depth = manifold::carrier_row_depth(fresh.len());
    if new_depth <= old_depth || manifold::carrier_row_words(new_depth) != fresh.len() {
        return None;
    }

    fresh[..manifold::CARRIER_HEADER_WORDS].copy_from_slice(&old[..manifold::CARRIER_HEADER_WORDS]);

    let old_enclosure_end = manifold::CARRIER_HEADER_WORDS
        .checked_add(old_depth.checked_mul(manifold::ENCLOSURE_WORDS)?)?;
    fresh[manifold::CARRIER_HEADER_WORDS..old_enclosure_end]
        .copy_from_slice(&old[manifold::CARRIER_HEADER_WORDS..old_enclosure_end]);

    let old_deferred = manifold::carrier_deferred_base(old_depth, 0);
    let new_deferred = manifold::carrier_deferred_base(new_depth, 0);
    let deferred_words = old_depth.checked_mul(manifold::CARRIER_DEFERRED_WORDS)?;
    fresh[new_deferred..new_deferred + deferred_words]
        .copy_from_slice(&old[old_deferred..old_deferred + deferred_words]);

    let old_continuation = manifold::carrier_continuation_base(old_depth);
    let new_continuation = manifold::carrier_continuation_base(new_depth);
    fresh[new_continuation..new_continuation + manifold::CARRIER_CONTINUATION_WORDS]
        .copy_from_slice(
            &old[old_continuation..old_continuation + manifold::CARRIER_CONTINUATION_WORDS],
        );

    let old_pending = manifold::carrier_pending_base(old_depth);
    let new_pending = manifold::carrier_pending_base(new_depth);
    fresh[new_pending..new_pending + manifold::CARRIER_PENDING_WORDS]
        .copy_from_slice(&old[old_pending..old_pending + manifold::CARRIER_PENDING_WORDS]);

    manifold::carried_frame_is_canonical(fresh).then_some((old_depth, new_depth))
}

/// Return the next physical depth required by an otherwise canonical carrier.  Only an afferent
/// continuation poised exactly at the mounted boundary has this posture.
pub fn required_carrier_rebase_depth(carrier: &[u32]) -> Option<u64> {
    if !manifold::carried_frame_is_canonical(carrier) {
        return None;
    }
    let reserved = manifold::carrier_row_depth(carrier.len());
    let continuation = manifold::carrier_continuation_base(reserved);
    let phase = carrier[continuation + manifold::CARRIER_CONTINUATION_PHASE];
    let live_depth = carrier[continuation + manifold::CARRIER_CONTINUATION_DEPTH_LO] as u64
        | ((carrier[continuation + manifold::CARRIER_CONTINUATION_DEPTH_HI] as u64) << 32);
    (manifold::continuation_is_afferent(phase) && live_depth == reserved as u64)
        .then(|| live_depth.checked_add(1))?
}

#[inline(always)]
fn no_node() -> Node {
    Node {
        well: num::Cog::lit(0),
        place: place::origin(),
        len: 0,
    }
}

/// The radiation aperture is a compile-time carriage species. Dense scope instantiates the
/// zero-sized face and therefore carries no backing slice or dormant store path; founded scope
/// instantiates the formed face, whose every word still crosses through `WordSeam`.
trait RadiationTarget<S: WordSeam> {
    type Backing: ?Sized;

    fn set_atom(state: &mut RadiationState, atom: usize);
    fn fold(backing: &mut Self::Backing, state: &RadiationState);
    fn path(
        backing: &mut Self::Backing,
        state: &RadiationState,
        grip: u32,
        form: RegionalForm,
        meeting: Face,
        cut: bool,
    );
    fn brick(backing: &mut Self::Backing, state: &RadiationState, brick: Node);
}

struct NoRadiation;

impl<S: WordSeam> RadiationTarget<S> for NoRadiation {
    type Backing = ();

    #[inline(always)]
    fn set_atom(_state: &mut RadiationState, _atom: usize) {}

    #[inline(always)]
    fn fold(_backing: &mut (), _state: &RadiationState) {}

    #[inline(always)]
    fn path(
        _backing: &mut (),
        _state: &RadiationState,
        _grip: u32,
        _form: RegionalForm,
        _meeting: Face,
        _cut: bool,
    ) {
    }

    #[inline(always)]
    fn brick(_backing: &mut (), _state: &RadiationState, _brick: Node) {}
}

#[derive(Clone, Copy)]
struct RadiationState {
    span: ValidatedSpan,
    formed: bool,
    at: usize,
}

struct WordRadiation;

impl WordRadiation {
    #[inline(always)]
    fn read<S: WordSeam>(words: &[u32], state: &RadiationState, local: usize) -> u32 {
        unsafe { S::read_u32_unchecked(words, state.span.absolute(local)) }
    }

    #[inline(always)]
    fn store<S: WordSeam>(words: &mut [u32], state: &RadiationState, local: usize, value: u32) {
        unsafe { S::store_u32_unchecked(words, state.span.absolute(local), value) }
    }
}

impl<S: WordSeam> RadiationTarget<S> for WordRadiation {
    type Backing = [u32];

    #[inline(always)]
    fn set_atom(state: &mut RadiationState, atom: usize) {
        if state.formed {
            state.at = atom * manifold::RADIATION_WORDS;
        }
    }

    #[inline(never)]
    fn fold(words: &mut [u32], state: &RadiationState) {
        if !state.formed {
            return;
        }
        let at = state.at + manifold::RADIATION_FLAGS;
        Self::store::<S>(
            words,
            state,
            at,
            Self::read::<S>(words, state, at) | manifold::RADIATION_FOLD,
        );
    }

    #[inline(never)]
    fn path(
        words: &mut [u32],
        state: &RadiationState,
        grip: u32,
        form: RegionalForm,
        meeting: Face,
        cut: bool,
    ) {
        if !state.formed {
            return;
        }
        let at = state.at;
        let mut flags = Self::read::<S>(words, state, at + manifold::RADIATION_FLAGS)
            | manifold::RADIATION_STEP;
        if cut {
            flags |= manifold::RADIATION_CUT;
        }
        Self::store::<S>(words, state, at + manifold::RADIATION_FLAGS, flags);
        Self::store::<S>(words, state, at + manifold::RADIATION_GRIP, grip);
        let mut word = 0usize;
        while word < FORM_WORDS {
            Self::store::<S>(
                words,
                state,
                at + manifold::RADIATION_FORM + word,
                form.packed_word(word),
            );
            word += 1;
        }
        word = 0;
        while word < manifold::COG_WORDS {
            Self::store::<S>(
                words,
                state,
                at + manifold::RADIATION_ROTOR + word,
                manifold::cog_packed_word(meeting.arrow.cross, word),
            );
            Self::store::<S>(
                words,
                state,
                at + manifold::RADIATION_ROTOR + manifold::COG_WORDS + word,
                manifold::cog_packed_word(meeting.arrow.aim, word),
            );
            word += 1;
        }
    }

    #[inline(never)]
    fn brick(words: &mut [u32], state: &RadiationState, brick: Node) {
        if !state.formed {
            return;
        }
        let at = state.at;
        let flags = Self::read::<S>(words, state, at + manifold::RADIATION_FLAGS)
            | manifold::RADIATION_BRICK_LIVE;
        Self::store::<S>(words, state, at + manifold::RADIATION_FLAGS, flags);
        let mut word = 0usize;
        while word < manifold::NODE_WORDS {
            Self::store::<S>(
                words,
                state,
                at + manifold::RADIATION_BRICK + word,
                manifold::node_packed_word(brick, word),
            );
            word += 1;
        }
    }
}

/// The complete-enclosure aperture is independent of the historical one-row-per-atom path face.
/// A formed invocation owns one contiguous row span and stops when the next completion fills its
/// last row. The carried continuation, not these output rows, is the state that resumes on the
/// next substrate invocation.
trait CompletionTarget<S: WordSeam> {
    type Backing: ?Sized;

    fn set_atom(state: &mut CompletionState, atom: usize);
    fn emit(
        backing: &mut Self::Backing,
        state: &mut CompletionState,
        kind: u32,
        grain: u64,
        grip: u32,
        form: RegionalForm,
        meeting: Face,
        brick: Node,
    );
    fn full(state: &CompletionState) -> bool;
    fn overflowed(state: &CompletionState) -> bool;
}

struct NoCompletion;

impl<S: WordSeam> CompletionTarget<S> for NoCompletion {
    type Backing = ();

    #[inline(always)]
    fn set_atom(_state: &mut CompletionState, _atom: usize) {}

    #[inline(always)]
    fn emit(
        _backing: &mut (),
        _state: &mut CompletionState,
        _kind: u32,
        _grain: u64,
        _grip: u32,
        _form: RegionalForm,
        _meeting: Face,
        _brick: Node,
    ) {
    }

    #[inline(always)]
    fn full(_state: &CompletionState) -> bool {
        false
    }

    #[inline(always)]
    fn overflowed(_state: &CompletionState) -> bool {
        false
    }
}

#[derive(Clone, Copy)]
struct CompletionState {
    span: ValidatedSpan,
    formed: bool,
    full: bool,
    overflowed: bool,
    atom: usize,
    rows: usize,
    next: usize,
}

struct WordCompletion;

impl WordCompletion {
    #[inline(always)]
    fn store<S: WordSeam>(words: &mut [u32], state: &CompletionState, local: usize, value: u32) {
        let row = state.next * manifold::COMPLETION_WORDS;
        unsafe { S::store_u32_unchecked(words, state.span.absolute(row + local), value) }
    }
}

impl<S: WordSeam> CompletionTarget<S> for WordCompletion {
    type Backing = [u32];

    #[inline(always)]
    fn set_atom(state: &mut CompletionState, atom: usize) {
        state.atom = atom;
    }

    #[inline(never)]
    fn emit(
        words: &mut [u32],
        state: &mut CompletionState,
        kind: u32,
        grain: u64,
        grip: u32,
        form: RegionalForm,
        meeting: Face,
        brick: Node,
    ) {
        if !state.formed {
            return;
        }
        if state.next >= state.rows {
            state.overflowed = true;
            return;
        }
        Self::store::<S>(words, state, manifold::COMPLETION_KIND, kind);
        Self::store::<S>(
            words,
            state,
            manifold::COMPLETION_EVENT_LO,
            state.atom as u32,
        );
        Self::store::<S>(
            words,
            state,
            manifold::COMPLETION_EVENT_HI,
            ((state.atom as u64) >> 32) as u32,
        );
        Self::store::<S>(words, state, manifold::COMPLETION_GRAIN_LO, grain as u32);
        Self::store::<S>(
            words,
            state,
            manifold::COMPLETION_GRAIN_HI,
            (grain >> 32) as u32,
        );
        Self::store::<S>(words, state, manifold::COMPLETION_GRIP, grip);
        let mut word = 0usize;
        while word < FORM_WORDS {
            Self::store::<S>(
                words,
                state,
                manifold::COMPLETION_FORM + word,
                form.packed_word(word),
            );
            word += 1;
        }
        word = 0;
        while word < manifold::COG_WORDS {
            Self::store::<S>(
                words,
                state,
                manifold::COMPLETION_ROTOR + word,
                manifold::cog_packed_word(meeting.arrow.cross, word),
            );
            Self::store::<S>(
                words,
                state,
                manifold::COMPLETION_ROTOR + manifold::COG_WORDS + word,
                manifold::cog_packed_word(meeting.arrow.aim, word),
            );
            word += 1;
        }
        word = 0;
        while word < manifold::NODE_WORDS {
            Self::store::<S>(
                words,
                state,
                manifold::COMPLETION_BRICK + word,
                manifold::node_packed_word(brick, word),
            );
            word += 1;
        }
        state.next += 1;
        state.full = state.next == state.rows;
    }

    #[inline(always)]
    fn full(state: &CompletionState) -> bool {
        state.full
    }

    #[inline(always)]
    fn overflowed(state: &CompletionState) -> bool {
        state.overflowed
    }
}

/// One invocation's first-person body over already-carved mutable ranges.
struct FeltLineage<S: WordSeam, const FOUNDED: bool, const REGISTERED: bool> {
    cells: usize,
    own_cells: usize,
    depth: usize,
    standing_axis: i64,
    own_axis: i64,
    frame: place::Place,
    channel: channel::LineageChannel,
    dark_pending: u64,
    sub_stance: Node,
    sub_fly: Face,
    sub_fly_live: bool,
    continuation_phase: u32,
    continuation_depth: usize,
    continuation_brick: Node,
    pending_control: u32,
    pending_form: RegionalForm,
    register_face: register_chart::RegisterFace,
    recast_old_axis: u32,
    recast_new_axis: u32,
    invalid: bool,
    own_cell_offset: usize,
    own_base: usize,
    carrier_base: usize,
    terms: TermCounts,
    seam: PhantomData<S>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
enum DepositState {
    Accepted,
    NeedsOwnRecast { old_axis: u32, new_axis: u32 },
    Rejected,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
enum CrossState {
    Absent,
    Accepted,
    NeedsOwnRecast,
    Rejected,
}

impl<S: WordSeam, const FOUNDED: bool, const REGISTERED: bool> FeltLineage<S, FOUNDED, REGISTERED> {
    #[inline(always)]
    fn read(words: &[u32], at: usize) -> u32 {
        debug_assert!(at < words.len());
        unsafe { S::read_u32_unchecked(words, at) }
    }

    #[inline(always)]
    fn store(words: &mut [u32], at: usize, value: u32) {
        debug_assert!(at < words.len());
        unsafe { S::store_u32_unchecked(words, at, value) }
    }

    #[inline(always)]
    fn unpack_form(words: &[u32], at: usize) -> RegionalForm {
        unsafe { RegionalForm::unpack_unchecked_with::<S>(words, at) }
    }

    #[inline(always)]
    fn unpack_node(words: &[u32], at: usize) -> Node {
        unsafe { manifold::unpack_node_unchecked_with::<S>(words, at) }
    }

    #[inline(always)]
    fn unpack_face(words: &[u32], at: usize) -> Face {
        unsafe { manifold::unpack_face_unchecked_with::<S>(words, at) }
    }

    #[inline(always)]
    fn carrier_word(&self, carriers: &[u32], at: usize) -> u32 {
        Self::read(carriers, self.carrier_base + at)
    }

    #[inline(always)]
    fn store_carrier_word(&mut self, carriers: &mut [u32], at: usize, word: u32) {
        Self::store(carriers, self.carrier_base + at, word);
    }

    #[inline(always)]
    fn carrier_at(&self, at: usize) -> usize {
        self.carrier_base + at
    }

    #[inline(always)]
    fn own_at(&self, at: usize) -> usize {
        self.own_base + self.own_cell_offset + at
    }

    #[inline(always)]
    fn store_node(&mut self, carriers: &mut [u32], at: usize, node: Node) {
        let mut word = 0usize;
        while word < manifold::NODE_WORDS {
            self.store_carrier_word(carriers, at + word, manifold::node_packed_word(node, word));
            word += 1;
        }
    }

    #[inline(always)]
    fn clear_node(&mut self, carriers: &mut [u32], at: usize) {
        let mut word = 0usize;
        while word < manifold::NODE_WORDS {
            self.store_carrier_word(carriers, at + word, 0);
            word += 1;
        }
    }

    #[inline(always)]
    fn store_face(&mut self, carriers: &mut [u32], at: usize, face: Face) {
        let mut word = 0usize;
        while word < manifold::FACE_WORDS {
            self.store_carrier_word(carriers, at + word, manifold::face_packed_word(face, word));
            word += 1;
        }
    }

    #[inline(always)]
    fn clear_face(&mut self, carriers: &mut [u32], at: usize) {
        let mut word = 0usize;
        while word < manifold::FACE_WORDS {
            self.store_carrier_word(carriers, at + word, 0);
            word += 1;
        }
    }

    /// A completed enclosure has already handed its composite to the next grain. Its lower
    /// co-present arrivals no longer factor independently into the continuing construction, so
    /// the fixed REGISTER projection must release them before admitting the triggering successor.
    #[inline(never)]
    fn release_co_present(&mut self, carriers: &mut [u32], base: usize) {
        let mut slot = 0usize;
        while slot < register::REGISTER as usize {
            self.clear_node(
                carriers,
                base + manifold::ENCLOSURE_REGISTER + slot * manifold::NODE_WORDS,
            );
            slot += 1;
        }
        self.store_carrier_word(carriers, base + manifold::ENCLOSURE_HEAD, 0);
        self.store_carrier_word(carriers, base + manifold::ENCLOSURE_LIVE, 0);
    }

    #[inline(always)]
    fn store_enclosure_state(
        &mut self,
        carriers: &mut [u32],
        base: usize,
        stance: Node,
        fly: Face,
        fly_live: bool,
    ) {
        self.store_node(carriers, base + manifold::ENCLOSURE_STANCE, stance);
        if fly_live {
            self.store_face(carriers, base + manifold::ENCLOSURE_FLY, fly);
        } else {
            self.clear_face(carriers, base + manifold::ENCLOSURE_FLY);
        }
        self.store_carrier_word(
            carriers,
            base + manifold::ENCLOSURE_FLY_LIVE,
            fly_live as u32,
        );
    }

    #[inline(never)]
    fn cone_at(&self, standing: &[u32], owns: &[u32], position: place::Place) -> RegionalForm {
        let standing_grip = place::ground(position, self.standing_axis) as usize;
        if standing_grip >= self.cells {
            return RegionalForm::UNBORN;
        }
        // `cells × FORM_WORDS` was proven before mutation, so this product and its row end form.
        let standing_at = standing_grip * FORM_WORDS;
        if standing_at + FORM_WORDS > standing.len() {
            return RegionalForm::UNBORN;
        }
        let standing_form = Self::unpack_form(standing, standing_at);
        let own_grip = place::ground(position, self.own_axis) as usize;
        if own_grip >= self.own_cells {
            return standing_form;
        }
        let own_form = if FOUNDED {
            let own_at = own_grip * manifold::OWN_CELL_WORDS;
            if Self::read(owns, self.own_at(own_at + manifold::OWN_CELL_LIVE)) != 0 {
                Self::unpack_form(owns, self.own_at(own_at + manifold::OWN_CELL_FORM))
            } else {
                RegionalForm::UNBORN
            }
        } else {
            let own_at = own_grip * FORM_WORDS;
            Self::unpack_form(owns, self.own_at(own_at))
        };
        standing_form.join(own_form)
    }

    #[inline(never)]
    fn deposit_at(
        &mut self,
        owns: &mut [u32],
        position: place::Place,
        term: medium::FeltTerm,
    ) -> DepositState {
        if REGISTERED {
            let deposited = register_chart::deposit::<S>(
                owns,
                self.own_base + self.own_cell_offset,
                self.own_cells,
                &mut self.register_face,
                position,
                term,
            );
            self.own_axis = self.register_face.axis as i64;
            return match deposited {
                register_chart::DepositResult::Accepted => DepositState::Accepted,
                register_chart::DepositResult::NeedsOwnRecast { old_axis, new_axis } => {
                    DepositState::NeedsOwnRecast { old_axis, new_axis }
                }
                register_chart::DepositResult::Invalid => DepositState::Rejected,
            };
        }
        let grip = place::ground(position, self.own_axis) as usize;
        if grip >= self.own_cells {
            return DepositState::Rejected;
        }
        let (at, form_at) = if FOUNDED {
            let at = grip * manifold::OWN_CELL_WORDS;
            if Self::read(owns, self.own_at(at + manifold::OWN_CELL_LIVE)) == 0 {
                let mut word = 0usize;
                while word < manifold::COG_WORDS {
                    Self::store(
                        owns,
                        self.own_at(at + manifold::OWN_CELL_POSITION + word),
                        manifold::cog_packed_word(position.0, word),
                    );
                    Self::store(
                        owns,
                        self.own_at(at + manifold::OWN_CELL_POSITION + manifold::COG_WORDS + word),
                        manifold::cog_packed_word(position.1, word),
                    );
                    word += 1;
                }
            }
            (at, at + manifold::OWN_CELL_FORM)
        } else {
            let at = grip * FORM_WORDS;
            (at, at)
        };
        let form = Self::unpack_form(owns, self.own_at(form_at)).deposit(term);
        let mut word = 0usize;
        while word < FORM_WORDS {
            Self::store(owns, self.own_at(form_at + word), form.packed_word(word));
            word += 1;
        }
        if FOUNDED {
            Self::store(owns, self.own_at(at + manifold::OWN_CELL_LIVE), 1);
        }
        DepositState::Accepted
    }

    #[inline(never)]
    fn fold_channel(&mut self, aim: num::Cog, cross: num::Cog, found_this: bool, found_that: bool) {
        self.channel = self
            .channel
            .fold_formed_hand_or_self(aim, cross, found_this, found_that);
    }

    #[inline]
    fn pending_kind(&self) -> u32 {
        manifold::pending_kind(self.pending_control)
    }

    #[inline(never)]
    fn suspend_pending(
        &mut self,
        kind: u32,
        next_contact_exclusive: usize,
        form: RegionalForm,
        old_axis: u32,
        new_axis: u32,
    ) {
        self.pending_control = manifold::pending_control(kind, next_contact_exclusive as u32);
        self.pending_form = form;
        self.recast_old_axis = old_axis;
        self.recast_new_axis = new_axis;
    }

    #[inline]
    fn clear_pending(&mut self) {
        self.pending_control = 0;
        self.pending_form = RegionalForm::UNBORN;
    }

    #[inline]
    fn accepted_term(&mut self, winding: channel::WindingQuantum) {
        match winding {
            channel::WindingQuantum::None => self.terms.ride += 1,
            channel::WindingQuantum::ThisWay => self.terms.found_this += 1,
            channel::WindingQuantum::ThatWay => self.terms.found_that += 1,
        }
    }

    /// Reconstruct the exact pending deposit from committed caller state without writing any body
    /// face. This is the checked pre-mutation gate: a kind cannot fall through to a no-term branch,
    /// and a forged checkpoint cannot make resume skip or replay a co-present contact.
    #[inline(never)]
    fn pending_position_if_formed(
        &self,
        carriers: &[u32],
        bytes: &[u32],
        stroke: LineageStroke,
        atom: usize,
    ) -> Option<place::Place> {
        let kind = self.pending_kind();
        let pending = manifold::carrier_pending_base(self.depth);
        let form_is_zero = {
            let mut word = 0usize;
            let mut zero = true;
            while word < FORM_WORDS {
                zero &= self
                    .carrier_word(carriers, pending + manifold::CARRIER_PENDING_FORM + word)
                    == 0;
                word += 1;
            }
            zero
        };
        if kind == manifold::PENDING_DARK_BEFORE || kind == manifold::PENDING_DARK_TERMINAL {
            if !form_is_zero
                || self.dark_pending == 0
                || self.continuation_phase != manifold::CONTINUATION_NONE
            {
                return None;
            }
            if kind == manifold::PENDING_DARK_BEFORE {
                if atom == 0 || atom >= stroke.byte_count {
                    return None;
                }
                let previous = packed_byte::<S>(bytes, stroke.byte_offset + atom - 1);
                let current = packed_byte::<S>(bytes, stroke.byte_offset + atom);
                if boundary::difference_word(current, previous).mag == 0 {
                    return None;
                }
            }
            let next = self.channel.fold_formed_hand_or_self(
                num::Cog::lit(1),
                num::Cog::lit(0),
                false,
                false,
            );
            return Some(next.frame().anchor);
        }

        if kind == manifold::PENDING_SUB {
            if self.continuation_phase != manifold::CONTINUATION_NONE
                || self.continuation_depth != 0
                || self.continuation_brick.len != 0
                || atom == 0
                || atom >= stroke.byte_count
            {
                return None;
            }
            let previous = packed_byte::<S>(bytes, stroke.byte_offset + atom - 1);
            let current = packed_byte::<S>(bytes, stroke.byte_offset + atom);
            let difference = boundary::difference_word(current, previous);
            if difference.mag == 0 || self.sub_stance.len == 0 || !self.sub_fly_live {
                return None;
            }
            let node = manifold::atom_node(difference);
            let meeting = manifold::face(node.place, self.sub_stance.place, self.frame);
            let met = self.pending_form.drag(meeting);
            if met.arrow.at_horizon() || !met.rotor_formed() || !self.sub_fly.rotor_formed() {
                return None;
            }
            return Some(manifold::cast_position(
                met.chi_against_formed(&self.sub_fly),
            ));
        }

        if kind == manifold::PENDING_ENCLOSURE_CO_PRESENT
            || kind == manifold::PENDING_ENCLOSURE_TERMINAL
        {
            let depth = if self.continuation_phase == manifold::CONTINUATION_WORD_PERCEIVE {
                if self.continuation_depth != 0 {
                    return None;
                }
                0
            } else if manifold::continuation_is_afferent(self.continuation_phase)
                && self.continuation_depth > 0
                && self.continuation_depth < self.depth
            {
                self.continuation_depth
            } else {
                return None;
            };
            if self.continuation_brick.len == 0 {
                return None;
            }
            let base = manifold::carrier_enclosure_base(depth);
            let head = self.carrier_word(carriers, base + manifold::ENCLOSURE_HEAD) as usize;
            let live = self.carrier_word(carriers, base + manifold::ENCLOSURE_LIVE) as usize;
            let fly = Self::unpack_face(carriers, self.carrier_at(base + manifold::ENCLOSURE_FLY));
            let fly_live = self.carrier_word(carriers, base + manifold::ENCLOSURE_FLY_LIVE) != 0;
            if !fly_live || !fly.rotor_formed() || live > register::REGISTER as usize {
                return None;
            }
            if kind == manifold::PENDING_ENCLOSURE_CO_PRESENT {
                if !form_is_zero {
                    return None;
                }
                let next = manifold::pending_next_contact(self.pending_control) as usize;
                if next == 0 || next > live {
                    return None;
                }
                let i = next - 1;
                let index =
                    (head + register::REGISTER as usize - live + i) % register::REGISTER as usize;
                let co_present = Self::unpack_node(
                    carriers,
                    self.carrier_at(
                        base + manifold::ENCLOSURE_REGISTER + index * manifold::NODE_WORDS,
                    ),
                );
                if co_present.len == 0 {
                    return None;
                }
                let meeting =
                    manifold::face(co_present.place, self.continuation_brick.place, self.frame);
                if !meeting.rotor_formed() {
                    return None;
                }
                return Some(manifold::cast_position(meeting.chi_against_formed(&fly)));
            }

            if manifold::pending_next_contact(self.pending_control) != 0 {
                return None;
            }
            let stance =
                Self::unpack_node(carriers, self.carrier_at(base + manifold::ENCLOSURE_STANCE));
            if stance.len == 0 {
                return None;
            }
            let landing = manifold::face(self.continuation_brick.place, stance.place, self.frame);
            if !landing.rotor_formed() {
                return None;
            }
            let met = self.pending_form.drag(landing);
            if met.arrow.at_horizon() || !met.rotor_formed() {
                return None;
            }
            return Some(manifold::cast_position(met.chi_against_formed(&fly)));
        }

        if kind == manifold::PENDING_PATH {
            let depth = if self.continuation_phase == manifold::CONTINUATION_WORD_PATH {
                if self.continuation_depth != 0 {
                    return None;
                }
                0
            } else if manifold::continuation_is_efferent(self.continuation_phase)
                && self.continuation_depth > 0
                && self.continuation_depth < self.depth
            {
                self.continuation_depth
            } else {
                return None;
            };
            let base = manifold::carrier_enclosure_base(depth);
            let stance =
                Self::unpack_node(carriers, self.carrier_at(base + manifold::ENCLOSURE_STANCE));
            let fly = Self::unpack_face(carriers, self.carrier_at(base + manifold::ENCLOSURE_FLY));
            if stance.len == 0
                || self.carrier_word(carriers, base + manifold::ENCLOSURE_FLY_LIVE) == 0
                || !fly.rotor_formed()
            {
                return None;
            }
            let aim = fly.arrow.aim;
            let cross = fly.arrow.cross;
            let re = stance.place.0.sub(self.frame.0);
            let im = stance.place.1.sub(self.frame.1);
            let next = (
                aim.mul(re).sub(cross.mul(im)).add(self.frame.0),
                cross.mul(re).add(aim.mul(im)).add(self.frame.1),
            );
            let meeting = manifold::face(next, stance.place, self.frame);
            if !meeting.rotor_formed() {
                return None;
            }
            let met = self.pending_form.drag(meeting);
            if met.arrow.at_horizon() || !met.rotor_formed() {
                return None;
            }
            return Some(manifold::cast_position(met.chi_against_formed(&fly)));
        }
        None
    }

    #[inline(always)]
    fn meeting_wound(met: &Face, fly: &Face) -> bool {
        met.rotor_formed() && fly.rotor_formed() && met.chi_against_formed(fly).wound()
    }

    /// Fold the whole meeting deed after the same horizon/flywheel reads as the host mouth. This
    /// scalar-guarded form avoids transporting an optional aggregate through a shader ABI.
    #[inline(never)]
    fn fold_meeting(&mut self, met: &Face, fly: &Face, fly_live: bool, wound: bool) {
        if !met.rotor_formed() {
            return;
        }
        let (found_this, found_that) = if fly_live && wound && fly.rotor_formed() {
            let chi = met.chi_against_formed(fly);
            if chi.other.turn & 2 == 0 {
                (true, false)
            } else {
                (false, true)
            }
        } else {
            (false, false)
        };
        self.fold_channel(met.arrow.aim, met.arrow.cross, found_this, found_that);
    }

    #[inline(never)]
    fn cross_deed(
        &mut self,
        owns: &mut [u32],
        met: &Face,
        fly: &Face,
        fly_live: bool,
        wound: bool,
        pending_kind: u32,
        next_contact_exclusive: usize,
        pending_form: RegionalForm,
    ) -> CrossState {
        if !fly_live || !met.rotor_formed() || !fly.rotor_formed() {
            return CrossState::Absent;
        }
        let chi = met.chi_against_formed(fly);
        self.cross_chi_deed(
            owns,
            chi,
            wound,
            pending_kind,
            next_contact_exclusive,
            pending_form,
        )
    }

    /// Commit one already-formed fourth contact. Cooperative substrates may form several `Chi`
    /// faces together, but this verb remains on the carried chronological deed.
    #[inline(never)]
    fn cross_chi_deed(
        &mut self,
        owns: &mut [u32],
        chi: soul::Chi,
        wound: bool,
        pending_kind: u32,
        next_contact_exclusive: usize,
        pending_form: RegionalForm,
    ) -> CrossState {
        let winding = if wound {
            if chi.other.turn & 2 == 0 {
                channel::WindingQuantum::ThisWay
            } else {
                channel::WindingQuantum::ThatWay
            }
        } else {
            channel::WindingQuantum::None
        };
        match self.deposit_at(
            owns,
            manifold::cast_position(chi),
            medium::FeltTerm { chi, winding },
        ) {
            DepositState::Accepted => {
                self.accepted_term(winding);
                CrossState::Accepted
            }
            DepositState::NeedsOwnRecast { old_axis, new_axis } => {
                self.suspend_pending(
                    pending_kind,
                    next_contact_exclusive,
                    pending_form,
                    old_axis,
                    new_axis,
                );
                CrossState::NeedsOwnRecast
            }
            DepositState::Rejected => {
                self.invalid = true;
                CrossState::Rejected
            }
        }
    }

    /// One completed static passage. This mirrors the standing PRESENTED shape without deciding
    /// it: one dark channel fold and one pure-Same term at this lineage's anchor.
    #[inline(never)]
    fn deposit_dark_tread(&mut self, owns: &mut [u32], pending_kind: u32) -> bool {
        if self.dark_pending == 0 {
            return true;
        }
        let next_channel =
            self.channel
                .fold_formed_hand_or_self(num::Cog::lit(1), num::Cog::lit(0), false, false);
        let norm = if self.sub_fly_live {
            let aim = self.sub_fly.arrow.aim;
            let cross = self.sub_fly.arrow.cross;
            aim.mul(aim).add(cross.mul(cross))
        } else {
            num::Cog::lit(1)
        };
        let same = norm.mul(num::Cog::lit(self.dark_pending as i64));
        match self.deposit_at(
            owns,
            next_channel.frame().anchor,
            medium::FeltTerm {
                chi: soul::Chi {
                    same,
                    other: num::Cog::lit(0),
                },
                winding: channel::WindingQuantum::None,
            },
        ) {
            DepositState::Accepted => {
                self.channel = next_channel;
                self.terms.dark += 1;
                self.dark_pending = 0;
                self.clear_pending();
                true
            }
            DepositState::NeedsOwnRecast { old_axis, new_axis } => {
                self.suspend_pending(pending_kind, 0, RegionalForm::UNBORN, old_axis, new_axis);
                false
            }
            DepositState::Rejected => {
                self.invalid = true;
                false
            }
        }
    }

    /// One enclosure's afferent arrival. Its returned brick is the only upward face; all relation,
    /// K-fold, precession, and OWN deposits occur before the enclosure is stored back.
    #[inline(never)]
    fn perceive_grain<C: CompletionTarget<S>, T: RegisterContactSurface<S>>(
        &mut self,
        standing: &[u32],
        owns: &mut [u32],
        carriers: &mut [u32],
        completion: &mut C::Backing,
        completion_state: &mut CompletionState,
        contact_surface: &mut T,
        depth: usize,
        node: Node,
    ) -> Node {
        if depth >= self.depth {
            return no_node();
        }
        let base = manifold::carrier_enclosure_base(depth);
        let mut head = self.carrier_word(carriers, base + manifold::ENCLOSURE_HEAD) as usize
            % register::REGISTER as usize;
        let mut live = (self.carrier_word(carriers, base + manifold::ENCLOSURE_LIVE) as usize)
            .min(register::REGISTER as usize);
        let mut stance =
            Self::unpack_node(carriers, self.carrier_at(base + manifold::ENCLOSURE_STANCE));
        let mut fly = Self::unpack_face(carriers, self.carrier_at(base + manifold::ENCLOSURE_FLY));
        let mut fly_live = self.carrier_word(carriers, base + manifold::ENCLOSURE_FLY_LIVE) != 0;
        let landing = manifold::face(node.place, stance.place, self.frame);

        let pending_kind = self.pending_kind();
        let pending_next = manifold::pending_next_contact(self.pending_control) as usize;
        let snapshot = RegisterContactSnapshot {
            register_at: self.carrier_at(base + manifold::ENCLOSURE_REGISTER),
            head,
            live,
            node,
            frame: self.frame,
            fly,
            fly_live,
        };
        contact_surface.prepare(carriers, snapshot);
        let mut i = if pending_kind == manifold::PENDING_ENCLOSURE_CO_PRESENT {
            if pending_next == 0 {
                self.invalid = true;
                return no_node();
            }
            pending_next - 1
        } else if pending_kind == manifold::PENDING_ENCLOSURE_TERMINAL {
            live
        } else {
            0
        };
        while i < live {
            let index =
                (head + register::REGISTER as usize - live + i) % register::REGISTER as usize;
            let co_present = Self::unpack_node(
                carriers,
                self.carrier_at(base + manifold::ENCLOSURE_REGISTER + index * manifold::NODE_WORDS),
            );
            if co_present.len != 0 {
                let mut same = num::Cog::ZERO;
                let mut other = num::Cog::ZERO;
                let crossing =
                    if contact_surface.select(carriers, snapshot, i, &mut same, &mut other) {
                        let chi = soul::Chi { same, other };
                        self.cross_chi_deed(
                            owns,
                            chi,
                            false,
                            manifold::PENDING_ENCLOSURE_CO_PRESENT,
                            i + 1,
                            RegionalForm::UNBORN,
                        )
                    } else {
                        CrossState::Absent
                    };
                if crossing == CrossState::NeedsOwnRecast || crossing == CrossState::Rejected {
                    return no_node();
                }
                if pending_kind == manifold::PENDING_ENCLOSURE_CO_PRESENT && i + 1 == pending_next {
                    if crossing != CrossState::Accepted {
                        self.invalid = true;
                        return no_node();
                    }
                    self.clear_pending();
                }
            }
            i += 1;
        }

        let completion_live =
            stance.len != 0 && fly_live && landing.rotor_formed() && fly.rotor_formed();
        let relation_position = if completion_live {
            manifold::cast_position(landing.chi_against_formed(&fly))
        } else {
            (num::Cog::ZERO, num::Cog::ZERO)
        };
        let relation_grip = if completion_live {
            place::ground(relation_position, self.standing_axis)
        } else {
            0
        };
        let relation_form = if pending_kind == manifold::PENDING_ENCLOSURE_TERMINAL {
            self.pending_form
        } else if completion_live {
            self.cone_at(standing, owns, relation_position)
        } else {
            RegionalForm::UNBORN
        };
        let met = relation_form.drag(landing);
        let dark = met.arrow.at_horizon();
        let from_pole = {
            let re = node.place.0.sub(self.frame.0);
            let im = node.place.1.sub(self.frame.1);
            re.mag == 0 && im.mag == 0
        };
        let wound = if dark {
            false
        } else if fly_live {
            FeltLineage::<S, FOUNDED, REGISTERED>::meeting_wound(&met, &fly)
        } else {
            met.founds()
        };
        let mut brick = no_node();
        if stance.len == 0 {
            self.fold_meeting(&met, &fly, fly_live, wound);
            if !from_pole {
                stance = node;
            }
        } else if dark {
            self.fold_meeting(&met, &fly, fly_live, wound);
            // the frame's horizon passes unread
        } else if wound {
            let old = stance;
            let (re, im) =
                manifold::rebase_pair(old.place.0.sub(self.frame.0), old.place.1.sub(self.frame.1));
            let enclosed = Node {
                well: old.well,
                place: (self.frame.0.add(re), self.frame.1.add(im)),
                len: old.len,
            };
            let crossing = self.cross_deed(
                owns,
                &met,
                &fly,
                fly_live,
                true,
                manifold::PENDING_ENCLOSURE_TERMINAL,
                0,
                relation_form,
            );
            if crossing == CrossState::NeedsOwnRecast || crossing == CrossState::Rejected {
                return no_node();
            }
            if crossing == CrossState::Absent
                && pending_kind == manifold::PENDING_ENCLOSURE_TERMINAL
            {
                self.invalid = true;
                return no_node();
            }
            if crossing == CrossState::Accepted {
                self.clear_pending();
            }
            self.fold_meeting(&met, &fly, fly_live, wound);
            brick = enclosed;
            C::emit(
                completion,
                completion_state,
                manifold::COMPLETION_AFFERENT,
                depth as u64 + 1,
                relation_grip,
                relation_form,
                met,
                enclosed,
            );
            stance = node;
            self.release_co_present(carriers, base);
            head = 0;
            live = 0;
            if fly_live {
                fly = relation_form.drag(fly);
            }
        } else {
            let (composition, _) = manifold::bond(stance, node, self.frame);
            let crossing = self.cross_deed(
                owns,
                &met,
                &fly,
                fly_live,
                false,
                manifold::PENDING_ENCLOSURE_TERMINAL,
                0,
                relation_form,
            );
            if crossing == CrossState::NeedsOwnRecast || crossing == CrossState::Rejected {
                return no_node();
            }
            if crossing == CrossState::Absent
                && pending_kind == manifold::PENDING_ENCLOSURE_TERMINAL
            {
                self.invalid = true;
                return no_node();
            }
            if crossing == CrossState::Accepted {
                self.clear_pending();
            }
            self.fold_meeting(&met, &fly, fly_live, wound);
            stance = composition;
            fly = met;
            fly_live = true;
        }

        self.store_node(
            carriers,
            base + manifold::ENCLOSURE_REGISTER + head * manifold::NODE_WORDS,
            node,
        );
        head = (head + 1) % register::REGISTER as usize;
        if live < register::REGISTER as usize {
            live += 1;
        }
        self.store_carrier_word(carriers, base + manifold::ENCLOSURE_HEAD, head as u32);
        self.store_carrier_word(carriers, base + manifold::ENCLOSURE_LIVE, live as u32);
        self.store_enclosure_state(carriers, base, stance, fly, fly_live);
        brick
    }

    /// One enclosure's efferent deed. A returned brick is the completed enclosure handed upward.
    #[inline(never)]
    fn path_grain<R: RadiationTarget<S>, C: CompletionTarget<S>>(
        &mut self,
        standing: &[u32],
        owns: &mut [u32],
        carriers: &mut [u32],
        radiation: &mut R::Backing,
        radiation_state: &mut RadiationState,
        completion: &mut C::Backing,
        completion_state: &mut CompletionState,
        depth: usize,
    ) -> Node {
        if depth >= self.depth {
            return no_node();
        }
        let base = manifold::carrier_enclosure_base(depth);
        let mut stance =
            Self::unpack_node(carriers, self.carrier_at(base + manifold::ENCLOSURE_STANCE));
        let mut fly = Self::unpack_face(carriers, self.carrier_at(base + manifold::ENCLOSURE_FLY));
        let fly_live = self.carrier_word(carriers, base + manifold::ENCLOSURE_FLY_LIVE) != 0;
        if stance.len == 0 || !fly_live {
            return no_node();
        }
        let aim = fly.arrow.aim;
        let cross = fly.arrow.cross;
        let re = stance.place.0.sub(self.frame.0);
        let im = stance.place.1.sub(self.frame.1);
        let next = (
            aim.mul(re).sub(cross.mul(im)).add(self.frame.0),
            cross.mul(re).add(aim.mul(im)).add(self.frame.1),
        );
        let meeting = manifold::face(next, stance.place, self.frame);
        let completion_live = meeting.rotor_formed() && fly.rotor_formed();
        let mut grip = 0u32;
        let mut relation_position = place::origin();
        if completion_live {
            relation_position = manifold::cast_position(meeting.chi_against_formed(&fly));
            grip = place::ground(relation_position, self.standing_axis);
        }
        let regional_form = if self.pending_kind() == manifold::PENDING_PATH {
            self.pending_form
        } else if completion_live {
            self.cone_at(standing, owns, relation_position)
        } else {
            RegionalForm::UNBORN
        };
        let met = regional_form.drag(meeting);
        let dark = met.arrow.at_horizon();
        let wound = if dark {
            false
        } else {
            FeltLineage::<S, FOUNDED, REGISTERED>::meeting_wound(&met, &fly)
        };
        if !dark && wound {
            let (re, im) =
                manifold::rebase_pair(next.0.sub(self.frame.0), next.1.sub(self.frame.1));
            let enclosed = Node {
                well: stance.well,
                place: (self.frame.0.add(re), self.frame.1.add(im)),
                len: stance.len,
            };
            let crossing = self.cross_deed(
                owns,
                &met,
                &fly,
                true,
                true,
                manifold::PENDING_PATH,
                0,
                regional_form,
            );
            if crossing == CrossState::NeedsOwnRecast || crossing == CrossState::Rejected {
                return no_node();
            }
            if crossing != CrossState::Accepted {
                self.invalid = true;
                return no_node();
            }
            self.clear_pending();
            if depth == 0 {
                R::path(radiation, radiation_state, grip, regional_form, met, true);
            }
            self.fold_meeting(&met, &fly, true, wound);
            fly = regional_form.drag(fly);
            let (aim, cross) = manifold::rebase_pair(fly.arrow.aim, fly.arrow.cross);
            fly.arrow.aim = aim;
            fly.arrow.cross = cross;
            stance = enclosed;
            self.release_co_present(carriers, base);
            self.store_enclosure_state(carriers, base, stance, fly, true);
            C::emit(
                completion,
                completion_state,
                manifold::COMPLETION_EFFERENT,
                depth as u64 + 1,
                grip,
                regional_form,
                met,
                enclosed,
            );
            if depth == 0 {
                R::brick(radiation, radiation_state, enclosed);
            }
            return enclosed;
        }
        if !dark {
            let crossing = self.cross_deed(
                owns,
                &met,
                &fly,
                true,
                false,
                manifold::PENDING_PATH,
                0,
                regional_form,
            );
            if crossing == CrossState::NeedsOwnRecast || crossing == CrossState::Rejected {
                return no_node();
            }
            if crossing != CrossState::Accepted {
                self.invalid = true;
                return no_node();
            }
            self.clear_pending();
            if depth == 0 {
                R::path(radiation, radiation_state, grip, regional_form, met, false);
            }
            self.fold_meeting(&met, &fly, true, wound);
            fly = met;
        } else {
            if depth == 0 {
                R::path(radiation, radiation_state, grip, regional_form, met, false);
            }
            self.fold_meeting(&met, &fly, true, wound);
        }
        stance = Node {
            well: stance.well,
            place: next,
            len: stance.len,
        };
        self.store_enclosure_state(carriers, base, stance, fly, true);
        no_node()
    }

    #[inline(always)]
    fn afferent_phase(phase: u32) -> u32 {
        if manifold::continuation_is_perceive(phase) {
            manifold::CONTINUATION_PERCEIVE_AFFERENT
        } else {
            manifold::CONTINUATION_PATH_AFFERENT
        }
    }

    #[inline(always)]
    fn efferent_phase(phase: u32) -> u32 {
        if manifold::continuation_is_perceive(phase) {
            manifold::CONTINUATION_PERCEIVE_EFFERENT
        } else {
            manifold::CONTINUATION_PATH_EFFERENT
        }
    }

    #[inline(always)]
    fn unwind_phase(phase: u32) -> u32 {
        if manifold::continuation_is_perceive(phase) {
            manifold::CONTINUATION_PERCEIVE_UNWIND
        } else {
            manifold::CONTINUATION_PATH_UNWIND
        }
    }

    #[inline(always)]
    fn clear_continuation(&mut self) {
        self.continuation_phase = manifold::CONTINUATION_NONE;
        self.continuation_depth = 0;
        self.continuation_brick = no_node();
    }

    #[inline(always)]
    fn begin_thickening(&mut self, phase: u32, brick: Node) {
        self.continuation_phase = phase;
        self.continuation_depth = 1;
        self.continuation_brick = brick;
    }

    #[inline(always)]
    fn required_carrier_depth(&self) -> Option<usize> {
        (manifold::continuation_is_afferent(self.continuation_phase)
            && self.continuation_depth >= self.depth)
            // `saturating_add(1)` explicit — the rust-gpu kernel has no saturating intrinsic
            // (`place.rs:52` is the same excision, same reason). `usize::MAX` is the only
            // spelling that stays correct across the seam: `usize` is 32-bit on
            // `spirv-unknown-vulkan1.2` and 64-bit on the host, and a literal would pin one.
            .then(|| {
                if self.continuation_depth == usize::MAX {
                    usize::MAX
                } else {
                    self.continuation_depth + 1
                }
            })
    }

    /// One exact move of the carrier-owned depth-first continuation. AFFERENT, EFFERENT, and
    /// UNWIND are separate phases so the substrate seam may land between them without repeating a
    /// deed. Deferred siblings remain in their reservation-derived carrier slots; no call-frame
    /// state belongs to the current after this move returns.
    #[inline(never)]
    fn continuation_move<
        R: RadiationTarget<S>,
        C: CompletionTarget<S>,
        T: RegisterContactSurface<S>,
    >(
        &mut self,
        standing: &[u32],
        owns: &mut [u32],
        carriers: &mut [u32],
        radiation: &mut R::Backing,
        radiation_state: &mut RadiationState,
        completion: &mut C::Backing,
        completion_state: &mut CompletionState,
        contact_surface: &mut T,
    ) {
        let phase = self.continuation_phase;
        if phase == manifold::CONTINUATION_WORD_PERCEIVE {
            let brick = self.perceive_grain::<C, T>(
                standing,
                owns,
                carriers,
                completion,
                completion_state,
                contact_surface,
                0,
                self.continuation_brick,
            );
            if self.pending_kind() != manifold::PENDING_NONE || self.invalid {
                return;
            }
            if brick.len != 0 {
                self.begin_thickening(manifold::CONTINUATION_PERCEIVE_AFFERENT, brick);
            } else {
                self.continuation_phase = manifold::CONTINUATION_WORD_PATH;
                self.continuation_depth = 0;
                self.continuation_brick = no_node();
            }
            return;
        }
        if manifold::continuation_is_afferent(phase) {
            if self.continuation_depth >= self.depth {
                // Preserve the exact live continuation.  The boundary will grow the physical
                // carrier row and resume this same brick before any later event can enter.
                return;
            }
            let crossed = self.perceive_grain::<C, T>(
                standing,
                owns,
                carriers,
                completion,
                completion_state,
                contact_surface,
                self.continuation_depth,
                self.continuation_brick,
            );
            if self.pending_kind() != manifold::PENDING_NONE || self.invalid {
                // A caused REGISTER carry freezes the afferent caller before its returned face
                // exists. Preserve the incoming brick: the pending contact re-enters this exact
                // call and reconstructs its deed from that brick after the row is re-based.
                return;
            }
            self.continuation_brick = crossed;
            self.continuation_phase = Self::efferent_phase(phase);
            return;
        }

        if manifold::continuation_is_efferent(phase) {
            let afferent = self.continuation_brick;
            let efferent = self.path_grain::<R, C>(
                standing,
                owns,
                carriers,
                radiation,
                radiation_state,
                completion,
                completion_state,
                self.continuation_depth,
            );
            if self.pending_kind() != manifold::PENDING_NONE || self.invalid {
                return;
            }
            if afferent.len != 0 {
                if efferent.len != 0 {
                    let at = manifold::carrier_deferred_base(self.depth, self.continuation_depth);
                    self.store_node(carriers, at, efferent);
                }
                self.continuation_brick = afferent;
                self.continuation_depth += 1;
                self.continuation_phase = Self::afferent_phase(phase);
                return;
            }
            if efferent.len != 0 {
                self.continuation_brick = efferent;
                self.continuation_depth += 1;
                self.continuation_phase = Self::afferent_phase(phase);
                return;
            }
            self.continuation_brick = no_node();
            self.continuation_phase = Self::unwind_phase(phase);
            return;
        }

        if manifold::continuation_is_unwind(phase) {
            if self.continuation_depth > 1 {
                let parent = self.continuation_depth - 1;
                let at = manifold::carrier_deferred_base(self.depth, parent);
                let sibling = Self::unpack_node(carriers, self.carrier_at(at));
                if sibling.len != 0 {
                    self.clear_node(carriers, at);
                    self.continuation_brick = sibling;
                    self.continuation_depth = parent + 1;
                    self.continuation_phase = Self::afferent_phase(phase);
                } else {
                    self.continuation_depth = parent;
                }
                return;
            }
            if manifold::continuation_is_perceive(phase) {
                self.continuation_phase = manifold::CONTINUATION_WORD_PATH;
                self.continuation_depth = 0;
                self.continuation_brick = no_node();
            } else {
                self.clear_continuation();
            }
            return;
        }

        if phase == manifold::CONTINUATION_WORD_PATH {
            let brick = self.path_grain::<R, C>(
                standing,
                owns,
                carriers,
                radiation,
                radiation_state,
                completion,
                completion_state,
                0,
            );
            if self.pending_kind() != manifold::PENDING_NONE || self.invalid {
                return;
            }
            if brick.len != 0 {
                self.begin_thickening(manifold::CONTINUATION_PATH_AFFERENT, brick);
            } else {
                self.clear_continuation();
            }
            return;
        }

        // Both safe and trusted mouths reject an unknown phase before mutation. Every transition
        // above writes one of the same exact phases, so this branch preserves rather than erases an
        // impossible transport if that internal contract ever drifts.
    }

    /// Continue the unfinished atom for at most the invocation's declared substrate installment.
    /// Zero is the uninterrupted comparison gauge. The count is not carried: only the traversal's
    /// exact phase is body state, and every later invocation resumes it unconditionally first.
    #[inline(never)]
    fn continue_atom<
        R: RadiationTarget<S>,
        C: CompletionTarget<S>,
        T: RegisterContactSurface<S>,
    >(
        &mut self,
        standing: &[u32],
        owns: &mut [u32],
        carriers: &mut [u32],
        radiation: &mut R::Backing,
        radiation_state: &mut RadiationState,
        completion: &mut C::Backing,
        completion_state: &mut CompletionState,
        contact_surface: &mut T,
        installment: usize,
        moved: &mut usize,
    ) -> bool {
        while self.pending_kind() == manifold::PENDING_NONE
            && !self.invalid
            && self.continuation_phase != manifold::CONTINUATION_NONE
            && self.required_carrier_depth().is_none()
            && !C::full(completion_state)
            && (installment == 0 || *moved < installment)
        {
            self.continuation_move::<R, C, T>(
                standing,
                owns,
                carriers,
                radiation,
                radiation_state,
                completion,
                completion_state,
                contact_surface,
            );
            *moved += 1;
        }
        self.pending_kind() == manifold::PENDING_NONE
            && !self.invalid
            && self.continuation_phase == manifold::CONTINUATION_NONE
    }

    #[inline(never)]
    fn perceive_node<R: RadiationTarget<S>, C: CompletionTarget<S>>(
        &mut self,
        standing: &[u32],
        owns: &mut [u32],
        carriers: &mut [u32],
        radiation: &mut R::Backing,
        radiation_state: &mut RadiationState,
        completion: &mut C::Backing,
        completion_state: &mut CompletionState,
        node: Node,
    ) {
        self.continuation_phase = manifold::CONTINUATION_WORD_PERCEIVE;
        self.continuation_depth = 0;
        self.continuation_brick = node;
        let _ = (
            standing,
            owns,
            carriers,
            radiation,
            radiation_state,
            completion,
            completion_state,
        );
    }

    /// One non-static atom through the sub-illicium and, when it folds, the whole upper circuit.
    #[inline(never)]
    fn live_difference<R: RadiationTarget<S>, C: CompletionTarget<S>>(
        &mut self,
        standing: &[u32],
        owns: &mut [u32],
        carriers: &mut [u32],
        radiation: &mut R::Backing,
        radiation_state: &mut RadiationState,
        completion: &mut C::Backing,
        completion_state: &mut CompletionState,
        difference: num::Cog,
        drive: u32,
    ) {
        if difference.mag == 0 {
            self.dark_pending = self.dark_pending.wrapping_add(drive as u64);
            return;
        }
        if !self.deposit_dark_tread(owns, manifold::PENDING_DARK_BEFORE) {
            return;
        }
        let node = manifold::atom_node(difference);
        let relation = manifold::face(node.place, self.sub_stance.place, self.frame);
        let completion_live = self.sub_stance.len != 0
            && self.sub_fly_live
            && relation.rotor_formed()
            && self.sub_fly.rotor_formed();
        let relation_position = if completion_live {
            manifold::cast_position(relation.chi_against_formed(&self.sub_fly))
        } else {
            (num::Cog::ZERO, num::Cog::ZERO)
        };
        let completion_grip = if completion_live {
            place::ground(relation_position, self.standing_axis)
        } else {
            0
        };
        let relation_form = if self.pending_kind() == manifold::PENDING_SUB {
            self.pending_form
        } else if completion_live {
            self.cone_at(standing, owns, relation_position)
        } else {
            RegionalForm::UNBORN
        };
        let met = relation_form.drag(relation);
        let dark = met.arrow.at_horizon();
        let from_pole = {
            let re = node.place.0.sub(self.frame.0);
            let im = node.place.1.sub(self.frame.1);
            re.mag == 0 && im.mag == 0
        };
        let wound = if dark {
            false
        } else if self.sub_fly_live {
            FeltLineage::<S, FOUNDED, REGISTERED>::meeting_wound(&met, &self.sub_fly)
        } else {
            met.founds()
        };
        let mut fold = no_node();
        if self.sub_stance.len == 0 {
            let held_sub_fly = self.sub_fly;
            self.fold_meeting(&met, &held_sub_fly, self.sub_fly_live, wound);
            if !from_pole {
                self.sub_stance = node;
            }
        } else if dark {
            let held_sub_fly = self.sub_fly;
            self.fold_meeting(&met, &held_sub_fly, self.sub_fly_live, wound);
            // the frame's horizon passes unread
        } else if wound {
            let old = self.sub_stance;
            let (re, im) =
                manifold::rebase_pair(old.place.0.sub(self.frame.0), old.place.1.sub(self.frame.1));
            let enclosed = Node {
                well: old.well,
                place: (self.frame.0.add(re), self.frame.1.add(im)),
                len: old.len,
            };
            let fly = self.sub_fly;
            let resuming = self.pending_kind() == manifold::PENDING_SUB;
            let crossing = self.cross_deed(
                owns,
                &met,
                &fly,
                self.sub_fly_live,
                true,
                manifold::PENDING_SUB,
                0,
                relation_form,
            );
            if crossing == CrossState::NeedsOwnRecast || crossing == CrossState::Rejected {
                return;
            }
            if crossing == CrossState::Absent && resuming {
                self.invalid = true;
                return;
            }
            if crossing == CrossState::Accepted {
                self.clear_pending();
            }
            self.fold_meeting(&met, &fly, self.sub_fly_live, wound);
            fold = enclosed;
            self.sub_stance = node;
            if self.sub_fly_live {
                self.sub_fly = relation_form.drag(self.sub_fly);
            }
        } else {
            let (composition, _) = manifold::bond(self.sub_stance, node, self.frame);
            let fly = self.sub_fly;
            let resuming = self.pending_kind() == manifold::PENDING_SUB;
            let crossing = self.cross_deed(
                owns,
                &met,
                &fly,
                self.sub_fly_live,
                false,
                manifold::PENDING_SUB,
                0,
                relation_form,
            );
            if crossing == CrossState::NeedsOwnRecast || crossing == CrossState::Rejected {
                return;
            }
            if crossing == CrossState::Absent && resuming {
                self.invalid = true;
                return;
            }
            if crossing == CrossState::Accepted {
                self.clear_pending();
            }
            self.fold_meeting(&met, &fly, self.sub_fly_live, wound);
            self.sub_stance = composition;
            self.sub_fly = met;
            self.sub_fly_live = true;
        }

        if fold.len != 0 {
            R::fold(radiation, radiation_state);
            C::emit(
                completion,
                completion_state,
                manifold::COMPLETION_ATOM_FOLD,
                0,
                completion_grip,
                relation_form,
                met,
                fold,
            );
            self.perceive_node::<R, C>(
                standing,
                owns,
                carriers,
                radiation,
                radiation_state,
                completion,
                completion_state,
                fold,
            );
        }
    }

    /// Store the complete first-person stand after a carriage stroke. A zero-lived organ has one
    /// all-zero boundary spelling.
    #[inline(never)]
    fn finish(&mut self, carriers: &mut [u32], cursor: u64) {
        self.store_carrier_word(carriers, manifold::CARRIER_CURSOR_LO, cursor as u32);
        self.store_carrier_word(carriers, manifold::CARRIER_CURSOR_HI, (cursor >> 32) as u32);
        self.store_carrier_word(
            carriers,
            manifold::CARRIER_DARK_LO,
            self.dark_pending as u32,
        );
        self.store_carrier_word(
            carriers,
            manifold::CARRIER_DARK_HI,
            (self.dark_pending >> 32) as u32,
        );
        let sub_stance_at = manifold::CARRIER_SUB_STANCE;
        if self.sub_stance.len == 0 {
            self.clear_node(carriers, sub_stance_at);
        } else {
            self.store_node(carriers, sub_stance_at, self.sub_stance);
        }
        let sub_fly_at = manifold::CARRIER_SUB_FLY;
        if self.sub_fly_live {
            self.store_face(carriers, sub_fly_at, self.sub_fly);
        } else {
            self.clear_face(carriers, sub_fly_at);
        }
        self.store_carrier_word(
            carriers,
            manifold::CARRIER_SUB_FLY_LIVE,
            self.sub_fly_live as u32,
        );
        let channel_at = manifold::CARRIER_CHANNEL;
        let mut word = 0usize;
        while word < channel::CHANNEL_WORDS {
            self.store_carrier_word(carriers, channel_at + word, self.channel.packed_word(word));
            word += 1;
        }
        let continuation = manifold::carrier_continuation_base(self.depth);
        self.store_carrier_word(
            carriers,
            continuation + manifold::CARRIER_CONTINUATION_PHASE,
            self.continuation_phase,
        );
        self.store_carrier_word(
            carriers,
            continuation + manifold::CARRIER_CONTINUATION_DEPTH_LO,
            self.continuation_depth as u64 as u32,
        );
        self.store_carrier_word(
            carriers,
            continuation + manifold::CARRIER_CONTINUATION_DEPTH_HI,
            ((self.continuation_depth as u64) >> 32) as u32,
        );
        if self.continuation_brick.len == 0 {
            self.clear_node(
                carriers,
                continuation + manifold::CARRIER_CONTINUATION_BRICK,
            );
        } else {
            self.store_node(
                carriers,
                continuation + manifold::CARRIER_CONTINUATION_BRICK,
                self.continuation_brick,
            );
        }
        let pending = manifold::carrier_pending_base(self.depth);
        self.store_carrier_word(
            carriers,
            pending + manifold::CARRIER_PENDING_CONTROL,
            self.pending_control,
        );
        word = 0;
        while word < FORM_WORDS {
            self.store_carrier_word(
                carriers,
                pending + manifold::CARRIER_PENDING_FORM + word,
                self.pending_form.packed_word(word),
            );
            word += 1;
        }
    }
}

#[inline(always)]
fn packed_byte<S: WordSeam>(bytes: &[u32], atom: usize) -> u32 {
    let word = unsafe { S::read_u32_unchecked(bytes, atom >> 2) };
    (word >> ((atom & 3) * 8)) & 0xff
}

#[derive(Clone, Copy)]
struct LayoutProof {
    own: ValidatedSpan,
    carrier: ValidatedSpan,
    radiation: ValidatedSpan,
    completion: ValidatedSpan,
    worldline_end: u64,
}

/// Form every extent before any body word can change. This function has scalar inputs only and is
/// deliberately kept outside the pointer-heavy stroke so rust-gpu does not structurally nest the
/// whole lineage law beneath each checked arithmetic branch.
#[allow(clippy::too_many_arguments)]
#[inline(never)]
fn prove_layout<const FOUNDED: bool, const REGISTERED: bool>(
    standing_len: usize,
    owns_len: usize,
    own_words: WordSpan,
    carriers_len: usize,
    carrier_words: WordSpan,
    bytes_len: usize,
    radiation_len: usize,
    radiation_words: WordSpan,
    radiates: bool,
    completion_len: usize,
    completion_words: WordSpan,
    completes: bool,
    stroke: LineageStroke,
) -> Option<LayoutProof> {
    let byte_capacity = checked_extent_mul(bytes_len, 4)?;
    let byte_end = checked_extent_add(stroke.byte_offset, stroke.byte_count)?;
    let standing_words = checked_extent_mul(stroke.cells, FORM_WORDS)?;
    let worldline_end = checked_worldline_add(stroke.worldline_base, stroke.byte_count as u64)?;
    let carrier_depth = manifold::carrier_row_depth(carrier_words.len);
    if stroke.cells == 0
        || stroke.standing_axis <= 0
        || stroke.own_axis <= 0
        || stroke.byte_count == 0
        || byte_end > byte_capacity
        || standing_words > standing_len
        || carrier_words.len < manifold::CARRIER_HEADER_WORDS
        || carrier_depth == 0
        || manifold::carrier_row_words(carrier_depth) != carrier_words.len
    {
        return None;
    }
    if FOUNDED && !REGISTERED && stroke.own_axis & (stroke.own_axis - 1) != 0 {
        return None;
    }
    let expected_own_words = if REGISTERED {
        checked_extent_mul(stroke.own_cells, manifold::OWN_CELL_WORDS)?
            .checked_add(manifold::OWN_REGISTER_WORDS)?
    } else if FOUNDED {
        checked_extent_mul(stroke.own_cells, manifold::OWN_CELL_WORDS)?
    } else {
        checked_extent_mul(stroke.own_cells, FORM_WORDS)?
    };
    let expected_radiation_words = if radiates {
        checked_extent_mul(stroke.byte_count, manifold::RADIATION_WORDS)?
    } else {
        0
    };
    let expected_completion_words = if completes {
        stroke.completion_stride
    } else {
        0
    };
    Some(LayoutProof {
        own: ValidatedSpan::form(owns_len, own_words, expected_own_words)?,
        carrier: ValidatedSpan::form(carriers_len, carrier_words, manifold::CARRIER_HEADER_WORDS)?,
        radiation: ValidatedSpan::form(radiation_len, radiation_words, expected_radiation_words)?,
        completion: ValidatedSpan::form(
            completion_len,
            completion_words,
            expected_completion_words,
        )?,
        worldline_end,
    })
}

/// Check the complete mutable and immutable body rows accepted by the safe host/reference mouth.
/// Device kernels enter the separately named trusted mouth after their mounting shell has supplied
/// producer-owned canonical buffers. This scan is therefore a boundary check, never an interior
/// carriage operation or a per-atom mechanism.
fn boundary_rows_are_canonical<const FOUNDED: bool, const REGISTERED: bool>(
    standing: &[u32],
    owns: &[u32],
    carriers: &[u32],
    layout: LayoutProof,
    stroke: LineageStroke,
) -> bool {
    let row = &carriers[layout.carrier.base..layout.carrier.base + layout.carrier.len];
    let cursor =
        row[manifold::CARRIER_CURSOR_LO] as u64 | ((row[manifold::CARRIER_CURSOR_HI] as u64) << 32);
    let carrier_formed = if cursor == 0 {
        row.iter().all(|word| *word == 0)
    } else {
        manifold::carried_frame_is_canonical(row)
    };
    if !carrier_formed {
        return false;
    }
    let pending_active =
        cursor != 0 && manifold::carrier_pending_kind(row) != manifold::PENDING_NONE;

    let mut cell = 0usize;
    while cell < stroke.cells {
        if RegionalForm::unpack_compact_checked(standing, cell * FORM_WORDS).is_err() {
            return false;
        }
        cell += 1;
    }

    if REGISTERED {
        let own_formed = if pending_active {
            register_chart::pending_row_is_canonical(owns, layout.own.base, stroke.own_cells)
        } else {
            register_chart::row_is_canonical(owns, layout.own.base, stroke.own_cells)
        };
        if !own_formed {
            return false;
        }
    } else {
        cell = 0;
        while cell < stroke.own_cells {
            if FOUNDED {
                let local = cell * manifold::OWN_CELL_WORDS;
                let at = layout.own.absolute(local);
                let live = owns[at + manifold::OWN_CELL_LIVE];
                if live > 1
                    || RegionalForm::unpack_compact_checked(owns, at + manifold::OWN_CELL_FORM)
                        .is_err()
                {
                    return false;
                }
                if live == 0 {
                    if owns[at..at + manifold::OWN_CELL_WORDS]
                        .iter()
                        .any(|word| *word != 0)
                    {
                        return false;
                    }
                } else {
                    if !num::packed_cog_is_canonical(owns, at + manifold::OWN_CELL_POSITION)
                        || !num::packed_cog_is_canonical(
                            owns,
                            at + manifold::OWN_CELL_POSITION + manifold::COG_WORDS,
                        )
                    {
                        return false;
                    }
                    let Ok(form) =
                        RegionalForm::unpack_compact_checked(owns, at + manifold::OWN_CELL_FORM)
                    else {
                        return false;
                    };
                    if !form.occupied() {
                        return false;
                    }
                }
            } else if RegionalForm::unpack_compact_checked(
                owns,
                layout.own.absolute(cell * FORM_WORDS),
            )
            .is_err()
            {
                return false;
            }
            cell += 1;
        }
    }

    true
}

/// An active founded continuation has already written part of its current atom's efferent row.
/// That row crosses the substrate seam with the carrier, so the checked mouth admits only the one
/// partial face implied by the next continuation move. It remains an output aperture: carriage
/// never reads the payload after this boundary check.
fn active_radiation_is_canonical(
    radiation: &[u32],
    carriers: &[u32],
    layout: LayoutProof,
    stroke: LineageStroke,
) -> bool {
    let carrier = &carriers[layout.carrier.base..layout.carrier.base + layout.carrier.len];
    let phase = manifold::carrier_continuation_phase(carrier);
    let pending = manifold::carrier_pending_kind(carrier);
    if phase == manifold::CONTINUATION_NONE && pending == manifold::PENDING_NONE {
        return true;
    }
    if pending == manifold::PENDING_DARK_TERMINAL {
        return phase == manifold::CONTINUATION_NONE;
    }
    if stroke.radiation_stride != manifold::RADIATION_WORDS {
        return true;
    }

    let cursor = carrier[manifold::CARRIER_CURSOR_LO] as u64
        | ((carrier[manifold::CARRIER_CURSOR_HI] as u64) << 32);
    if cursor < stroke.worldline_base {
        return false;
    }
    let atom_u64 = cursor - stroke.worldline_base;
    if atom_u64 == 0 || atom_u64 >= stroke.byte_count as u64 || atom_u64 > usize::MAX as u64 {
        return false;
    }
    let atom = atom_u64 as usize;
    let Some(local) = checked_extent_mul(atom, manifold::RADIATION_WORDS) else {
        return false;
    };
    let Some(local_end) = checked_extent_add(local, manifold::RADIATION_WORDS) else {
        return false;
    };
    if local_end > layout.radiation.len {
        return false;
    }
    let at = layout.radiation.absolute(local);
    let row = &radiation[at..at + manifold::RADIATION_WORDS];

    if phase == manifold::CONTINUATION_NONE {
        return (pending == manifold::PENDING_DARK_BEFORE || pending == manifold::PENDING_SUB)
            && row.iter().all(|word| *word == 0);
    }
    if manifold::continuation_is_perceive(phase)
        || phase == manifold::CONTINUATION_WORD_PATH
        || phase == manifold::CONTINUATION_WORD_PERCEIVE
    {
        return row[manifold::RADIATION_FLAGS] == manifold::RADIATION_FOLD
            && row[manifold::RADIATION_GRIP..]
                .iter()
                .all(|word| *word == 0);
    }
    if !manifold::continuation_is_path(phase)
        || row[manifold::RADIATION_FLAGS]
            != (manifold::RADIATION_FOLD
                | manifold::RADIATION_STEP
                | manifold::RADIATION_CUT
                | manifold::RADIATION_BRICK_LIVE)
        || row[manifold::RADIATION_GRIP] as usize >= stroke.cells
        || RegionalForm::unpack_compact_checked(row, manifold::RADIATION_FORM).is_err()
        || !num::packed_cog_is_canonical(row, manifold::RADIATION_ROTOR)
        || !num::packed_cog_is_canonical(row, manifold::RADIATION_ROTOR + manifold::COG_WORDS)
        || !manifold::packed_node_is_canonical(row, manifold::RADIATION_BRICK)
    {
        return false;
    }
    let cross = manifold::unpack_cog(row, manifold::RADIATION_ROTOR);
    let aim = manifold::unpack_cog(row, manifold::RADIATION_ROTOR + manifold::COG_WORDS);
    (cross.mag != 0 || aim.mag != 0)
        && manifold::unpack_node(row, manifold::RADIATION_BRICK).len != 0
}

#[derive(Clone, Copy)]
struct CursorProof {
    atom: usize,
    end: usize,
}

#[inline(never)]
fn prove_cursor(cursor: u64, layout: LayoutProof, stroke: LineageStroke) -> Option<CursorProof> {
    if cursor < stroke.worldline_base || cursor > layout.worldline_end {
        return None;
    }
    let local_cursor = cursor - stroke.worldline_base;
    if local_cursor > stroke.byte_count as u64 {
        return None;
    }
    let atom = if local_cursor < 1 {
        1
    } else {
        local_cursor as usize
    };
    let end = if stroke.stroke_atoms == 0 {
        stroke.byte_count
    } else {
        let carried = checked_extent_add(local_cursor as usize, stroke.stroke_atoms)?;
        if carried < stroke.byte_count {
            carried
        } else {
            stroke.byte_count
        }
    };
    Some(CursorProof { atom, end })
}

/// The one body-owned lineage-time verb. `FOUNDED`, the depth-zero radiation target, and the
/// complete-enclosure target alter only boundary representation; the atom loop, darkness,
/// thickening, channel fold, and finish exist once.
#[allow(clippy::too_many_arguments)]
fn carry_formed<S, R, C, T, const FOUNDED: bool, const REGISTERED: bool>(
    standing: &[u32],
    owns: &mut [u32],
    carriers: &mut [u32],
    bytes: &[u32],
    radiation: &mut R::Backing,
    mut radiation_state: RadiationState,
    completion: &mut C::Backing,
    mut completion_state: CompletionState,
    layout: LayoutProof,
    stroke: LineageStroke,
    recast: &mut [u32; 2],
    contact_surface: &mut T,
) -> Option<StrokeResult>
where
    S: WordSeam,
    R: RadiationTarget<S>,
    C: CompletionTarget<S>,
    T: RegisterContactSurface<S>,
{
    let seed_difference = boundary::difference_word(stroke.seed_current, stroke.seed_previous);
    let seed_frame = manifold::atom_node(seed_difference).place;
    let genesis = channel::LineageChannel::from_located_first_difference(seed_frame);
    let cursor = FeltLineage::<S, FOUNDED, REGISTERED>::read(
        carriers,
        layout.carrier.absolute(manifold::CARRIER_CURSOR_LO),
    ) as u64
        | ((FeltLineage::<S, FOUNDED, REGISTERED>::read(
            carriers,
            layout.carrier.absolute(manifold::CARRIER_CURSOR_HI),
        ) as u64)
            << 32);
    if cursor != 0
        && !unsafe {
            channel::LineageChannel::packed_basis_forms_unchecked_with::<S>(
                carriers,
                layout.carrier.absolute(manifold::CARRIER_CHANNEL),
            )
        }
    {
        return None;
    }
    let channel = unsafe {
        channel::LineageChannel::unpack_or_unchecked_with::<S>(
            carriers,
            layout.carrier.absolute(manifold::CARRIER_CHANNEL),
            genesis,
        )
    };
    let frame = channel.frame().anchor;
    let cursor_proof = prove_cursor(cursor, layout, stroke)?;
    let dark_pending = FeltLineage::<S, FOUNDED, REGISTERED>::read(
        carriers,
        layout.carrier.absolute(manifold::CARRIER_DARK_LO),
    ) as u64
        | ((FeltLineage::<S, FOUNDED, REGISTERED>::read(
            carriers,
            layout.carrier.absolute(manifold::CARRIER_DARK_HI),
        ) as u64)
            << 32);
    let sub_stance = unsafe {
        manifold::unpack_node_unchecked_with::<S>(
            carriers,
            layout.carrier.absolute(manifold::CARRIER_SUB_STANCE),
        )
    };
    let sub_fly = unsafe {
        manifold::unpack_face_unchecked_with::<S>(
            carriers,
            layout.carrier.absolute(manifold::CARRIER_SUB_FLY),
        )
    };
    let sub_fly_live = FeltLineage::<S, FOUNDED, REGISTERED>::read(
        carriers,
        layout.carrier.absolute(manifold::CARRIER_SUB_FLY_LIVE),
    ) != 0;
    let carrier_depth = manifold::carrier_row_depth(layout.carrier.len);
    let continuation = manifold::carrier_continuation_base(carrier_depth);
    let continuation_phase = FeltLineage::<S, FOUNDED, REGISTERED>::read(
        carriers,
        layout
            .carrier
            .absolute(continuation + manifold::CARRIER_CONTINUATION_PHASE),
    );
    let continuation_depth_u64 = FeltLineage::<S, FOUNDED, REGISTERED>::read(
        carriers,
        layout
            .carrier
            .absolute(continuation + manifold::CARRIER_CONTINUATION_DEPTH_LO),
    ) as u64
        | ((FeltLineage::<S, FOUNDED, REGISTERED>::read(
            carriers,
            layout
                .carrier
                .absolute(continuation + manifold::CARRIER_CONTINUATION_DEPTH_HI),
        ) as u64)
            << 32);
    if continuation_depth_u64 > usize::MAX as u64 {
        return None;
    }
    let continuation_depth = continuation_depth_u64 as usize;
    let continuation_brick = unsafe {
        manifold::unpack_node_unchecked_with::<S>(
            carriers,
            layout
                .carrier
                .absolute(continuation + manifold::CARRIER_CONTINUATION_BRICK),
        )
    };
    let pending = manifold::carrier_pending_base(carrier_depth);
    let pending_control = FeltLineage::<S, FOUNDED, REGISTERED>::read(
        carriers,
        layout
            .carrier
            .absolute(pending + manifold::CARRIER_PENDING_CONTROL),
    );
    let pending_kind = manifold::pending_kind(pending_control);
    if pending_control & !manifold::PENDING_CONTROL_MASK != 0
        || pending_kind == manifold::PENDING_INVALID
    {
        return None;
    }
    let pending_form = unsafe {
        RegionalForm::unpack_unchecked_with::<S>(
            carriers,
            layout
                .carrier
                .absolute(pending + manifold::CARRIER_PENDING_FORM),
        )
    };
    if !manifold::continuation_shape_is_formed(
        continuation_phase,
        continuation_depth,
        continuation_brick.len != 0,
        carrier_depth,
    ) || (continuation_phase != manifold::CONTINUATION_NONE && cursor == 0)
    {
        return None;
    }
    if continuation_phase != manifold::CONTINUATION_NONE
        || (pending_kind != manifold::PENDING_NONE
            && pending_kind != manifold::PENDING_DARK_TERMINAL)
    {
        let admitted = checked_worldline_add(stroke.worldline_base, cursor_proof.atom as u64)?;
        if cursor != admitted || cursor_proof.atom >= stroke.byte_count {
            return None;
        }
    }
    if pending_kind == manifold::PENDING_DARK_TERMINAL
        && (cursor != layout.worldline_end
            || continuation_phase != manifold::CONTINUATION_NONE
            || dark_pending == 0)
    {
        return None;
    }
    let register_face = if REGISTERED {
        register_chart::read_face::<S>(owns, layout.own.base)
    } else {
        register_chart::RegisterFace::BORN
    };
    let own_axis = if REGISTERED {
        register_face.axis as i64
    } else {
        stroke.own_axis
    };
    if REGISTERED {
        let active_own_cells =
            checked_extent_mul(register_face.axis as usize, register_face.axis as usize)?;
        if !register_face.axis.is_power_of_two() || active_own_cells > stroke.own_cells {
            return None;
        }
    }
    let mut body = FeltLineage::<S, FOUNDED, REGISTERED> {
        cells: stroke.cells,
        own_cells: stroke.own_cells,
        depth: carrier_depth,
        standing_axis: stroke.standing_axis,
        own_axis,
        frame,
        channel,
        dark_pending,
        sub_stance,
        sub_fly,
        sub_fly_live,
        continuation_phase,
        continuation_depth,
        continuation_brick,
        pending_control,
        pending_form,
        register_face,
        recast_old_axis: 0,
        recast_new_axis: 0,
        invalid: false,
        own_cell_offset: if REGISTERED {
            manifold::OWN_REGISTER_WORDS
        } else {
            0
        },
        own_base: layout.own.base,
        carrier_base: layout.carrier.base,
        terms: TermCounts::ZERO,
        seam: PhantomData,
    };

    if pending_kind != manifold::PENDING_NONE {
        if !REGISTERED {
            return None;
        }
        let position =
            body.pending_position_if_formed(carriers, bytes, stroke, cursor_proof.atom)?;
        if !register_chart::pending_stage_is_formed::<S>(
            owns,
            layout.own.base,
            stroke.own_cells,
            body.register_face,
            position,
        ) {
            return None;
        }
    }

    let mut atom = cursor_proof.atom;
    let mut interior_moves = 0usize;
    let mut installment_spent = false;
    let entering_pending = body.pending_kind();
    let mut resumed_atom = false;

    // A pending deed owns the absolute front of the relaunch. The old caller/K/radiation faces are
    // still committed, so the exact old-gauge form and typed checkpoint reconstruct the same deed
    // before any ordinary continuation or later raw difference may move.
    if entering_pending != manifold::PENDING_NONE {
        if entering_pending != manifold::PENDING_DARK_TERMINAL {
            R::set_atom(&mut radiation_state, atom);
            C::set_atom(&mut completion_state, atom);
        }
        if entering_pending == manifold::PENDING_DARK_BEFORE
            || entering_pending == manifold::PENDING_DARK_TERMINAL
        {
            let _ = body.deposit_dark_tread(owns, entering_pending);
        } else if entering_pending == manifold::PENDING_SUB {
            let previous = packed_byte::<S>(bytes, stroke.byte_offset + atom - 1);
            let current = packed_byte::<S>(bytes, stroke.byte_offset + atom);
            let difference = boundary::difference_word(current, previous);
            if difference.mag == 0 {
                return None;
            }
            body.live_difference::<R, C>(
                standing,
                owns,
                carriers,
                radiation,
                &mut radiation_state,
                completion,
                &mut completion_state,
                difference,
                stroke.drive,
            );
            resumed_atom = true;
        } else if entering_pending == manifold::PENDING_ENCLOSURE_CO_PRESENT
            || entering_pending == manifold::PENDING_ENCLOSURE_TERMINAL
            || entering_pending == manifold::PENDING_PATH
        {
            body.continuation_move::<R, C, T>(
                standing,
                owns,
                carriers,
                radiation,
                &mut radiation_state,
                completion,
                &mut completion_state,
                contact_surface,
            );
            interior_moves += 1;
            resumed_atom = true;
        } else {
            return None;
        }
        if body.invalid || C::overflowed(&completion_state) {
            return None;
        }
        if body.pending_kind() != manifold::PENDING_NONE {
            let cursor = if entering_pending == manifold::PENDING_DARK_TERMINAL {
                layout.worldline_end
            } else {
                stroke.worldline_base + atom as u64
            };
            body.finish(carriers, cursor);
            if REGISTERED {
                register_chart::store_face::<S>(owns, layout.own.base, body.register_face);
            }
            recast[0] = body.recast_old_axis;
            recast[1] = body.recast_new_axis;
            return Some(StrokeResult {
                cursor,
                terms: body.terms,
            });
        }
    }

    // An unfinished atom owns the front of every later invocation. Its cursor names that same raw
    // difference until the continuation closes; no later difference can enter between substrate
    // installments.
    if body.continuation_phase != manifold::CONTINUATION_NONE {
        R::set_atom(&mut radiation_state, atom);
        C::set_atom(&mut completion_state, atom);
        if !body.continue_atom::<R, C, T>(
            standing,
            owns,
            carriers,
            radiation,
            &mut radiation_state,
            completion,
            &mut completion_state,
            contact_surface,
            stroke.interior_installment,
            &mut interior_moves,
        ) {
            if body.invalid || C::overflowed(&completion_state) {
                return None;
            }
            let cursor = stroke.worldline_base + atom as u64;
            body.finish(carriers, cursor);
            if REGISTERED {
                register_chart::store_face::<S>(owns, layout.own.base, body.register_face);
            }
            recast[0] = body.recast_old_axis;
            recast[1] = body.recast_new_axis;
            return Some(StrokeResult {
                cursor,
                terms: body.terms,
            });
        }
        atom += 1;
        if C::full(&completion_state)
            || (stroke.interior_installment != 0 && interior_moves >= stroke.interior_installment)
        {
            installment_spent = true;
        }
    } else if resumed_atom {
        atom += 1;
        if C::full(&completion_state) {
            installment_spent = true;
        }
    }

    while !installment_spent && atom < cursor_proof.end {
        let previous = packed_byte::<S>(bytes, stroke.byte_offset + atom - 1);
        let current = packed_byte::<S>(bytes, stroke.byte_offset + atom);
        R::set_atom(&mut radiation_state, atom);
        C::set_atom(&mut completion_state, atom);
        body.live_difference::<R, C>(
            standing,
            owns,
            carriers,
            radiation,
            &mut radiation_state,
            completion,
            &mut completion_state,
            boundary::difference_word(current, previous),
            stroke.drive,
        );
        if body.invalid || C::overflowed(&completion_state) {
            return None;
        }
        if C::full(&completion_state) {
            break;
        }
        if !body.continue_atom::<R, C, T>(
            standing,
            owns,
            carriers,
            radiation,
            &mut radiation_state,
            completion,
            &mut completion_state,
            contact_surface,
            stroke.interior_installment,
            &mut interior_moves,
        ) {
            break;
        }
        atom += 1;
        if C::full(&completion_state)
            || (stroke.interior_installment != 0 && interior_moves >= stroke.interior_installment)
        {
            break;
        }
    }
    if atom >= stroke.byte_count
        && body.continuation_phase == manifold::CONTINUATION_NONE
        && body.pending_kind() == manifold::PENDING_NONE
    {
        let _ = body.deposit_dark_tread(owns, manifold::PENDING_DARK_TERMINAL);
    }
    if body.invalid || C::overflowed(&completion_state) {
        return None;
    }
    let cursor = stroke.worldline_base + atom as u64;
    body.finish(carriers, cursor);
    if REGISTERED {
        register_chart::store_face::<S>(owns, layout.own.base, body.register_face);
    }
    recast[0] = body.recast_old_axis;
    recast[1] = body.recast_new_axis;
    Some(StrokeResult {
        cursor,
        terms: body.terms,
    })
}

#[allow(clippy::too_many_arguments)]
fn carry_dense_with_layout<S: WordSeam>(
    standing: &[u32],
    owns: &mut [u32],
    carriers: &mut [u32],
    bytes: &[u32],
    layout: LayoutProof,
    stroke: LineageStroke,
) -> Option<StrokeResult> {
    let mut no_radiation = ();
    let mut no_completion = ();
    let mut no_recast = [0u32; 2];
    let mut contact_surface = InlineRegisterContactSurface;
    carry_formed::<S, NoRadiation, NoCompletion, _, false, false>(
        standing,
        owns,
        carriers,
        bytes,
        &mut no_radiation,
        RadiationState {
            span: layout.radiation,
            formed: false,
            at: 0,
        },
        &mut no_completion,
        CompletionState {
            span: layout.completion,
            formed: false,
            full: false,
            overflowed: false,
            atom: 0,
            rows: 0,
            next: 0,
        },
        layout,
        stroke,
        &mut no_recast,
        &mut contact_surface,
    )
}

#[allow(clippy::too_many_arguments)]
fn carry_founded_with_layout<S: WordSeam>(
    standing: &[u32],
    owns: &mut [u32],
    carriers: &mut [u32],
    bytes: &[u32],
    radiation: &mut [u32],
    layout: LayoutProof,
    stroke: LineageStroke,
) -> Option<StrokeResult> {
    let radiates = stroke.radiation_stride == manifold::RADIATION_WORDS;
    let radiation_state = RadiationState {
        span: layout.radiation,
        formed: radiates,
        at: 0,
    };
    let mut no_completion = ();
    let mut no_recast = [0u32; 2];
    let mut contact_surface = InlineRegisterContactSurface;
    carry_formed::<S, WordRadiation, NoCompletion, _, true, false>(
        standing,
        owns,
        carriers,
        bytes,
        radiation,
        radiation_state,
        &mut no_completion,
        CompletionState {
            span: layout.completion,
            formed: false,
            full: false,
            overflowed: false,
            atom: 0,
            rows: 0,
            next: 0,
        },
        layout,
        stroke,
        &mut no_recast,
        &mut contact_surface,
    )
}

#[allow(clippy::too_many_arguments)]
fn carry_register_with_layout_target<S: WordSeam, C: CompletionTarget<S>>(
    standing: &[u32],
    owns: &mut [u32],
    carriers: &mut [u32],
    bytes: &[u32],
    radiation: &mut [u32],
    completion: &mut C::Backing,
    completion_state: CompletionState,
    layout: LayoutProof,
    stroke: LineageStroke,
) -> Option<RegisterStrokeResult> {
    let mut contact_surface = InlineRegisterContactSurface;
    carry_register_with_layout_target_surface::<S, C, _>(
        standing,
        owns,
        carriers,
        bytes,
        radiation,
        completion,
        completion_state,
        layout,
        stroke,
        &mut contact_surface,
    )
}

#[allow(clippy::too_many_arguments)]
fn carry_register_with_layout_target_surface<
    S: WordSeam,
    C: CompletionTarget<S>,
    T: RegisterContactSurface<S>,
>(
    standing: &[u32],
    owns: &mut [u32],
    carriers: &mut [u32],
    bytes: &[u32],
    radiation: &mut [u32],
    completion: &mut C::Backing,
    completion_state: CompletionState,
    layout: LayoutProof,
    stroke: LineageStroke,
    contact_surface: &mut T,
) -> Option<RegisterStrokeResult> {
    let radiates = stroke.radiation_stride == manifold::RADIATION_WORDS;
    let radiation_state = RadiationState {
        span: layout.radiation,
        formed: radiates,
        at: 0,
    };
    let mut recast = [0u32; 2];
    let result = carry_formed::<S, WordRadiation, C, T, true, true>(
        standing,
        owns,
        carriers,
        bytes,
        radiation,
        radiation_state,
        completion,
        completion_state,
        layout,
        stroke,
        &mut recast,
        contact_surface,
    )?;
    let carrier = &carriers[layout.carrier.base..layout.carrier.base + layout.carrier.len];
    Some(RegisterStrokeResult {
        cursor: result.cursor,
        terms: result.terms,
        status: if recast[1] != 0 {
            RegisterStrokeStatus::NeedsOwnRecast {
                old_axis: recast[0],
                new_axis: recast[1],
            }
        } else if let Some(required_depth) = required_carrier_rebase_depth(carrier) {
            RegisterStrokeStatus::NeedsCarrierRebase { required_depth }
        } else if result.cursor != layout.worldline_end
            || !manifold::carried_frame_is_at_rest(carrier)
        {
            RegisterStrokeStatus::Continue
        } else {
            RegisterStrokeStatus::Complete
        },
    })
}

#[allow(clippy::too_many_arguments)]
fn carry_register_with_layout<S: WordSeam>(
    standing: &[u32],
    owns: &mut [u32],
    carriers: &mut [u32],
    bytes: &[u32],
    radiation: &mut [u32],
    layout: LayoutProof,
    stroke: LineageStroke,
) -> Option<RegisterStrokeResult> {
    let mut no_completion = ();
    carry_register_with_layout_target::<S, NoCompletion>(
        standing,
        owns,
        carriers,
        bytes,
        radiation,
        &mut no_completion,
        CompletionState {
            span: layout.completion,
            formed: false,
            full: false,
            overflowed: false,
            atom: 0,
            rows: 0,
            next: 0,
        },
        layout,
        stroke,
    )
}

/// Carry one dense host/reference stroke after rejecting every malformed persisted input row. No
/// radiation slice exists in this API or its monomorphized body.
#[allow(clippy::too_many_arguments)]
pub fn carry_dense_stroke<S: WordSeam>(
    standing: &[u32],
    owns: &mut [u32],
    own_words: WordSpan,
    carriers: &mut [u32],
    carrier_words: WordSpan,
    bytes: &[u32],
    stroke: LineageStroke,
) -> Option<StrokeResult> {
    let layout = prove_layout::<false, false>(
        standing.len(),
        owns.len(),
        own_words,
        carriers.len(),
        carrier_words,
        bytes.len(),
        0,
        WordSpan::empty(),
        false,
        0,
        WordSpan::empty(),
        false,
        stroke,
    )?;
    if !boundary_rows_are_canonical::<false, false>(standing, owns, carriers, layout, stroke) {
        return None;
    }
    carry_dense_with_layout::<S>(standing, owns, carriers, bytes, layout, stroke)
}

/// Carry one founded host/reference stroke after rejecting every malformed persisted input row. A
/// formed radiation stride instantiates the real aperture; every other stride preserves the
/// historical no-radiation face without fabricating a backing slice.
#[allow(clippy::too_many_arguments)]
pub fn carry_founded_stroke<S: WordSeam>(
    standing: &[u32],
    owns: &mut [u32],
    own_words: WordSpan,
    carriers: &mut [u32],
    carrier_words: WordSpan,
    bytes: &[u32],
    radiation: &mut [u32],
    radiation_words: WordSpan,
    stroke: LineageStroke,
) -> Option<StrokeResult> {
    let radiates = stroke.radiation_stride == manifold::RADIATION_WORDS;
    let layout = prove_layout::<true, false>(
        standing.len(),
        owns.len(),
        own_words,
        carriers.len(),
        carrier_words,
        bytes.len(),
        radiation.len(),
        radiation_words,
        radiates,
        0,
        WordSpan::empty(),
        false,
        stroke,
    )?;
    if !boundary_rows_are_canonical::<true, false>(standing, owns, carriers, layout, stroke) {
        return None;
    }
    if !active_radiation_is_canonical(radiation, carriers, layout, stroke) {
        return None;
    }
    carry_founded_with_layout::<S>(standing, owns, carriers, bytes, radiation, layout, stroke)
}

/// Carry one REGISTER host/reference stroke. The mutable OWN span is
/// `header ⊕ capacity_cells·whole_cell`; the header's active axis, never the capacity, grounds the
/// current. `NeedsOwnRecast` leaves the causing caller frozen in the carrier; the boundary supplies
/// the exact recast row and relaunches the same stroke before any later caller may run.
#[allow(clippy::too_many_arguments)]
pub fn carry_register_stroke<S: WordSeam>(
    standing: &[u32],
    owns: &mut [u32],
    own_words: WordSpan,
    carriers: &mut [u32],
    carrier_words: WordSpan,
    bytes: &[u32],
    radiation: &mut [u32],
    radiation_words: WordSpan,
    stroke: LineageStroke,
) -> Option<RegisterStrokeResult> {
    let radiates = stroke.radiation_stride == manifold::RADIATION_WORDS;
    let layout = prove_layout::<true, true>(
        standing.len(),
        owns.len(),
        own_words,
        carriers.len(),
        carrier_words,
        bytes.len(),
        radiation.len(),
        radiation_words,
        radiates,
        0,
        WordSpan::empty(),
        false,
        stroke,
    )?;
    if !boundary_rows_are_canonical::<true, true>(standing, owns, carriers, layout, stroke) {
        return None;
    }
    if !active_radiation_is_canonical(radiation, carriers, layout, stroke) {
        return None;
    }
    carry_register_with_layout::<S>(standing, owns, carriers, bytes, radiation, layout, stroke)
}

/// Carry one REGISTER host/reference stroke while exposing the next completed enclosure in this
/// invocation. The completion row must enter zero and is never read by the body after it is
/// written. Filling it yields only at the already-ratified descending stroke seam.
#[allow(clippy::too_many_arguments)]
pub fn carry_register_stroke_with_completion<S: WordSeam>(
    standing: &[u32],
    owns: &mut [u32],
    own_words: WordSpan,
    carriers: &mut [u32],
    carrier_words: WordSpan,
    bytes: &[u32],
    radiation: &mut [u32],
    radiation_words: WordSpan,
    completion: &mut [u32],
    completion_words: WordSpan,
    stroke: LineageStroke,
) -> Option<RegisterStrokeResult> {
    let radiates = stroke.radiation_stride == manifold::RADIATION_WORDS;
    let completes = stroke.completion_stride >= manifold::COMPLETION_WORDS
        && stroke.completion_stride % manifold::COMPLETION_WORDS == 0;
    let layout = prove_layout::<true, true>(
        standing.len(),
        owns.len(),
        own_words,
        carriers.len(),
        carrier_words,
        bytes.len(),
        radiation.len(),
        radiation_words,
        radiates,
        completion.len(),
        completion_words,
        completes,
        stroke,
    )?;
    if !boundary_rows_are_canonical::<true, true>(standing, owns, carriers, layout, stroke)
        || !active_radiation_is_canonical(radiation, carriers, layout, stroke)
        || completion[layout.completion.base..layout.completion.base + layout.completion.len]
            .iter()
            .any(|word| *word != 0)
    {
        return None;
    }
    carry_register_with_layout_target::<S, WordCompletion>(
        standing,
        owns,
        carriers,
        bytes,
        radiation,
        completion,
        CompletionState {
            span: layout.completion,
            formed: completes,
            full: false,
            overflowed: false,
            atom: 0,
            rows: stroke.completion_stride / manifold::COMPLETION_WORDS,
            next: 0,
        },
        layout,
        stroke,
    )
}

/// Device/raw-ABI dense mouth. The mounting shell owns the proof that standing/OWN rows are
/// canonical and that a zero-cursor carrier is zero while a continuing carrier is canonical.
/// Extents are still checked here before any mutation.
#[allow(clippy::too_many_arguments)]
pub fn carry_dense_stroke_trusted<S: WordSeam>(
    standing: &[u32],
    owns: &mut [u32],
    own_words: WordSpan,
    carriers: &mut [u32],
    carrier_words: WordSpan,
    bytes: &[u32],
    stroke: LineageStroke,
) -> Option<StrokeResult> {
    let layout = prove_layout::<false, false>(
        standing.len(),
        owns.len(),
        own_words,
        carriers.len(),
        carrier_words,
        bytes.len(),
        0,
        WordSpan::empty(),
        false,
        0,
        WordSpan::empty(),
        false,
        stroke,
    )?;
    carry_dense_with_layout::<S>(standing, owns, carriers, bytes, layout, stroke)
}

/// Device/raw-ABI founded mouth. The mounting shell supplies canonical standing/OWN/carrier rows;
/// this shared verb retains the complete extent proof and performs no duplicate whole-body scan.
#[allow(clippy::too_many_arguments)]
pub fn carry_founded_stroke_trusted<S: WordSeam>(
    standing: &[u32],
    owns: &mut [u32],
    own_words: WordSpan,
    carriers: &mut [u32],
    carrier_words: WordSpan,
    bytes: &[u32],
    radiation: &mut [u32],
    radiation_words: WordSpan,
    stroke: LineageStroke,
) -> Option<StrokeResult> {
    let radiates = stroke.radiation_stride == manifold::RADIATION_WORDS;
    let layout = prove_layout::<true, false>(
        standing.len(),
        owns.len(),
        own_words,
        carriers.len(),
        carrier_words,
        bytes.len(),
        radiation.len(),
        radiation_words,
        radiates,
        0,
        WordSpan::empty(),
        false,
        stroke,
    )?;
    carry_founded_with_layout::<S>(standing, owns, carriers, bytes, radiation, layout, stroke)
}

/// Device/raw-ABI REGISTER mouth. The mounted row is producer-owned and persistent;
/// scalar extents are still formed here before the body can touch them.
#[allow(clippy::too_many_arguments)]
pub fn carry_register_stroke_trusted<S: WordSeam>(
    standing: &[u32],
    owns: &mut [u32],
    own_words: WordSpan,
    carriers: &mut [u32],
    carrier_words: WordSpan,
    bytes: &[u32],
    radiation: &mut [u32],
    radiation_words: WordSpan,
    stroke: LineageStroke,
) -> Option<RegisterStrokeResult> {
    let radiates = stroke.radiation_stride == manifold::RADIATION_WORDS;
    let layout = prove_layout::<true, true>(
        standing.len(),
        owns.len(),
        own_words,
        carriers.len(),
        carrier_words,
        bytes.len(),
        radiation.len(),
        radiation_words,
        radiates,
        0,
        WordSpan::empty(),
        false,
        stroke,
    )?;
    carry_register_with_layout::<S>(standing, owns, carriers, bytes, radiation, layout, stroke)
}

/// Device/raw-ABI REGISTER mouth with one invocation-local, producer-zeroed completion row. The
/// kernel shell owns row disjointness; this shared verb still forms every scalar extent before the
/// body may move.
#[allow(clippy::too_many_arguments)]
pub fn carry_register_stroke_trusted_with_completion<S: WordSeam>(
    standing: &[u32],
    owns: &mut [u32],
    own_words: WordSpan,
    carriers: &mut [u32],
    carrier_words: WordSpan,
    bytes: &[u32],
    radiation: &mut [u32],
    radiation_words: WordSpan,
    completion: &mut [u32],
    completion_words: WordSpan,
    stroke: LineageStroke,
) -> Option<RegisterStrokeResult> {
    let mut contact_surface = InlineRegisterContactSurface;
    carry_register_stroke_trusted_with_completion_surface::<S, _>(
        standing,
        owns,
        own_words,
        carriers,
        carrier_words,
        bytes,
        radiation,
        radiation_words,
        completion,
        completion_words,
        stroke,
        &mut contact_surface,
    )
}

/// Device/raw-ABI REGISTER mouth whose substrate may form the immutable co-present contact sheet
/// cooperatively. Only contact formation crosses this surface; every deposit and carried deed
/// remains in the body-owned chronological path.
#[allow(clippy::too_many_arguments)]
pub fn carry_register_stroke_trusted_with_completion_surface<
    S: WordSeam,
    T: RegisterContactSurface<S>,
>(
    standing: &[u32],
    owns: &mut [u32],
    own_words: WordSpan,
    carriers: &mut [u32],
    carrier_words: WordSpan,
    bytes: &[u32],
    radiation: &mut [u32],
    radiation_words: WordSpan,
    completion: &mut [u32],
    completion_words: WordSpan,
    stroke: LineageStroke,
    contact_surface: &mut T,
) -> Option<RegisterStrokeResult> {
    let radiates = stroke.radiation_stride == manifold::RADIATION_WORDS;
    let completes = stroke.completion_stride >= manifold::COMPLETION_WORDS
        && stroke.completion_stride % manifold::COMPLETION_WORDS == 0;
    let layout = prove_layout::<true, true>(
        standing.len(),
        owns.len(),
        own_words,
        carriers.len(),
        carrier_words,
        bytes.len(),
        radiation.len(),
        radiation_words,
        radiates,
        completion.len(),
        completion_words,
        completes,
        stroke,
    )?;
    carry_register_with_layout_target_surface::<S, WordCompletion, T>(
        standing,
        owns,
        carriers,
        bytes,
        radiation,
        completion,
        CompletionState {
            span: layout.completion,
            formed: completes,
            full: false,
            overflowed: false,
            atom: 0,
            rows: stroke.completion_stride / manifold::COMPLETION_WORDS,
            next: 0,
        },
        layout,
        stroke,
        contact_surface,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    struct HostWordSeam;

    unsafe impl WordSeam for HostWordSeam {
        unsafe fn read_u32_unchecked(words: &[u32], at: usize) -> u32 {
            *words.get_unchecked(at)
        }

        unsafe fn store_u32_unchecked(words: &mut [u32], at: usize, value: u32) {
            *words.get_unchecked_mut(at) = value;
        }
    }

    fn packed(raw: &[u8]) -> std::vec::Vec<u32> {
        let mut words = std::vec![0u32; (raw.len() + 3) / 4];
        for (at, &byte) in raw.iter().enumerate() {
            words[at >> 2] |= (byte as u32) << ((at & 3) * 8);
        }
        words
    }

    fn run_species(
        founded: bool,
        stroke_atoms: usize,
    ) -> (
        std::vec::Vec<u32>,
        std::vec::Vec<u32>,
        std::vec::Vec<u32>,
        TermCounts,
    ) {
        run_species_with_installment(founded, stroke_atoms, 0)
    }

    fn run_species_with_installment(
        founded: bool,
        stroke_atoms: usize,
        interior_installment: usize,
    ) -> (
        std::vec::Vec<u32>,
        std::vec::Vec<u32>,
        std::vec::Vec<u32>,
        TermCounts,
    ) {
        run_species_observed(
            founded,
            stroke_atoms,
            interior_installment,
            b"aabccddeeffghij",
        )
        .0
    }

    #[allow(clippy::type_complexity)]
    fn run_species_observed(
        founded: bool,
        stroke_atoms: usize,
        interior_installment: usize,
        raw: &[u8],
    ) -> (
        (
            std::vec::Vec<u32>,
            std::vec::Vec<u32>,
            std::vec::Vec<u32>,
            TermCounts,
        ),
        u32,
        usize,
        bool,
    ) {
        const AXIS: usize = 8;
        const DEPTH: usize = 4;
        let bytes = packed(raw);
        let standing = std::vec![0u32; AXIS * AXIS * FORM_WORDS];
        let own_words = if founded {
            AXIS * AXIS * manifold::OWN_CELL_WORDS
        } else {
            AXIS * AXIS * FORM_WORDS
        };
        let mut owns = std::vec![0u32; own_words];
        let mut carriers = std::vec![0u32; manifold::carrier_row_words(DEPTH)];
        let mut radiation = if founded {
            std::vec![0u32; raw.len() * manifold::RADIATION_WORDS]
        } else {
            std::vec::Vec::new()
        };
        let make_stroke = |stroke_atoms| {
            if founded {
                LineageStroke::founded(
                    AXIS as i64,
                    AXIS as i64,
                    AXIS * AXIS,
                    AXIS * AXIS,
                    0,
                    raw.len(),
                    raw[0] as u32,
                    raw[1] as u32,
                    0,
                    stroke_atoms,
                    137,
                    manifold::RADIATION_WORDS,
                )
                .with_interior_installment(interior_installment)
            } else {
                LineageStroke::dense(
                    AXIS as i64,
                    AXIS * AXIS,
                    0,
                    raw.len(),
                    raw[0] as u32,
                    raw[1] as u32,
                    0,
                    stroke_atoms,
                    137,
                )
                .with_interior_installment(interior_installment)
            }
        };
        let mut terms = TermCounts::ZERO;
        let mut phases = 0u32;
        let mut deepest = 0usize;
        let mut resumed_deposit = false;
        loop {
            let carrier_depth = manifold::carrier_row_depth(carriers.len());
            let continuation = manifold::carrier_continuation_base(carrier_depth);
            let prior_phase = carriers[continuation + manifold::CARRIER_CONTINUATION_PHASE];
            let own_words = WordSpan::new(0, owns.len());
            let carrier_words = WordSpan::new(0, carriers.len());
            let result = if founded {
                let radiation_words = WordSpan::new(0, radiation.len());
                carry_founded_stroke::<HostWordSeam>(
                    &standing,
                    &mut owns,
                    own_words,
                    &mut carriers,
                    carrier_words,
                    &bytes,
                    &mut radiation,
                    radiation_words,
                    make_stroke(stroke_atoms),
                )
            } else {
                carry_dense_stroke::<HostWordSeam>(
                    &standing,
                    &mut owns,
                    own_words,
                    &mut carriers,
                    carrier_words,
                    &bytes,
                    make_stroke(stroke_atoms),
                )
            }
            .expect("the bounded lineage stroke is formed");
            if manifold::continuation_is_efferent(prior_phase) && result.terms.total() != 0 {
                resumed_deposit = true;
            }
            terms = terms.add(result.terms);
            let phase = carriers[continuation + manifold::CARRIER_CONTINUATION_PHASE];
            phases |= 1u32 << phase;
            let continuation_depth = carriers
                [continuation + manifold::CARRIER_CONTINUATION_DEPTH_LO]
                as u64
                | ((carriers[continuation + manifold::CARRIER_CONTINUATION_DEPTH_HI] as u64) << 32);
            deepest = deepest.max(continuation_depth as usize);
            if let Some(required_depth) = required_carrier_rebase_depth(&carriers) {
                let required_depth = usize::try_from(required_depth)
                    .expect("the host test boundary can address its required carrier depth");
                let mut fresh = std::vec![0u32; manifold::carrier_row_words(required_depth)];
                assert_eq!(
                    rebase_carrier_row(&carriers, &mut fresh),
                    Some((carrier_depth, required_depth)),
                    "the live continuation mounts exactly the enclosure it reached"
                );
                carriers = fresh;
                continue;
            }
            if result.cursor == raw.len() as u64 {
                break;
            }
        }
        (
            (owns, carriers, radiation, terms),
            phases,
            deepest,
            resumed_deposit,
        )
    }

    type ActiveFoundedFixture = (
        std::vec::Vec<u32>,
        std::vec::Vec<u32>,
        std::vec::Vec<u32>,
        std::vec::Vec<u32>,
        std::vec::Vec<u32>,
        LineageStroke,
    );

    fn active_founded_fixture() -> ActiveFoundedFixture {
        const AXIS: usize = 8;
        const DEPTH: usize = 4;
        let raw: &[u8] =
            b"the cat sat on the mat and then it ran to see an old dog who was far too shy \
now the cat sat on the mat again and the dog ran to see the old cat by the mat";
        let bytes = packed(raw);
        let standing = std::vec![0u32; AXIS * AXIS * FORM_WORDS];
        let mut owns = std::vec![0u32; AXIS * AXIS * manifold::OWN_CELL_WORDS];
        let mut carriers = std::vec![0u32; manifold::carrier_row_words(DEPTH)];
        let mut radiation = std::vec![0u32; raw.len() * manifold::RADIATION_WORDS];
        let stroke = LineageStroke::founded(
            AXIS as i64,
            AXIS as i64,
            AXIS * AXIS,
            AXIS * AXIS,
            0,
            raw.len(),
            raw[0] as u32,
            raw[1] as u32,
            0,
            0,
            137,
            manifold::RADIATION_WORDS,
        )
        .with_interior_installment(1);

        loop {
            let own_len = owns.len();
            let carrier_len = carriers.len();
            let radiation_len = radiation.len();
            let result = carry_founded_stroke::<HostWordSeam>(
                &standing,
                &mut owns,
                WordSpan::new(0, own_len),
                &mut carriers,
                WordSpan::new(0, carrier_len),
                &bytes,
                &mut radiation,
                WordSpan::new(0, radiation_len),
                stroke,
            )
            .expect("the fixture's checked founded continuation is formed");
            if manifold::carrier_continuation_phase(&carriers) != manifold::CONTINUATION_NONE {
                assert!(
                    manifold::carried_frame_is_canonical(&carriers),
                    "the fixture crosses as one canonical active carrier"
                );
                break;
            }
            assert!(
                result.cursor < raw.len() as u64,
                "the fixed fixture reaches an interior continuation before its light end"
            );
        }

        (standing, owns, carriers, bytes, radiation, stroke)
    }

    fn store_test_node(words: &mut [u32], at: usize, node: Node) {
        let mut word = 0usize;
        while word < manifold::NODE_WORDS {
            words[at + word] = manifold::node_packed_word(node, word);
            word += 1;
        }
    }

    fn clear_test_deferred(words: &mut [u32], depth: usize) {
        let first = manifold::carrier_deferred_base(depth, 0);
        let end = manifold::carrier_continuation_base(depth);
        words[first..end].fill(0);
    }

    fn assert_founded_rejected_without_mutation(
        standing: &[u32],
        owns: &mut std::vec::Vec<u32>,
        carriers: &mut std::vec::Vec<u32>,
        bytes: &[u32],
        radiation: &mut std::vec::Vec<u32>,
        stroke: LineageStroke,
        reason: &str,
    ) {
        let owns_before = owns.clone();
        let carriers_before = carriers.clone();
        let radiation_before = radiation.clone();
        let own_len = owns.len();
        let carrier_len = carriers.len();
        let radiation_len = radiation.len();
        assert_eq!(
            carry_founded_stroke::<HostWordSeam>(
                standing,
                owns,
                WordSpan::new(0, own_len),
                carriers,
                WordSpan::new(0, carrier_len),
                bytes,
                radiation,
                WordSpan::new(0, radiation_len),
                stroke,
            ),
            None,
            "{reason}"
        );
        assert_eq!(*owns, owns_before, "{reason}: OWN cannot mutate");
        assert_eq!(
            *carriers, carriers_before,
            "{reason}: carrier cannot mutate"
        );
        assert_eq!(
            *radiation, radiation_before,
            "{reason}: radiation cannot mutate"
        );
    }

    #[test]
    fn the_reserved_register_carriage_is_the_host_register_at_its_accepted_gauge() {
        struct VecChart {
            words: std::vec::Vec<u32>,
        }
        impl manifold::OwnRecast for VecChart {
            fn words(&self) -> &[u32] {
                &self.words
            }
            fn words_mut(&mut self) -> &mut [u32] {
                &mut self.words
            }
            fn recast(&mut self, old_axis: i64, new_axis: i64) {
                let mut fresh = std::vec![0u32; new_axis as usize * new_axis as usize * manifold::OWN_CELL_WORDS];
                if new_axis > old_axis {
                    manifold::zero_extend_own_cells(&self.words, &mut fresh, old_axis, new_axis);
                } else {
                    manifold::narrow_own_cells(&self.words, &mut fresh, old_axis, new_axis);
                }
                self.words = fresh;
            }
        }

        const AXIS: usize = 64;
        const CAPACITY_CELLS: usize = AXIS * AXIS;
        const DEPTH: usize = 32;
        let raw: &[u8] =
            b"the cat sat on the mat and then it ran to see an old dog who was far too shy \
now the cat sat on the mat again and the dog ran to see the old cat by the mat";
        let standing = std::vec![0u32; AXIS * AXIS * FORM_WORDS];

        let mut host_chart = VecChart {
            words: std::vec![0u32; manifold::OWN_CELL_WORDS],
        };
        let mut host_enclosures = std::vec![0u32; DEPTH * manifold::ENCLOSURE_WORDS];
        let mut host = manifold::ErosBody::over_register(
            &standing,
            &mut host_chart,
            AXIS as i64,
            &raw[..2],
            20,
            &mut host_enclosures,
        );
        let mut atom = 1usize;
        while atom < raw.len() {
            host.live_atom(raw[atom - 1], raw[atom], 137);
            atom += 1;
        }
        host.flush_dark();
        let host_axis = host.own_axis() as usize;
        let host_breath = host.breath();
        let host_terms = host.deposited_terms();
        let mut host_carrier = std::vec![0u32; manifold::carrier_row_words(DEPTH)];
        assert!(host.pack_carried_frame(raw.len() as u64, &mut host_carrier));
        drop(host);

        let packed = packed(raw);
        let own_words = manifold::OWN_REGISTER_WORDS + CAPACITY_CELLS * manifold::OWN_CELL_WORDS;
        let mut registered = std::vec![0u32; own_words];
        let mut carrier = std::vec![0u32; manifold::carrier_row_words(DEPTH)];
        let mut no_radiation = std::vec::Vec::new();
        let stroke = LineageStroke::registered(
            AXIS as i64,
            AXIS * AXIS,
            CAPACITY_CELLS,
            0,
            raw.len(),
            raw[0] as u32,
            raw[1] as u32,
            0,
            0,
            137,
            0,
        );
        let result = carry_register_stroke::<HostWordSeam>(
            &standing,
            &mut registered,
            WordSpan::new(0, own_words),
            &mut carrier,
            WordSpan::new(0, manifold::carrier_row_words(DEPTH)),
            &packed,
            &mut no_radiation,
            WordSpan::empty(),
            stroke,
        )
        .expect("the registered host-reference carriage is formed");
        assert_eq!(
            result.status,
            RegisterStrokeStatus::Complete,
            "the declared gate aperture is not the active gauge"
        );
        assert_eq!(result.cursor, raw.len() as u64);
        assert_eq!(result.terms, host_terms);
        assert_eq!(
            carrier, host_carrier,
            "the register posture changes no carrier/K deed"
        );

        let axis = registered[manifold::OWN_REGISTER_AXIS] as usize;
        let occupancy = registered[manifold::OWN_REGISTER_OCCUPANCY_LO] as u64
            | ((registered[manifold::OWN_REGISTER_OCCUPANCY_HI] as u64) << 32);
        let releases = registered[manifold::OWN_REGISTER_RELEASES_LO] as u64
            | ((registered[manifold::OWN_REGISTER_RELEASES_HI] as u64) << 32);
        let narrows = registered[manifold::OWN_REGISTER_NARROWS_LO] as u64
            | ((registered[manifold::OWN_REGISTER_NARROWS_HI] as u64) << 32);
        assert_eq!(axis, host_axis);
        assert_eq!((releases, narrows), host_breath);
        let cell_base = manifold::OWN_REGISTER_WORDS;
        let active_words = axis * axis * manifold::OWN_CELL_WORDS;
        assert_eq!(
            &registered[cell_base..cell_base + active_words],
            host_chart.words.as_slice(),
            "the in-place register is the fresh host chart byte-whole at its accepted hand"
        );
        assert!(
            registered[cell_base + active_words..]
                .iter()
                .all(|word| *word == 0),
            "the unused substrate reservation carries no chart face"
        );
        let live = registered[cell_base..cell_base + active_words]
            .chunks_exact(manifold::OWN_CELL_WORDS)
            .filter(|row| row[manifold::OWN_CELL_LIVE] != 0)
            .count() as u64;
        assert_eq!(
            occupancy, live,
            "the occupancy register and its live grips agree"
        );
        assert!(register_chart::row_is_canonical(
            &registered,
            0,
            CAPACITY_CELLS
        ));
    }

    #[test]
    fn carrier_rebase_preserves_the_live_brick_and_converges_with_an_uninterrupted_row() {
        const AXIS: usize = 64;
        const DEEP: usize = 32;
        const CELLS: usize = AXIS * AXIS;
        let raw: &[u8] = b"a shallow physical carrier must grow around the same live current without retiring its brick or changing the eventual topology";
        let bytes = packed(raw);
        let standing = std::vec![0u32; CELLS * FORM_WORDS];
        let own_words = manifold::OWN_REGISTER_WORDS + CELLS * manifold::OWN_CELL_WORDS;
        let stroke = LineageStroke::registered(
            AXIS as i64,
            CELLS,
            CELLS,
            0,
            raw.len(),
            raw[0] as u32,
            raw[1] as u32,
            0,
            0,
            137,
            0,
        );

        let mut deep_own = std::vec![0u32; own_words];
        let mut deep_carrier = std::vec![0u32; manifold::carrier_row_words(DEEP)];
        let deep = carry_register_stroke::<HostWordSeam>(
            &standing,
            &mut deep_own,
            WordSpan::new(0, own_words),
            &mut deep_carrier,
            WordSpan::new(0, manifold::carrier_row_words(DEEP)),
            &bytes,
            &mut [],
            WordSpan::empty(),
            stroke,
        )
        .expect("the uninterrupted comparison row is formed");
        assert_eq!(deep.status, RegisterStrokeStatus::Complete);

        let mut own = std::vec![0u32; own_words];
        let mut carrier = std::vec![0u32; manifold::carrier_row_words(1)];
        let mut terms = TermCounts::ZERO;
        let mut rebases = 0usize;
        loop {
            let carrier_words = carrier.len();
            let result = carry_register_stroke::<HostWordSeam>(
                &standing,
                &mut own,
                WordSpan::new(0, own_words),
                &mut carrier,
                WordSpan::new(0, carrier_words),
                &bytes,
                &mut [],
                WordSpan::empty(),
                stroke,
            )
            .expect("every rebased invocation resumes the same formed current");
            terms = terms.add(result.terms);
            match result.status {
                RegisterStrokeStatus::Complete => {
                    assert_eq!(result.cursor, raw.len() as u64);
                    break;
                }
                RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => {
                    let old = carrier.clone();
                    let old_depth = manifold::carrier_row_depth(old.len());
                    assert_eq!(required_depth, old_depth as u64 + 1);
                    assert_eq!(required_carrier_rebase_depth(&old), Some(required_depth));
                    let new_depth = usize::try_from(required_depth).unwrap();
                    let mut fresh = std::vec![0u32; manifold::carrier_row_words(new_depth)];
                    assert_eq!(
                        rebase_carrier_row(&old, &mut fresh),
                        Some((old_depth, new_depth))
                    );
                    assert_eq!(
                        &fresh[..manifold::CARRIER_HEADER_WORDS],
                        &old[..manifold::CARRIER_HEADER_WORDS]
                    );
                    for depth in 0..old_depth {
                        let old_at = manifold::carrier_enclosure_base(depth);
                        let new_at = manifold::carrier_enclosure_base(depth);
                        assert_eq!(
                            &fresh[new_at..new_at + manifold::ENCLOSURE_WORDS],
                            &old[old_at..old_at + manifold::ENCLOSURE_WORDS]
                        );
                        let old_at = manifold::carrier_deferred_base(old_depth, depth);
                        let new_at = manifold::carrier_deferred_base(new_depth, depth);
                        assert_eq!(
                            &fresh[new_at..new_at + manifold::CARRIER_DEFERRED_WORDS],
                            &old[old_at..old_at + manifold::CARRIER_DEFERRED_WORDS]
                        );
                    }
                    let old_at = manifold::carrier_continuation_base(old_depth);
                    let new_at = manifold::carrier_continuation_base(new_depth);
                    assert_eq!(
                        &fresh[new_at..new_at + manifold::CARRIER_CONTINUATION_WORDS],
                        &old[old_at..old_at + manifold::CARRIER_CONTINUATION_WORDS]
                    );
                    assert_ne!(
                        manifold::unpack_node(
                            &fresh,
                            new_at + manifold::CARRIER_CONTINUATION_BRICK,
                        )
                        .len,
                        0,
                        "the pressured brick survives the physical rebase"
                    );
                    carrier = fresh;
                    rebases += 1;
                }
                RegisterStrokeStatus::NeedsOwnRecast { .. } => {
                    panic!("the fully afforded OWN row cannot request a chart rebase")
                }
                RegisterStrokeStatus::Continue => {
                    panic!("a zero-installment stroke yields only for an exact resource rebase")
                }
            }
        }
        assert!(rebases > 0);
        assert_eq!(terms, deep.terms);
        assert_eq!(own, deep_own);

        if manifold::carrier_row_depth(carrier.len()) < DEEP {
            let mut normalized = std::vec![0u32; manifold::carrier_row_words(DEEP)];
            rebase_carrier_row(&carrier, &mut normalized).unwrap();
            carrier = normalized;
        }
        assert_eq!(carrier, deep_carrier);
    }

    #[test]
    fn the_one_cell_birth_suspends_recasts_and_resumes_exactly_once() {
        const AXIS: usize = 64;
        const DEPTH: usize = 32;
        const SIBLING_CELLS: usize = AXIS * AXIS;
        let raw: &[u8] =
            b"the cat sat on the mat and then it ran to see an old dog who was far too shy \
now the cat sat on the mat again and the dog ran to see the old cat by the matt";
        let bytes = packed(raw);
        let standing = std::vec![0u32; AXIS * AXIS * FORM_WORDS];
        let carrier_words = manifold::carrier_row_words(DEPTH);
        let radiation_words = raw.len() * manifold::RADIATION_WORDS;

        let stroke_for = |own_cells| {
            LineageStroke::registered(
                AXIS as i64,
                AXIS * AXIS,
                own_cells,
                0,
                raw.len(),
                raw[0] as u32,
                raw[1] as u32,
                0,
                0,
                137,
                manifold::RADIATION_WORDS,
            )
        };

        let sibling_words = manifold::OWN_REGISTER_WORDS + SIBLING_CELLS * manifold::OWN_CELL_WORDS;
        let mut sibling_own = std::vec![0u32; sibling_words];
        let mut sibling_carrier = std::vec![0u32; carrier_words];
        let mut sibling_radiation = std::vec![0u32; radiation_words];
        let sibling = carry_register_stroke::<HostWordSeam>(
            &standing,
            &mut sibling_own,
            WordSpan::new(0, sibling_words),
            &mut sibling_carrier,
            WordSpan::new(0, carrier_words),
            &bytes,
            &mut sibling_radiation,
            WordSpan::new(0, radiation_words),
            stroke_for(SIBLING_CELLS),
        )
        .expect("the already-afforded sibling is formed");
        assert_eq!(sibling.status, RegisterStrokeStatus::Complete);

        let mut own_cells = 1usize;
        let mut exact_own = std::vec![
            0u32;
            manifold::OWN_REGISTER_WORDS + manifold::OWN_CELL_WORDS
        ];
        let mut exact_carrier = std::vec![0u32; carrier_words];
        let mut exact_radiation = std::vec![0u32; radiation_words];
        let mut exact_terms = TermCounts::ZERO;
        let mut first = true;
        let mut invocation = 0usize;
        let mut pending_mask = 0u32;
        loop {
            invocation += 1;
            let own_words = exact_own.len();
            let attempted = carry_register_stroke::<HostWordSeam>(
                &standing,
                &mut exact_own,
                WordSpan::new(0, own_words),
                &mut exact_carrier,
                WordSpan::new(0, carrier_words),
                &bytes,
                &mut exact_radiation,
                WordSpan::new(0, radiation_words),
                stroke_for(own_cells),
            );
            assert!(
                attempted.is_some(),
                "the exact-row conductor invocation {invocation} is formed (axis {} pending {})",
                exact_own[manifold::OWN_REGISTER_AXIS],
                manifold::carrier_pending_kind(&exact_carrier),
            );
            let result = attempted.unwrap();
            exact_terms = exact_terms.add(result.terms);
            match result.status {
                RegisterStrokeStatus::Complete => {
                    assert_eq!(result.cursor, raw.len() as u64);
                    break;
                }
                RegisterStrokeStatus::Continue => {
                    panic!("the zero-installment recast gate cannot yield")
                }
                RegisterStrokeStatus::NeedsOwnRecast { old_axis, new_axis } => {
                    let pending_kind = manifold::carrier_pending_kind(&exact_carrier);
                    pending_mask |= 1 << pending_kind;
                    if pending_kind == manifold::PENDING_ENCLOSURE_CO_PRESENT {
                        assert!(manifold::carried_frame_is_canonical(&exact_carrier));
                        assert!(
                            !manifold::carried_frame_is_at_rest(&exact_carrier),
                            "a real partial co-presence checkpoint is invisible at every receiving edge"
                        );
                        let mut legacy_own =
                            std::vec![0u32; AXIS * AXIS * manifold::OWN_CELL_WORDS];
                        let mut legacy_carrier = exact_carrier.clone();
                        let legacy_resume =
                            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                                let _ = manifold::ErosBody::resume(
                                    &standing,
                                    &mut legacy_own,
                                    AXIS as i64,
                                    b"ab",
                                    137,
                                    &mut legacy_carrier,
                                );
                            }));
                        assert!(
                            legacy_resume.is_err(),
                            "legacy resume cannot expose a partially deposited co-present configuration"
                        );
                    }
                    if first {
                        assert_eq!((old_axis, new_axis), (1, 2));
                        assert_eq!(exact_own[manifold::OWN_REGISTER_AXIS], 1);
                        assert_eq!(exact_own[manifold::OWN_REGISTER_OCCUPANCY_LO], 0);
                        assert!(exact_own[manifold::OWN_REGISTER_WORDS..]
                            .iter()
                            .all(|word| *word == 0));
                        assert_ne!(
                            manifold::carrier_pending_kind(&exact_carrier),
                            manifold::PENDING_NONE,
                            "the first actual term, not a preflight, carries the pending cause"
                        );
                        first = false;
                    }
                    let carrier_before = exact_carrier.clone();
                    let radiation_before = exact_radiation.clone();
                    let fresh_words = registered_own_recast_words(new_axis).unwrap();
                    let mut fresh = std::vec![0u32; fresh_words];
                    assert_eq!(
                        recast_registered_own_row(&exact_own, &mut fresh),
                        Some((old_axis, new_axis))
                    );
                    assert_eq!(exact_carrier, carrier_before);
                    assert_eq!(exact_radiation, radiation_before);
                    exact_own = fresh;
                    own_cells = new_axis as usize * new_axis as usize;
                }
                RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => {
                    panic!("the recast fixture requires carrier depth {required_depth}")
                }
            }
        }

        let final_axis = exact_own[manifold::OWN_REGISTER_AXIS] as usize;
        let exact_words =
            manifold::OWN_REGISTER_WORDS + final_axis * final_axis * manifold::OWN_CELL_WORDS;
        assert_eq!(exact_own.len(), exact_words);
        assert_eq!(exact_own, sibling_own[..exact_words]);
        assert_eq!(exact_carrier, sibling_carrier);
        assert_eq!(exact_radiation, sibling_radiation);
        assert_eq!(exact_terms, sibling.terms);
        assert_eq!(
            manifold::carrier_pending_kind(&exact_carrier),
            manifold::PENDING_NONE
        );
        assert!(registered_own_row_is_canonical(
            &exact_own,
            final_axis * final_axis
        ));
        assert_eq!(
            pending_mask,
            (1 << manifold::PENDING_SUB)
                | (1 << manifold::PENDING_ENCLOSURE_TERMINAL)
                | (1 << manifold::PENDING_PATH),
            "after completed lower constituents depart, the long conductor pins only its live SUB, enclosure-terminal, and path callers"
        );
    }

    #[test]
    fn discharged_lower_constituents_do_not_reappear_as_afferent_co_present_recasts() {
        const DEPTH: usize = 32;
        let raw: &[u8] =
            b"fn carry(frame: Frame, light: &[u8]) -> Frame { light.iter().fold(frame, |held, event| held.relate(*event)) }";
        let bytes = packed(raw);
        let standing = std::vec![0u32; FORM_WORDS];
        let carrier_words = manifold::carrier_row_words(DEPTH);
        let radiation_words = raw.len() * manifold::RADIATION_WORDS;
        let mut owns = std::vec![0u32; registered_own_recast_words(1).unwrap()];
        let mut own_cells = 1usize;
        let mut carrier = std::vec![0u32; carrier_words];
        let mut radiation = std::vec![0u32; radiation_words];
        let mut saw_afferent_co_present = false;

        loop {
            let own_words = owns.len();
            let result = carry_register_stroke::<HostWordSeam>(
                &standing,
                &mut owns,
                WordSpan::new(0, own_words),
                &mut carrier,
                WordSpan::new(0, carrier_words),
                &bytes,
                &mut radiation,
                WordSpan::new(0, radiation_words),
                LineageStroke::registered(
                    1,
                    1,
                    own_cells,
                    0,
                    raw.len(),
                    raw[0] as u32,
                    raw[1] as u32,
                    0,
                    0,
                    137,
                    manifold::RADIATION_WORDS,
                ),
            )
            .expect("the exact-row code current remains formed across every recast");

            match result.status {
                RegisterStrokeStatus::Complete => break,
                RegisterStrokeStatus::Continue => {
                    panic!("the zero-installment code-current gate cannot yield")
                }
                RegisterStrokeStatus::NeedsOwnRecast { new_axis, .. } => {
                    assert!(
                        manifold::carried_frame_is_canonical(&carrier),
                        "every pending deed carries a complete caller posture"
                    );
                    if manifold::carrier_pending_kind(&carrier)
                        == manifold::PENDING_ENCLOSURE_CO_PRESENT
                        && manifold::continuation_is_afferent(manifold::carrier_continuation_phase(
                            &carrier,
                        ))
                    {
                        let continuation = manifold::carrier_continuation_base(DEPTH);
                        assert_ne!(
                            manifold::unpack_node(
                                &carrier,
                                continuation + manifold::CARRIER_CONTINUATION_BRICK,
                            )
                            .len,
                            0,
                            "the frozen afferent call retains the brick it has not yet returned"
                        );
                        saw_afferent_co_present = true;
                    }
                    let mut fresh = std::vec![0u32; registered_own_recast_words(new_axis).unwrap()];
                    recast_registered_own_row(&owns, &mut fresh).unwrap();
                    owns = fresh;
                    own_cells = new_axis as usize * new_axis as usize;
                }
                RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => {
                    panic!("the afferent fixture requires carrier depth {required_depth}")
                }
            }
        }

        assert!(
            !saw_afferent_co_present,
            "a completed lower constituent cannot remain active merely to force a later co-present recast"
        );
        assert!(manifold::carried_frame_is_at_rest(&carrier));
    }

    #[test]
    fn registered_installments_continue_until_the_true_completed_edge() {
        const DEPTH: usize = 32;
        let raw: &[u8] = b"a carried current yields between exact interior moves and resumes over the same immutable light until its true receiving edge";
        let bytes = packed(raw);
        let standing = std::vec![0u32; FORM_WORDS];
        let carrier_words = manifold::carrier_row_words(DEPTH);
        let mut owns = std::vec![0u32; registered_own_recast_words(1).unwrap()];
        let mut own_cells = 1usize;
        let mut carrier = std::vec![0u32; carrier_words];
        let mut no_radiation = std::vec![0u32; 1];
        let mut saw_continue = false;

        loop {
            let own_words = owns.len();
            let result = carry_register_stroke::<HostWordSeam>(
                &standing,
                &mut owns,
                WordSpan::new(0, own_words),
                &mut carrier,
                WordSpan::new(0, carrier_words),
                &bytes,
                &mut no_radiation,
                WordSpan::empty(),
                LineageStroke::registered(
                    1,
                    1,
                    own_cells,
                    0,
                    raw.len(),
                    raw[0] as u32,
                    raw[1] as u32,
                    0,
                    0,
                    137,
                    0,
                )
                .with_interior_installment(1),
            )
            .expect("every installment resumes the same formed current");
            match result.status {
                RegisterStrokeStatus::Continue => {
                    saw_continue = true;
                    assert!(
                        result.cursor < raw.len() as u64
                            || !manifold::carried_frame_is_at_rest(&carrier),
                        "CONTINUE exposes a real unfinished worldline or carrier"
                    );
                }
                RegisterStrokeStatus::NeedsOwnRecast { new_axis, .. } => {
                    let mut fresh = std::vec![0u32; registered_own_recast_words(new_axis).unwrap()];
                    recast_registered_own_row(&owns, &mut fresh).unwrap();
                    owns = fresh;
                    own_cells = new_axis as usize * new_axis as usize;
                }
                RegisterStrokeStatus::Complete => {
                    assert_eq!(result.cursor, raw.len() as u64);
                    assert!(manifold::carried_frame_is_at_rest(&carrier));
                    break;
                }
                RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => {
                    panic!("the installment fixture requires carrier depth {required_depth}")
                }
            }
        }
        assert!(
            saw_continue,
            "the positive installment returns its continuation face"
        );
    }

    #[test]
    fn every_enclosure_completion_crosses_one_event_aperture_and_the_seam_is_gauge() {
        const DEPTH: usize = 32;
        let raw: &[u8] = b"the same code and language return through a changed body while every completed enclosure crosses in its own order";
        let bytes = packed(raw);
        let standing = std::vec![0u32; FORM_WORDS];
        let carrier_words = manifold::carrier_row_words(DEPTH);
        let radiation_words = raw.len() * manifold::RADIATION_WORDS;

        let stroke = |own_cells| {
            LineageStroke::registered(
                1,
                1,
                own_cells,
                0,
                raw.len(),
                raw[0] as u32,
                raw[1] as u32,
                0,
                0,
                137,
                manifold::RADIATION_WORDS,
            )
        };

        let mut gauge_owns = std::vec![0u32; registered_own_recast_words(1).unwrap()];
        let mut gauge_cells = 1usize;
        let mut gauge_carrier = std::vec![0u32; carrier_words];
        let mut gauge_radiation = std::vec![0u32; radiation_words];
        let mut gauge_terms = TermCounts::ZERO;
        loop {
            let own_words = gauge_owns.len();
            let result = carry_register_stroke::<HostWordSeam>(
                &standing,
                &mut gauge_owns,
                WordSpan::new(0, own_words),
                &mut gauge_carrier,
                WordSpan::new(0, carrier_words),
                &bytes,
                &mut gauge_radiation,
                WordSpan::new(0, radiation_words),
                stroke(gauge_cells),
            )
            .unwrap();
            gauge_terms = gauge_terms.add(result.terms);
            match result.status {
                RegisterStrokeStatus::Complete => break,
                RegisterStrokeStatus::Continue => panic!("the uninterrupted gauge cannot yield"),
                RegisterStrokeStatus::NeedsOwnRecast { new_axis, .. } => {
                    let mut fresh = std::vec![0u32; registered_own_recast_words(new_axis).unwrap()];
                    recast_registered_own_row(&gauge_owns, &mut fresh).unwrap();
                    gauge_owns = fresh;
                    gauge_cells = new_axis as usize * new_axis as usize;
                }
                RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => {
                    panic!("the completion gauge requires carrier depth {required_depth}")
                }
            }
        }

        let mut owns = std::vec![0u32; registered_own_recast_words(1).unwrap()];
        let mut own_cells = 1usize;
        let mut carrier = std::vec![0u32; carrier_words];
        let mut radiation = std::vec![0u32; radiation_words];
        let mut completion = std::vec![0u32; manifold::COMPLETION_WORDS];
        let mut terms = TermCounts::ZERO;
        let mut events = 0usize;
        let mut kinds = 0u32;
        let mut deepest = 0u64;
        let mut narrow_rows = std::vec::Vec::new();
        loop {
            completion.fill(0);
            let own_words = owns.len();
            let result = carry_register_stroke_with_completion::<HostWordSeam>(
                &standing,
                &mut owns,
                WordSpan::new(0, own_words),
                &mut carrier,
                WordSpan::new(0, carrier_words),
                &bytes,
                &mut radiation,
                WordSpan::new(0, radiation_words),
                &mut completion,
                WordSpan::new(0, manifold::COMPLETION_WORDS),
                stroke(own_cells)
                    .with_interior_installment(1024)
                    .with_completion_stride(manifold::COMPLETION_WORDS),
            )
            .expect("the next-completion aperture carries the same formed current");
            terms = terms.add(result.terms);
            let kind = completion[manifold::COMPLETION_KIND];
            if kind != 0 {
                narrow_rows.push(completion.clone());
                events += 1;
                kinds |= 1 << kind;
                let event = completion[manifold::COMPLETION_EVENT_LO] as u64
                    | ((completion[manifold::COMPLETION_EVENT_HI] as u64) << 32);
                let grain = completion[manifold::COMPLETION_GRAIN_LO] as u64
                    | ((completion[manifold::COMPLETION_GRAIN_HI] as u64) << 32);
                deepest = deepest.max(grain);
                assert!(event > 0 && event < raw.len() as u64);
                assert!(
                    (kind == manifold::COMPLETION_ATOM_FOLD && grain == 0)
                        || ((kind == manifold::COMPLETION_AFFERENT
                            || kind == manifold::COMPLETION_EFFERENT)
                            && grain > 0)
                );
                assert!(RegionalForm::unpack_compact_checked(
                    &completion,
                    manifold::COMPLETION_FORM,
                )
                .is_ok());
                assert!(num::packed_cog_is_canonical(
                    &completion,
                    manifold::COMPLETION_ROTOR,
                ));
                assert!(num::packed_cog_is_canonical(
                    &completion,
                    manifold::COMPLETION_ROTOR + manifold::COG_WORDS,
                ));
                assert!(manifold::packed_node_is_canonical(
                    &completion,
                    manifold::COMPLETION_BRICK,
                ));
                assert_ne!(
                    manifold::unpack_node(&completion, manifold::COMPLETION_BRICK).len,
                    0
                );
            }
            match result.status {
                RegisterStrokeStatus::Complete => break,
                RegisterStrokeStatus::Continue => {}
                RegisterStrokeStatus::NeedsOwnRecast { new_axis, .. } => {
                    let mut fresh = std::vec![0u32; registered_own_recast_words(new_axis).unwrap()];
                    recast_registered_own_row(&owns, &mut fresh).unwrap();
                    owns = fresh;
                    own_cells = new_axis as usize * new_axis as usize;
                }
                RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => {
                    panic!("the narrow completion fixture requires carrier depth {required_depth}")
                }
            }
        }

        assert!(events > 0 && deepest > 1);
        assert_ne!(kinds & (1 << manifold::COMPLETION_ATOM_FOLD), 0);
        assert_ne!(kinds & (1 << manifold::COMPLETION_AFFERENT), 0);
        assert_ne!(kinds & (1 << manifold::COMPLETION_EFFERENT), 0);
        assert_eq!(owns, gauge_owns);
        assert_eq!(carrier, gauge_carrier);
        assert_eq!(radiation, gauge_radiation);
        assert_eq!(terms, gauge_terms);

        const WIDE_ROWS: usize = 64;
        let wide_words = WIDE_ROWS * manifold::COMPLETION_WORDS;
        let mut wide_owns = std::vec![0u32; registered_own_recast_words(1).unwrap()];
        let mut wide_cells = 1usize;
        let mut wide_carrier = std::vec![0u32; carrier_words];
        let mut wide_radiation = std::vec![0u32; radiation_words];
        let mut wide_completion = std::vec![0u32; wide_words];
        let mut wide_terms = TermCounts::ZERO;
        let mut wide_rows = std::vec::Vec::new();
        loop {
            wide_completion.fill(0);
            let own_words = wide_owns.len();
            let result = carry_register_stroke_with_completion::<HostWordSeam>(
                &standing,
                &mut wide_owns,
                WordSpan::new(0, own_words),
                &mut wide_carrier,
                WordSpan::new(0, carrier_words),
                &bytes,
                &mut wide_radiation,
                WordSpan::new(0, radiation_words),
                &mut wide_completion,
                WordSpan::new(0, wide_words),
                stroke(wide_cells)
                    .with_interior_installment(1024)
                    .with_completion_stride(wide_words),
            )
            .expect("the plural completion aperture carries the same formed current");
            wide_terms = wide_terms.add(result.terms);
            let mut dormant = false;
            for row in wide_completion.chunks_exact(manifold::COMPLETION_WORDS) {
                if row[manifold::COMPLETION_KIND] == 0 {
                    dormant = true;
                } else {
                    assert!(
                        !dormant,
                        "completion rows precede the dormant aperture tail"
                    );
                    wide_rows.push(row.to_vec());
                }
            }
            match result.status {
                RegisterStrokeStatus::Complete => break,
                RegisterStrokeStatus::Continue => {}
                RegisterStrokeStatus::NeedsOwnRecast { new_axis, .. } => {
                    let mut fresh = std::vec![0u32; registered_own_recast_words(new_axis).unwrap()];
                    recast_registered_own_row(&wide_owns, &mut fresh).unwrap();
                    wide_owns = fresh;
                    wide_cells = new_axis as usize * new_axis as usize;
                }
                RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => {
                    panic!("the wide completion fixture requires carrier depth {required_depth}")
                }
            }
        }

        assert_eq!(wide_rows, narrow_rows);
        assert_eq!(wide_owns, gauge_owns);
        assert_eq!(wide_carrier, gauge_carrier);
        assert_eq!(wide_radiation, gauge_radiation);
        assert_eq!(wide_terms, gauge_terms);
    }

    fn assert_pending_species_resumes_exact(raw: &[u8], expected_kind: u32) {
        const AXIS: usize = 16;
        const DEPTH: usize = 4;
        let bytes = packed(raw);
        let standing = std::vec![0u32; AXIS * AXIS * FORM_WORDS];
        let carrier_words = manifold::carrier_row_words(DEPTH);
        let radiation_words = raw.len() * manifold::RADIATION_WORDS;
        let stroke_for = |own_cells| {
            LineageStroke::registered(
                AXIS as i64,
                AXIS * AXIS,
                own_cells,
                0,
                raw.len(),
                raw[0] as u32,
                raw[1] as u32,
                0,
                0,
                137,
                manifold::RADIATION_WORDS,
            )
        };

        let sibling_cells = AXIS * AXIS;
        let sibling_words = manifold::OWN_REGISTER_WORDS + sibling_cells * manifold::OWN_CELL_WORDS;
        let mut sibling_own = std::vec![0u32; sibling_words];
        let mut sibling_carrier = std::vec![0u32; carrier_words];
        let mut sibling_radiation = std::vec![0u32; radiation_words];
        let sibling = carry_register_stroke::<HostWordSeam>(
            &standing,
            &mut sibling_own,
            WordSpan::new(0, sibling_words),
            &mut sibling_carrier,
            WordSpan::new(0, carrier_words),
            &bytes,
            &mut sibling_radiation,
            WordSpan::new(0, radiation_words),
            stroke_for(sibling_cells),
        )
        .unwrap();
        assert_eq!(sibling.status, RegisterStrokeStatus::Complete);

        let mut owns = std::vec![
            0u32;
            manifold::OWN_REGISTER_WORDS + manifold::OWN_CELL_WORDS
        ];
        let mut own_cells = 1usize;
        let mut carrier = std::vec![0u32; carrier_words];
        let mut radiation = std::vec![0u32; radiation_words];
        let mut terms = TermCounts::ZERO;
        let mut mask = 0u32;
        loop {
            let own_words = owns.len();
            let result = carry_register_stroke::<HostWordSeam>(
                &standing,
                &mut owns,
                WordSpan::new(0, own_words),
                &mut carrier,
                WordSpan::new(0, carrier_words),
                &bytes,
                &mut radiation,
                WordSpan::new(0, radiation_words),
                stroke_for(own_cells),
            )
            .unwrap();
            terms = terms.add(result.terms);
            match result.status {
                RegisterStrokeStatus::Complete => break,
                RegisterStrokeStatus::Continue => {
                    panic!("the zero-installment pending-kind gate cannot yield")
                }
                RegisterStrokeStatus::NeedsOwnRecast { new_axis, .. } => {
                    let kind = manifold::carrier_pending_kind(&carrier);
                    mask |= 1 << kind;
                    let carrier_before = carrier.clone();
                    let radiation_before = radiation.clone();
                    let mut fresh = std::vec![0u32; registered_own_recast_words(new_axis).unwrap()];
                    recast_registered_own_row(&owns, &mut fresh).unwrap();
                    assert_eq!(carrier, carrier_before);
                    assert_eq!(radiation, radiation_before);
                    owns = fresh;
                    own_cells = new_axis as usize * new_axis as usize;
                }
                RegisterStrokeStatus::NeedsCarrierRebase { required_depth } => {
                    panic!("the pending-species fixture requires carrier depth {required_depth}")
                }
            }
        }

        assert_ne!(
            mask & (1 << expected_kind),
            0,
            "the requested caller suspended"
        );
        let axis = owns[manifold::OWN_REGISTER_AXIS] as usize;
        let active_words = manifold::OWN_REGISTER_WORDS + axis * axis * manifold::OWN_CELL_WORDS;
        assert_eq!(
            owns,
            sibling_own[..active_words],
            "OWN kind {expected_kind}"
        );
        assert_eq!(carrier, sibling_carrier, "carrier kind {expected_kind}");
        assert_eq!(
            radiation, sibling_radiation,
            "radiation kind {expected_kind}"
        );
        assert_eq!(terms, sibling.terms, "terms kind {expected_kind}");
    }

    #[test]
    fn dark_before_terminal_dark_and_path_suspend_as_total_callers() {
        assert_pending_species_resumes_exact(b"aab", manifold::PENDING_DARK_BEFORE);
        assert_pending_species_resumes_exact(b"aa", manifold::PENDING_DARK_TERMINAL);
        // A bounded exhaustive enumeration of short `a`..=`d` streams produced this compact
        // conductor as the first retained fixture whose one-cell caller freezes at PATH. The
        // search is deliberately absent from the gate; this fixed worldline pins its result.
        assert_pending_species_resumes_exact(b"adcacaaaa", manifold::PENDING_PATH);
    }

    #[test]
    fn malformed_pending_caller_is_rejected_before_mutation() {
        const AXIS: usize = 16;
        const DEPTH: usize = 4;
        let raw = b"aa";
        let bytes = packed(raw);
        let standing = std::vec![0u32; AXIS * AXIS * FORM_WORDS];
        let own_words = manifold::OWN_REGISTER_WORDS + manifold::OWN_CELL_WORDS;
        let carrier_words = manifold::carrier_row_words(DEPTH);
        let radiation_words = raw.len() * manifold::RADIATION_WORDS;
        let mut owns = std::vec![0u32; own_words];
        let mut carrier = std::vec![0u32; carrier_words];
        let mut radiation = std::vec![0u32; radiation_words];
        let stroke = LineageStroke::registered(
            AXIS as i64,
            AXIS * AXIS,
            1,
            0,
            raw.len(),
            raw[0] as u32,
            raw[1] as u32,
            0,
            0,
            137,
            manifold::RADIATION_WORDS,
        );
        let suspended = carry_register_stroke::<HostWordSeam>(
            &standing,
            &mut owns,
            WordSpan::new(0, own_words),
            &mut carrier,
            WordSpan::new(0, carrier_words),
            &bytes,
            &mut radiation,
            WordSpan::new(0, radiation_words),
            stroke,
        )
        .unwrap();
        assert_eq!(
            suspended.status,
            RegisterStrokeStatus::NeedsOwnRecast {
                old_axis: 1,
                new_axis: 2,
            }
        );
        assert_eq!(
            manifold::carrier_pending_kind(&carrier),
            manifold::PENDING_DARK_TERMINAL
        );

        let pending = manifold::carrier_pending_base(DEPTH);
        carrier[pending + manifold::CARRIER_PENDING_CONTROL] =
            manifold::pending_control(manifold::PENDING_SUB, 0);
        assert!(manifold::carried_frame_is_canonical(&carrier));
        let before = (owns.clone(), carrier.clone(), radiation.clone());
        assert!(carry_register_stroke::<HostWordSeam>(
            &standing,
            &mut owns,
            WordSpan::new(0, own_words),
            &mut carrier,
            WordSpan::new(0, carrier_words),
            &bytes,
            &mut radiation,
            WordSpan::new(0, radiation_words),
            stroke,
        )
        .is_none());
        assert_eq!(owns, before.0);
        assert_eq!(carrier, before.1);
        assert_eq!(radiation, before.2);
    }

    #[test]
    fn dense_and_founded_species_share_one_stroke_and_the_seam_is_gauge() {
        for founded in [false, true] {
            let whole = run_species(founded, 0);
            let split = run_species(founded, 3);
            let continuation_light: &[u8] =
                b"the cat sat on the mat and then it ran to see an old dog who was far too shy \
now the cat sat on the mat again and the dog ran to see the old cat by the mat";
            let (continuation_whole, _, uninterrupted_deepest, _) =
                run_species_observed(founded, 0, 0, continuation_light);
            let (interior, phases, deepest, resumed_deposit) =
                run_species_observed(founded, 0, 1, continuation_light);
            assert_eq!(
                split, whole,
                "split and whole carriage are one construction"
            );
            assert_eq!(
                interior, continuation_whole,
                "the descending stroke seam preserves one unfinished atom exactly"
            );
            assert_eq!(
                phases, 0xff,
                "the gauge lands before and after every perceive/path afferent/efferent/unwind face"
            );
            assert_eq!(
                deepest, uninterrupted_deepest,
                "one installment crosses the same deepest enclosure as uninterrupted carriage"
            );
            assert!(
                deepest > 4,
                "the bounded initial reservation is not a ceiling on the live construction"
            );
            assert!(
                resumed_deposit,
                "an efferent seam stands exactly one move before a later deed deposit"
            );
            assert!(whole.3.total() > 0, "the shared stroke emits felt terms");
            assert!(
                whole.1.iter().any(|&word| word != 0),
                "the complete carrier/K row stands"
            );
            assert!(
                whole.0.iter().any(|&word| word != 0),
                "the lineage's OWN construction stands"
            );
        }
    }

    #[test]
    fn malformed_continuation_rows_are_rejected_before_mutation() {
        const DEPTH: usize = 4;
        let live_brick = manifold::atom_node(boundary::difference_word(b'z' as u32, b'a' as u32));
        assert_ne!(live_brick.len, 0);

        let (standing, owns, carrier, bytes, radiation, stroke) = active_founded_fixture();
        let continuation = manifold::carrier_continuation_base(DEPTH);

        {
            let mut owns = owns.clone();
            let mut carriers = carrier.clone();
            let mut radiation = radiation.clone();
            carriers[continuation + manifold::CARRIER_CONTINUATION_PHASE] =
                manifold::CONTINUATION_PATH_UNWIND + 1;
            assert!(!manifold::carried_frame_is_canonical(&carriers));
            assert_founded_rejected_without_mutation(
                &standing,
                &mut owns,
                &mut carriers,
                &bytes,
                &mut radiation,
                stroke,
                "an unknown continuation phase is rejected, never cleared",
            );
        }

        {
            let mut owns = owns.clone();
            let mut carriers = carrier.clone();
            let mut radiation = radiation.clone();
            clear_test_deferred(&mut carriers, DEPTH);
            carriers[continuation + manifold::CARRIER_CONTINUATION_PHASE] =
                manifold::CONTINUATION_PERCEIVE_AFFERENT;
            carriers[continuation + manifold::CARRIER_CONTINUATION_DEPTH_LO] = 0;
            carriers[continuation + manifold::CARRIER_CONTINUATION_DEPTH_HI] = 0;
            store_test_node(
                &mut carriers,
                continuation + manifold::CARRIER_CONTINUATION_BRICK,
                live_brick,
            );
            assert!(!manifold::carried_frame_is_canonical(&carriers));
            assert_founded_rejected_without_mutation(
                &standing,
                &mut owns,
                &mut carriers,
                &bytes,
                &mut radiation,
                stroke,
                "an afferent continuation cannot carry a live brick at depth zero",
            );
        }

        {
            let mut owns = owns.clone();
            let mut carriers = carrier.clone();
            let mut radiation = radiation.clone();
            clear_test_deferred(&mut carriers, DEPTH);
            carriers[continuation + manifold::CARRIER_CONTINUATION_PHASE] =
                manifold::CONTINUATION_PERCEIVE_UNWIND;
            carriers[continuation + manifold::CARRIER_CONTINUATION_DEPTH_LO] = 1;
            carriers[continuation + manifold::CARRIER_CONTINUATION_DEPTH_HI] = 0;
            store_test_node(
                &mut carriers,
                continuation + manifold::CARRIER_CONTINUATION_BRICK,
                live_brick,
            );
            assert!(!manifold::carried_frame_is_canonical(&carriers));
            assert_founded_rejected_without_mutation(
                &standing,
                &mut owns,
                &mut carriers,
                &bytes,
                &mut radiation,
                stroke,
                "an unwind continuation cannot carry a live current brick",
            );
        }

        {
            let mut owns = owns.clone();
            let mut carriers = carrier.clone();
            let mut radiation = radiation.clone();
            clear_test_deferred(&mut carriers, DEPTH);
            carriers[continuation + manifold::CARRIER_CONTINUATION_PHASE] =
                manifold::CONTINUATION_PERCEIVE_AFFERENT;
            carriers[continuation + manifold::CARRIER_CONTINUATION_DEPTH_LO] = 1;
            carriers[continuation + manifold::CARRIER_CONTINUATION_DEPTH_HI] = 0;
            store_test_node(
                &mut carriers,
                continuation + manifold::CARRIER_CONTINUATION_BRICK,
                live_brick,
            );
            store_test_node(
                &mut carriers,
                manifold::carrier_deferred_base(DEPTH, 0),
                live_brick,
            );
            assert!(!manifold::carried_frame_is_canonical(&carriers));
            assert_founded_rejected_without_mutation(
                &standing,
                &mut owns,
                &mut carriers,
                &bytes,
                &mut radiation,
                stroke,
                "deferred slot zero is unreachable and must remain empty",
            );
        }

        {
            let mut owns = owns.clone();
            let mut carriers = carrier.clone();
            let mut radiation = radiation.clone();
            clear_test_deferred(&mut carriers, DEPTH);
            carriers[continuation + manifold::CARRIER_CONTINUATION_PHASE] =
                manifold::CONTINUATION_PERCEIVE_AFFERENT;
            carriers[continuation + manifold::CARRIER_CONTINUATION_DEPTH_LO] = 1;
            carriers[continuation + manifold::CARRIER_CONTINUATION_DEPTH_HI] = 0;
            store_test_node(
                &mut carriers,
                continuation + manifold::CARRIER_CONTINUATION_BRICK,
                live_brick,
            );
            store_test_node(
                &mut carriers,
                manifold::carrier_deferred_base(DEPTH, 1),
                live_brick,
            );
            assert!(!manifold::carried_frame_is_canonical(&carriers));
            assert_founded_rejected_without_mutation(
                &standing,
                &mut owns,
                &mut carriers,
                &bytes,
                &mut radiation,
                stroke,
                "a deferred sibling cannot stand at or above the active depth",
            );
        }
    }

    #[test]
    fn active_cursor_and_partial_radiation_are_rejected_before_mutation() {
        const DEPTH: usize = 4;
        let (standing, owns, carrier, bytes, radiation, stroke) = active_founded_fixture();
        let continuation = manifold::carrier_continuation_base(DEPTH);

        {
            let mut owns = owns.clone();
            let mut carriers = carrier.clone();
            let mut radiation = radiation.clone();
            carriers[manifold::CARRIER_CURSOR_LO] = stroke.byte_count as u64 as u32;
            carriers[manifold::CARRIER_CURSOR_HI] = ((stroke.byte_count as u64) >> 32) as u32;
            assert!(
                manifold::carried_frame_is_canonical(&carriers),
                "cursor range is contextual to the delivered light, not carrier shape"
            );
            assert_founded_rejected_without_mutation(
                &standing,
                &mut owns,
                &mut carriers,
                &bytes,
                &mut radiation,
                stroke,
                "an active continuation cannot name the light end as its unfinished atom",
            );
        }

        {
            let mut owns = owns.clone();
            let mut carriers = carrier.clone();
            let mut radiation = radiation.clone();
            clear_test_deferred(&mut carriers, DEPTH);
            carriers[continuation + manifold::CARRIER_CONTINUATION_PHASE] =
                manifold::CONTINUATION_WORD_PATH;
            carriers[continuation + manifold::CARRIER_CONTINUATION_DEPTH_LO] = 0;
            carriers[continuation + manifold::CARRIER_CONTINUATION_DEPTH_HI] = 0;
            carriers[continuation + manifold::CARRIER_CONTINUATION_BRICK
                ..continuation + manifold::CARRIER_CONTINUATION_WORDS]
                .fill(0);
            assert!(manifold::carried_frame_is_canonical(&carriers));

            let cursor = carriers[manifold::CARRIER_CURSOR_LO] as u64
                | ((carriers[manifold::CARRIER_CURSOR_HI] as u64) << 32);
            let atom = (cursor - stroke.worldline_base) as usize;
            let row = atom * manifold::RADIATION_WORDS;
            radiation[row..row + manifold::RADIATION_WORDS].fill(0);
            radiation[row + manifold::RADIATION_FLAGS] = manifold::RADIATION_FOLD;
            let layout = prove_layout::<true, false>(
                standing.len(),
                owns.len(),
                WordSpan::new(0, owns.len()),
                carriers.len(),
                WordSpan::new(0, carriers.len()),
                bytes.len(),
                radiation.len(),
                WordSpan::new(0, radiation.len()),
                true,
                0,
                WordSpan::empty(),
                false,
                stroke,
            )
            .expect("the partial-radiation fixture has one formed layout");
            assert!(
                active_radiation_is_canonical(&radiation, &carriers, layout, stroke),
                "WORD_PATH admits exactly its canonical FOLD-only partial face"
            );
            radiation[row + manifold::RADIATION_FLAGS] =
                manifold::RADIATION_FOLD | manifold::RADIATION_STEP;
            assert_founded_rejected_without_mutation(
                &standing,
                &mut owns,
                &mut carriers,
                &bytes,
                &mut radiation,
                stroke,
                "WORD_PATH cannot resume through a malformed stepped partial radiation face",
            );
        }
    }

    #[test]
    fn the_checked_carriage_mouth_rejects_malformed_rows_before_mutation() {
        const AXIS: usize = 8;
        const DEPTH: usize = 4;
        let raw = b"abcd";
        let bytes = packed(raw);
        let stroke = LineageStroke::dense(
            AXIS as i64,
            AXIS * AXIS,
            0,
            raw.len(),
            raw[0] as u32,
            raw[1] as u32,
            0,
            0,
            137,
        );
        let mut standing = std::vec![0u32; AXIS * AXIS * FORM_WORDS];
        let mut owns = std::vec![0u32; standing.len()];
        let mut carriers = std::vec![0u32; manifold::carrier_row_words(DEPTH)];

        standing[FORM_WORDS - 1] = 1 << 31;
        let owns_before = owns.clone();
        let carriers_before = carriers.clone();
        assert_eq!(
            carry_dense_stroke::<HostWordSeam>(
                &standing,
                &mut owns,
                WordSpan::new(0, AXIS * AXIS * FORM_WORDS),
                &mut carriers,
                WordSpan::new(0, manifold::carrier_row_words(DEPTH)),
                &bytes,
                stroke,
            ),
            None,
            "a malformed compact standing row cannot enter the checked stroke",
        );
        assert_eq!(owns, owns_before);
        assert_eq!(carriers, carriers_before);

        standing.fill(0);
        carriers[manifold::CARRIER_CHANNEL + 4 * manifold::COG_WORDS] = 1;
        let carriers_before = carriers.clone();
        assert_eq!(
            carry_dense_stroke::<HostWordSeam>(
                &standing,
                &mut owns,
                WordSpan::new(0, AXIS * AXIS * FORM_WORDS),
                &mut carriers,
                WordSpan::new(0, manifold::carrier_row_words(DEPTH)),
                &bytes,
                stroke,
            ),
            None,
            "a zero-cursor carrier cannot smuggle a stale formed K into genesis",
        );
        assert_eq!(owns, owns_before);
        assert_eq!(carriers, carriers_before);
    }

    #[test]
    fn nonzero_spans_leave_every_prefix_and_suffix_canary_untouched() {
        const AXIS: usize = 8;
        const DEPTH: usize = 4;
        const CANARY: u32 = 0xa5c3_7e19;
        const OWN_BASE: usize = 11;
        const CARRIER_BASE: usize = 13;
        const RADIATION_BASE: usize = 17;
        const TAIL: usize = 19;

        let raw = b"aabccddeeffghij";
        let bytes = packed(raw);
        let standing = std::vec![0u32; AXIS * AXIS * FORM_WORDS];
        let own_len = AXIS * AXIS * manifold::OWN_CELL_WORDS;
        let carrier_len = manifold::carrier_row_words(DEPTH);
        let radiation_len = raw.len() * manifold::RADIATION_WORDS;
        let mut owns = std::vec![CANARY; OWN_BASE + own_len + TAIL];
        let mut carriers = std::vec![CANARY; CARRIER_BASE + carrier_len + TAIL];
        let mut radiation = std::vec![CANARY; RADIATION_BASE + radiation_len + TAIL];
        owns[OWN_BASE..OWN_BASE + own_len].fill(0);
        carriers[CARRIER_BASE..CARRIER_BASE + carrier_len].fill(0);
        radiation[RADIATION_BASE..RADIATION_BASE + radiation_len].fill(0);

        let result = carry_founded_stroke::<HostWordSeam>(
            &standing,
            &mut owns,
            WordSpan::new(OWN_BASE, own_len),
            &mut carriers,
            WordSpan::new(CARRIER_BASE, carrier_len),
            &bytes,
            &mut radiation,
            WordSpan::new(RADIATION_BASE, radiation_len),
            LineageStroke::founded(
                AXIS as i64,
                AXIS as i64,
                AXIS * AXIS,
                AXIS * AXIS,
                0,
                raw.len(),
                raw[0] as u32,
                raw[1] as u32,
                0,
                0,
                137,
                manifold::RADIATION_WORDS,
            ),
        )
        .expect("the nonzero-base carriage is formed");
        assert_eq!(result.cursor, raw.len() as u64);

        let zero_base = run_species(true, 0);
        assert_eq!(
            &owns[OWN_BASE..OWN_BASE + own_len],
            zero_base.0.as_slice(),
            "the nonzero OWN span carries the exact base-zero construction"
        );
        assert_eq!(
            &carriers[CARRIER_BASE..CARRIER_BASE + carrier_len],
            zero_base.1.as_slice(),
            "the nonzero carrier span carries the exact base-zero construction"
        );
        assert_eq!(
            &radiation[RADIATION_BASE..RADIATION_BASE + radiation_len],
            zero_base.2.as_slice(),
            "the nonzero radiation span carries the exact base-zero construction"
        );
        assert_eq!(
            result.terms, zero_base.3,
            "term publication is independent of substrate base"
        );

        assert!(owns[..OWN_BASE].iter().all(|&word| word == CANARY));
        assert!(owns[OWN_BASE + own_len..]
            .iter()
            .all(|&word| word == CANARY));
        assert!(carriers[..CARRIER_BASE].iter().all(|&word| word == CANARY));
        assert!(carriers[CARRIER_BASE + carrier_len..]
            .iter()
            .all(|&word| word == CANARY));
        assert!(radiation[..RADIATION_BASE]
            .iter()
            .all(|&word| word == CANARY));
        assert!(radiation[RADIATION_BASE + radiation_len..]
            .iter()
            .all(|&word| word == CANARY));
    }
}
