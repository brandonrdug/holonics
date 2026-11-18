//! **The strand's triads, on the card.** The words pointed at a tick's triads' carriers; the pair's, the circle's and the triad's
//! launches stand with the contact's (`hnn/contact.rs`), and the host's strand is `crates/engine/src/carry.rs`, whose first lines state
//! the equations, the kind and the Lean and atlas owners. THE_ENGINE §3 lists each kernel beside the phase it serves, and the host is
//! the reference these bits are read against (`athena parity`).

#[allow(unused_imports)]
use crate::hnn::field::*;
#[allow(unused_imports)]
use core::ffi::c_void;
#[allow(unused_imports)]
use std::time::Instant;
#[allow(unused_imports)]
use holonics_engine::field::{band_bits, landmarks_of, BlankClocks, CarryGates, Constitution, Declaration, ReadLogits, Realization, HeldRows, NearOffsets, RealizationCounters, RowCurrent, Region, Scale, TickRead, NEAR, SHARE_BITS, STATE_BITS};
#[allow(unused_imports)]
use holonics_engine::field::{level_cut, level_section, PACE_BITS};
#[allow(unused_imports)]
use holonics_engine::field::{TowerError, TowerFace, MATERIAL_BITS};
#[allow(unused_imports)]
use crate::cuda::{Dim3, Module};
#[allow(unused_imports)]
use crate::hnn::card::{Card, CardBuffer, CardError};

/// [theory, November 12; the triad record §4] Point the words at a tick's triads' carriers (`abg`, `p`, `c^T`), none where the field has no triads.
pub(crate) fn set_triads(w: &mut Words, tick: &Tick) {
    (w.pabg, w.ptp, w.pct) = (held_at(&tick.pabg), held_at(&tick.ptp), held_at(&tick.pct));
}
