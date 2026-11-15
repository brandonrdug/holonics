//! The card realization's carry (C5 of #603: cut from `hnn/field.rs` by object, each item's text as it stood but for its visibility).

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
