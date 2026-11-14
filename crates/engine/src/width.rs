//! The engine's width (C5 of #603: cut from `field.rs` by object, each item's text as it stood but for its visibility).

#[allow(unused_imports)]
use crate::field::*;
#[allow(unused_imports)]
use crate::inherited::tower::{affine, covector, deposit_step, div_nearest, exp_series, face_code, fewer_bits_weighed, fit32, fit64, half_turn, on_step_grain, outer_sum, ratio_adjoint, ratio_to_power, reach, refuse, release, toward, transposed, weighed_code, Result, TowerError, TowerFace, FACE_BITS, FIRST_RATE, MATERIAL_BITS, MOVE_BITS, SECOND_RATE};
#[allow(unused_imports)]
use crate::inherited::keyed_modes::{ln2_face, log2_face, Exponential};
#[allow(unused_imports)]
use rayon::prelude::*;

/// [agent-inferred, November 1] **A term's share of its row's mass** on `2^(−63)` (§14.11): formed
/// once, by one division of the exact series, for the return; the declared crossing into the step,
/// whose own release is to the material's grain.
pub const SHARE_BITS: u32 = 63;

/// A key's return past its 128-bit carrier, refused on the host and the card alike.
pub(crate) const KEY_RETURN: &str = "a contact's key return past its 128-bit carrier";

/// The contact covector's grain, `2^(−40)` (`δz` and `δs`).
pub(crate) const CONTACT_BITS: u32 = 40;

/// A face carried as a site's state, each class's share on `2^(−16)` ([`shares`]); its opening
/// `Σ_a w_a E(a)` releases the shares' grain to the encoding's own.
pub const STATE_BITS: u32 = 16;
