//! The eta-zero atlas as a library: bands, lineages, relations and verification, parameterized
//! by **where the jets come from** and owning everything else.
//!
//! A nontrivial zero of zeta is a winding. The image of a receiver box boundary under eta
//! winds around the origin once per zero inside; a box symmetric about the critical line that
//! holds exactly one zero holds it on the line, because reflection carries zeros to zeros and
//! fixes only that line. Nothing here is a float; every coordinate is a rational interval and
//! every certificate is exact.
//!
//! Two apparatus can supply the boundary jets: the serial evaluator in exact_analysis, and a
//! resident one that forms the O(N) head on a card and hands it to eta_evaluate_jet_with_head.
//! The atlas they produce has one schema and one verifier, because certification, winding and
//! refinement live here and not in either apparatus.
//!
//! Refinement is transport along the cut, not a rebuild of the box. A zero-bearing band is
//! located by splitting it in height. The children share the parent's bottom and top edges,
//! each keeps its half of the certified sides, and the only new boundary is the cut, certified
//! once and traversed in opposite directions by the two children.

mod atlas;
mod core;
mod saddle;
mod verify;

use std::fs;
use std::path::Path;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, mpsc};
use std::thread;
use std::time::Instant;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};

use crate::exact::{Rat, integer, rat};
use crate::exact_analysis::{
    BoundarySegmentReceipt, ComplexInterval, ComplexReceiverBox, EtaCurrentReceipt,
    ExactSeriesConfig, HeadJet, RatComplex, RatInterval, WindingReceipt,
    derive_euler_maclaurin_start, eta_evaluate, eta_evaluate_jet_with_head, eta_partial_current,
    eta_second_derivative_bound, interval_common_continued_fraction, polygon_winding,
    zeta_derivative_bound_uniform, zeta_evaluate_jet2_with_head,
};

pub const ATLAS_SCHEMA: &str = "laboratory.holonic-eta-ratio-atlas.v2";

pub(crate) use atlas::*;
pub(crate) use verify::*;

pub use atlas::*;
pub use core::*;
pub use saddle::*;
pub use verify::*;
