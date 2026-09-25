//! **Holonic Compression: a navigator family against terrain, its kernel and its cokernel.**
//!
//! [definition] Rebuild step 3 (#145): **compression is intelligence is navigation**
//! ([the line](../../../../docs/plans/THE_REBUILD.md#the-line-the-rebuild-serves)). Terrain is
//! whatever is present for a navigator to meet; Holonic Compression couples a navigator's
//! resonating modes with it, and a compression is a codec pivot carrying its decoder. The law is
//! stated in Lean `Compression/Core` and realized here in four parts:
//!
//! - [`face_map`]: the face map `F x (ρ, w) = ρ(T_w x)` of a navigator family against terrain and
//!   an admitted receiver family. Its **kernel** is the relevance kernel, computed by the
//!   blind-subspace recursion and stable by horizon `dim X − 1`; the kernel quotient is
//!   **retention**, the coarsest lawful retention, and the navigators run on it. Its **cokernel**
//!   is the residual the navigators' image does not reach on a declared request set, relative to
//!   that set's horizon; a face is reachable exactly when its cokernel class is zero.
//! - [`resonance`]: the unique `C`-orthogonal split of a drive against a constitution's modes at
//!   `λ = ω²` into the resonating part (RIDE: zero effort, the exchange law) and the emanating part
//!   (FOUND: nonzero effort, whose work form `λ S_C(e) − S_K(e)` is exact over ℚ and can be zero).
//! - [`cost`]: a navigator codec's cost `Kt = |p| + ⌈log₂ t⌉`, every bit of `|p|` written by an
//!   actual code against a declared codec family, compared with the literal by the integer test
//!   `Kt < ℓ`; a partial pivot adds the residual faces it founds as patches.
//! - [`keys`]: locating keys. The consistent keys of a menu of pair contacts are the fibre of the
//!   loop-closure map over the boundary images at the menu's ports; each added loop only shrinks
//!   it, and the key is located only up to the machine's gauge.
//!
//! | Lean `Compression/Core` | Rust |
//! |---|---|
//! | `FaceMap.faceMap`, `causalSignature_eq_faceMap` | [`FaceMap`] |
//! | `FaceMap.horizonBlind`, `mem_horizonBlind_iff`, `horizonBlind_stable_forever`, `ker_faceMap_eq_iInf_horizonBlind`, `exists_stable_le_finrank_pred`, `Shift.horizon_sharp` | [`FaceMap::new`], [`FaceMap::blind`], [`FaceMap::stable_at`] |
//! | `FaceMap.ker_faceMap_eq_relevanceKernel`, `horizonBlind_finrank_pred_eq_ker`, `horizonBlind_eq_ker_of_le` | [`FaceMap::kernel`] |
//! | `FaceMap.kernelQuotient_is_coarsest_retention`, `kernelQuotient_eq_iff_futureAgreement`, `kernelReceiverQuotient` | [`FaceMap::quotient`], [`Retention`] |
//! | `FaceMap.ker_faceMap_invariant`, `descendedNavigator`, `kernelHistoryCompression`, `kernelClass_after_word` | [`Retention::navigator`], [`Retention::transport_word`], [`Retention::face`] |
//! | `FaceMap.horizonFaceMap`, `ker_horizonFaceMap`, `ker_horizonFaceMap_finrank_pred_eq_relevanceKernel`, `rank_nullity_ledger`, `finrank_faces`, `cokernel_ledger` | [`FaceMap::at_horizon`], [`FiniteFaceMap::ledger`], [`FaceLedger`] |
//! | `FaceMap.exact_sequence`, `reachable_iff_cokernelClass_zero`, `reachable_iff_cocycles_vanish` | [`FiniteFaceMap::cokernel`], [`Cokernel`], [`FiniteFaceMap::reachable`] |
//! | `FaceMap.Ramp.*` | `face_map` tests |
//! | `Resonance.modeSpace`, `emanationSpace`, `split_exists_unique`, `split_orthogonal` | [`resonance_split`], [`ResonanceSplit`] |
//! | `Resonance.effort_split`, `emanating_effort_eq_zero_iff`, `reactive_split` | [`ResonanceSplit::effort_amplitude`], [`ResonanceSplit::rides`], [`ResonanceSplit::work`] |
//! | `Resonance.holdingEffort_newton`, `hasDerivAt_modeEnergy`, `work_ledger`, `resonant_drive_rides`, `emanating_drive_needs_effort`, `founded_mode_energy_pos`, `clamp_witness`, `work_witness` | `resonance` tests, at rational clock phases |
//! | `Cost.NavigatorCodec`, `NavigatorCodec.decode`, `decode_succ`, `decode_take`, `Regenerates` | [`NavigatorCodec`] |
//! | `Cost.CodecFamily`, `CodecFamily.describe`, `describe_length`, `readIndex_describe`, `ofDescription_describe`, `describe_injective`, `readField_length`, `ofDescription_length`, `CodecFamily.release`, `CodecPivot.release_code` | [`CodecFamily`], [`NavigatorCodec::description`], [`CodecFamily::codec_of`], [`CodecFamily::release`] |
//! | `Cost.literalCode`, `literalBits`, `literalCode_length`, `readLiteral`, `readLiteral_literalCode` | [`Alphabet::literal`], [`Alphabet::read_literal`], [`literal_bits`] |
//! | `Cost.CodecPivot`, `CodecPivot.kt`, `kt_eq`, `CodecPivot.PaysOff`, `CodecPivot.paysOff_iff_code_shorter` | [`CodecPivot`], [`CompressionCost::pays_off`] |
//! | `Cost.foundedFaces`, `foundedFaces_eq_nil_iff`, `CodecFamily.partialCode`, `CodecFamily.partialCode_length`, `CodecFamily.partialRelease`, `CodecFamily.partialRelease_partialCode` | [`NavigatorCodec::partial_pivot`], [`CodecFamily::release`] |
//! | `Cost.oneBit`, `oneBit_descriptionBits`, `alternatorIndex`, `alternator_regenerates`, `alternator_pays_off_iff`, `alternator_pays_off_iff_pow`, `alternation_witnesses`, `no_one_bit_navigator_regenerates`, `outside_material_stays_literal`, `one_founded_face_pays_off` | `cost` tests, computed from the codec |
//! | `Keys.Loop`, `Loop.Closes`, `Loop.closes_iff`, `closureMap`, `fibre`, `Observed`, `truth_mem_fibre`, `fibre_eq_bombe` | [`Loop`], [`Menu`], [`PortImages`] |
//! | `Keys.fibre_cons`, `fibre_append_subset`, `fibre_depends_only_on_port_images` | [`Menu::extended`], [`Menu::candidates`] and `keys` tests |
//! | `Keys.Gauge`, `Gauge.act`, `Gauge.closes_iff`, `Gauge.closureMap_act`, `fibre_gauge_invariant`, `iterate_mem_fibre_iff`, `fibre_gauge_truth`, `fibre_eq_orbit` | [`Gauge`], `keys` tests |
//! | `Keys.Machine.*`, `Machine.rotorGauge` | [`ReflectorMachine`], [`ReflectorMachine::gauge`], `keys` tests |
//! | `HNN/Keys.propagation_eq_edge_fibre` | [`Edge`], [`Menu::propagate`], [`Propagation`] |
//!
//! [definition; agent-inferred] Where this owner departs from the Lean it says so: [`FaceMap`]
//! admits receivers of different face extents (Lean's face space `#requests · dim V` is the
//! uniform case), and [`Gauge::new`] checks covariance at declared keys, where Lean's `Gauge`
//! carries it for every key. The Perron navigator's code of a walk (`Cost.perron_walk_code_length`,
//! `two_regular_perron_code`) and the two-candidate posterior reading
//! (`Cost.posterior_prefers_iff_pays_off`) have no Rust consumer here; the pay-off is the integer
//! comparison of two codes.
//!
//! [open] The owed scope is Lean's, #62: the integral cokernel ledger (the reachability join over ℤ
//! is `HolonicsResearch/Landmarks/IntegralCokernel.reachableOnlyInMultiple_iff`, which this ℚ owner
//! does not realize), the dissipative steady response `(K − ω²C + iωD)⁻¹` and its work per cycle,
//! and key inference over continuous navigator configurations with the joint description of key
//! and gauge.

pub mod cost;
pub mod face_map;
pub mod keys;
pub mod landmark;
pub mod resonance;

pub use cost::{
    Alphabet, CodecFamily, CodecPivot, CompressionCost, NavigatorCodec, PivotForm, literal_bits,
};
pub use face_map::{Cokernel, FaceLedger, FaceMap, FiniteFaceMap, Request, Retention};
pub use keys::{Candidate, Edge, Gauge, Loop, Menu, PortImages, Propagation, ReflectorMachine};
pub use resonance::{ResonanceSplit, resonance_split};

use thiserror::Error;

use crate::holon::contact::menu::MenuError;
use crate::holon::parametron::ParametronError;
use crate::ratio::linear::ExactLinearError;
use crate::receiver::standing::StandingRefusal;

/// Every refusal of a compression law. Bad input is a typed return, never a panic.
#[derive(Debug, Error, PartialEq)]
pub enum CompressionError {
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Standing(#[from] StandingRefusal),
    #[error(transparent)]
    Parametron(#[from] ParametronError),
    #[error(transparent)]
    Menu(#[from] MenuError),
    #[error("a face map needs at least one admitted receiver")]
    EmptyReceiverFamily,
    #[error("{what}: expected extent {expected}, found {found}")]
    Extent {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("the relevance kernel is not carried by navigator {navigator}")]
    KernelNotInvariant { navigator: usize },
    #[error("receiver {receiver} does not factor through the kernel quotient")]
    ReceiverNotFactored { receiver: usize },
    #[error("the capacity is singular: a node without capacitance admits no unique split")]
    SingularCapacity,
    #[error("the codec does not regenerate its material of length {length}")]
    NotRegenerated { length: usize },
    #[error("a codec family needs at least one member in its {what}")]
    EmptyFamily { what: &'static str },
    #[error("symbol {index} repeats an earlier symbol of the alphabet")]
    RepeatedSymbol { index: usize },
    #[error("a symbol lies outside the declared alphabet")]
    SymbolOutside,
    #[error("index {index} lies outside a population of {population}")]
    IndexOutside { index: usize, population: usize },
    #[error("the code ends before its decoder does")]
    TruncatedCode,
    #[error("the code continues after its decoder ends")]
    TrailingCode,
    #[error("loop port {port} lies outside a menu of {ports} ports")]
    LoopPort { port: usize, ports: usize },
    #[error("the candidate declares no boundary image at loop port {port}")]
    MissingImage { port: usize },
    #[error("the boundary images repeat at port {port}")]
    NotInjective { port: usize },
    #[error("loop {loop_index} is not conjugated by the gauge's boundary turn at key {key_index}")]
    NotCovariant { loop_index: usize, key_index: usize },
    #[error("edge {edge_index} is not conjugated by the gauge's boundary turn at key {key_index}")]
    EdgeNotCovariant { edge_index: usize, key_index: usize },
    #[error(
        "the stage of edge {edge} at key {key_index} is not an involution, so it has no reverse"
    )]
    StageNotInvolution { edge: usize, key_index: usize },
    #[error("{ports} ports take too many images at {at} menu ports: past the ceiling of {ceiling}")]
    ImageFamilyCeiling {
        ports: usize,
        at: usize,
        ceiling: usize,
    },
}
