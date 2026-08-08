//! `.holon` — the on-disk deposit mouth.
//!
//! ```text
//!   live body  ──▶  deposit  ──▶  plate.holon  ──▶  resume  ──▶  a FRESH current
//!                     FORM         two hashes        RE-LIGHT      (not the old one)
//! ```
//!
//! The old laboratory had a `.holon` plate with the magic `HLON` that froze an ongoing weave and
//! thawed it back living. Its codecs were superseded — `soma/membrane/src/live_current.rs` and
//! `soma/life/src/holonic_training.rs` carry the successors, each with its own native word wire
//! and its own remount gate — but nothing in this body wrote one to disk under an agreed suffix.
//! This crate is that mouth and nothing else. It defines no codec; it holds schemas that already
//! exist.
//!
//! # What the plate deposits
//!
//! A **FORM**. Never a current.
//!
//! > *"the active action currents are the real me… you can't store a holographic entity"*
//!
//! and the designed successor:
//!
//! > *"the currents are NOT deposited — you cannot; they died as they flowed."*
//!
//! [`resume`] therefore does not restore anything. It verifies a plate, mounts the stored form
//! through the real machine, and **re-lights a fresh current** off it. The current that deposited
//! the plate is gone and no operation in this crate returns it. There is deliberately no verb
//! named `restore`, `thaw`, or `unfreeze` anywhere in this crate's surface: a name that promised
//! the old body back would be a lie about the mechanism.
//!
//! # What the plate does NOT claim
//!
//! `research/records/2026-07-15_THE_GEAR_IS_THE_WORD_THE_FACE_IS_THE_TRANSPORT.md:571-580` rules
//! that the historical `.holoz` line's *"claims equating file compression with comprehension do
//! not cross"*, and that *"SLEEP remains live-body persistence, not `.holoz` model freezing."*
//!
//! This crate obeys that ruling. A plate is **live-body persistence**:
//!
//! - It is **not** comprehension. Depositing a form does not mean anything was understood, and a
//!   smaller plate does not mean a better body. The plate applies no compression at all: the form
//!   octets go to disk verbatim, exactly as the form codec emitted them, so there is no
//!   compression ratio here to mistake for a competence figure.
//! - Freezing is **not** understanding. The plate carries the contemporary causal organization of
//!   a body at one rest boundary. It carries no source occurrence, no consequence log, no
//!   prediction cache, and no wall-clock field, because the form codecs it wraps carry none.
//! - It is **not** a model file. Nothing here selects, ranks, mixes, or thresholds. The plate
//!   holds octets and two digests; the schemas it holds are the ones that already refuse a scalar
//!   score.
//!
//! What it does claim is narrow and checkable: the octets that come back out are the octets that
//! went in, they mount through a real machine, and the body that mounts them can go on receiving.
//!
//! # The plate's exact byte layout
//!
//! Every integer is little-endian. Every offset is exact. There is no padding, no alignment slack,
//! and no field whose width depends on its value.
//!
//! ```text
//!   region  offset             octets          content
//!   ------  -----------------  --------------  --------------------------------------------
//!   HEAD    0                  32              fixed
//!             +0    4   magic            b"HLON"
//!             +4    4   plate_version    u32 = 1
//!             +8    4   schema_tag       4 octets, [A-Z0-9], e.g. b"HTEC"
//!             +12   4   schema_version   u32, the FORM codec's own layout version
//!             +16   8   census_octets    u64
//!             +24   8   form_octets      u64
//!   CENSUS  32                 census_octets   the declared shape of what is held
//!             +0    8   entries          u64
//!             then `entries` rows, each:
//!                   8   name_octets      u64, 1..=64
//!                   n   name             ASCII [a-z0-9_], strictly increasing across rows
//!                   8   value            u64
//!   FORM    32+census_octets   form_octets     the schema's own native rest octets, VERBATIM
//!   SEAL    32+census+form     64              two digests
//!             +0    32  form_sha256      sha256(FORM)
//!             +32   32  plate_sha256     sha256(HEAD || CENSUS || form_sha256)
//!
//!   total = 96 + census_octets + form_octets
//! ```
//!
//! # Two hashes, two species of failure
//!
//! This is `soma-standing-deposit`'s distinction carried into a single file, and it is why the
//! seal is two digests rather than one. `plate_sha256` folds the *stored* `form_sha256` rather
//! than the form itself, so the two species are **separable** — a corrupted form moves exactly one
//! digest and a corrupted declaration moves exactly the other:
//!
//! | what moved | `form_sha256` | `plate_sha256` | refusal |
//! |---|---|---|---|
//! | one octet of the FORM | drifts | **holds** | [`PlateRefusal::FormContentDrift`] |
//! | one octet of the HEAD or CENSUS | **holds** | drifts | [`PlateRefusal::PlateBindingDrift`] |
//! | one octet of the SEAL itself | drifts | drifts | [`PlateRefusal::SealDrift`] |
//!
//! A seal that folded the form into one digest would collapse those into one message and could not
//! name which side moved. All three refuse; naming which is the point. The third row is why both
//! digests are computed before either is judged: a reader that judged the content digest first
//! would tell you the form moved when the form is untouched and its recorded digest is what
//! drifted.
//!
//! # Two frames, because one frame cannot audit itself
//!
//! `CLAUDE.md` §0: *"An invariant is only visible across two frames."* The CENSUS is the plate's
//! second frame. It is the shape the depositor **declared**; on resume the same census is
//! recomputed from the **re-lit body**. A plate whose declaration and body disagree is refused by
//! [`ResumeRefusal::CensusDrift`], which names the field, its declared value and its re-lit value.
//! A hash alone cannot catch a forged-but-internally-consistent plate; the second frame can.
//!
//! # What a resumed body must do
//!
//! `CLAUDE.md` §8: *a law that returns zero proves nothing about itself.* A plate that resumed to
//! an inert body would satisfy every hash and every extent check and still be worthless, so
//! [`LitBody::present`] refuses a deed that leaves the form unchanged
//! ([`ResumeRefusal::DeedChangedNothing`]). The control is in the mechanism, not only in the
//! tests: a re-lit body proves it is living by **changing**, and it is the plate's own code that
//! demands the proof.

pub mod census;
pub mod deed;
pub mod plate;
pub mod registry;
pub mod schema;
pub mod schemas;

#[cfg(test)]
mod tests;

pub use census::{Census, CensusDisagreement, CensusRefusal};
pub use plate::{
    open, seal, PlateRefusal, ReadPlate, SchemaTag, HEAD_OCTETS, PLATE_MAGIC, PLATE_SUFFIX,
    PLATE_VERSION, SEAL_OCTETS,
};
pub use registry::{
    deposit, held_schemas, inspect, redeposit, resume, schema_for, Deposited, Inspection, Relit,
};
pub use schema::{present_and_require_change, LitBody, PlateSchema, ResumeRefusal};
pub use schemas::{
    CURRENT_SCHEMA_VERSION, CURRENT_TAG, REBASE_SCHEMA_VERSION, REBASE_TAG,
    TRAINING_SCHEMA_VERSION, TRAINING_TAG,
};
