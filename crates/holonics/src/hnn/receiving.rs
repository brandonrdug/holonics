//! **The receiving phases, the receiving parametron's active suffix address, and the combined
//! read at the receiver's grain.**
//!
//! [definition] A receiver reads the front crossing its ring (design (a), `receive`; "Exact
//! charts", the receiving face). [`ReceivingPhases`] names the receiving ring `R`, its first epoch
//! `e_0 = min_(g∈𝒮) dist(g, R)`, its aperture `A` (so `e_last = e_0 + A − 1` and the word evaluates
//! `e_max = e_0 + A` junction steps), its grain `L_R = ⌈1/ε_bits⌉`, derived from the receiver's
//! declared code tolerance `ε_bits` per cell (R2 M2), and the depth `D` of its landmark tree's
//! address (the landmark tree). It refuses `A` beyond the rank of the receiving ring's observability
//! over the word, and reports that rank (review C7).
//!
//! ```text
//! a_j = [x_(p+j−1), …, x_p, x_(p−1), …]_D        phase j's address: the epoch's earlier targets, then the active suffix address
//! f_j = k(a_j)/L_R + R · P_R^(τ_R) v_R(e_j)      complex logits over |A| classes, realified [Re, Im, …]
//! 2^(k_c) ≤ q(c | a_j)^(L_R) < 2^(k_c+1)         the tree face's grain exponent (integer comparisons)
//! Re f_c = n_c + k_c/L_R + ε_c,  ε_c ∈ [0, 1/L_R)   the grain cell (carry, phase class) and the fibre
//! φ^H_c = Im f_c / 2                             each class's phase, in turns
//! ```
//!
//! [definition; agent-inferred, U5] **The receiver reads the passage by epochs.** Two clocks meet
//! there. Over the passage, the source's cell clock (an unwound `navigator::Clock`, one tick a
//! cell) is crossed by the receiver's section every `A` cells: the cells between two crossings are
//! an epoch of the passage's aeon at that section, the digit clock of base `A`
//! ([`ReceivingPhases::windows`], the exposure's epochs; Lean
//! `Aeon/Clock/Epoch.{forward_epoch_is_window, mem_epoch_digitTicks}`). Inside a word, the word's
//! own unwound clock (`hnn::word::Word`, one tick a junction step) is read by the receiver at its
//! ticks `e_0 … e_last` ([`ReceivingPhases::epochs`]), the epochs of the word's aeon at its unit
//! section, which is every tick; phase `j` at word tick `e_0 + j` reads cell `p + j` of the
//! passage's epoch opening at `p`. The inferred choice: the epoch's cell span is the aeon owner's
//! reading, not a loop's stride, and the word's tick index is its clock's, disclosed as such.
//!
//! [definition; agent-inferred] **The receiving parametron's storage is the landmark tree**
//! (the landmark tree, `compression::landmark::context::Landmarks`, held in `Θ` at the receiving locus beside `R`). It
//! replaces the region table, whose laws stay in Lean (`HNN/RegionCounts`). The region
//! table is the depth-one forced case of the whole-cell emission (`|A|`-ary masses at a node; Lean
//! `Compression/Landmark/Context/Tree.depth_one_is_the_whole_cell_table`), which lives in Lean only; this tree emits the
//! cell's odometer digits, and its depth-one forced case is a product of binary KT faces at the
//! preceding cell, not the region table's `|A|`-ary face.
//! The tree is declared from the receiver ([`landmark_declaration`]): the cell emitted as its
//! odometer digits, the depth `D` (4 on campaign 1, chosen on the development cells in the landmark
//! receipt), no forced split, the field's declared population `n*` and the receiver's grain, from
//! which the owner derives its widths (the path lattice `M_p` and the β carrier `W`).
//!
//! [definition; agent-inferred] **The active suffix address** ([`ActiveAddress`]; the tower thread,
//! the suffix restriction of the source navigator's word). The last `D` cells the receiver has
//! received, newest first, `Boundary` before the passage's first cell. It is the receiving
//! parametron's own state, kept by the resident beside the tree and shifted at every ingested
//! cell. It is not the source moment's state: the word never reads it, so the moment still holds
//! `max Δ` cells and the capacity `n*` (which counts the source state the word reads) is unchanged
//! by construction. Its bits count in the resident's state bits, and the aeon collapse keeps it
//! with the tree whole (Lean `Compression/Landmark/Context/Tree.release_rule` proves that nodes deeper than `D` are
//! releasable, of which the tree founds none, and that a retention is lawful exactly when it
//! refines the causal signature; it does not prove that no shallower merge is lawful, and the
//! collapse attempts none). A pending ratio copies it at its cut, an operand like the moment's
//! counts.
//! **The address is per cell and causal**: phase `j` of the epoch opening at `p` reads the tree at
//! `a_j = [x_(p+j−1), …, x_p]` (the epoch's own earlier targets, known at compare) followed by the
//! copied suffix `[x_(p−1), …]`, truncated to `D` ([`ActiveAddress::phase`]). It equals
//! `compression::landmark::context::address(cells, p + j, D)` exactly (the test
//! `the_phase_address_is_the_trees_causal_address`), so an aperture-two epoch reads its two
//! phases at their own addresses (the located failure pooled lags one and two at one region).
//! **The epoch is read in cell order** (prequential scoring within an epoch): phase `j`'s tree face
//! is read at the standing after the epoch's earlier phases' tree deposits (their targets are known
//! at compare), on a working overlay of the nodes those deposits write
//! ([`window_faces`], over `compression::landmark::context::Landmarks::window`); the deposit then applies exactly those steps to the
//! published tree, in cell order, so the tree it publishes is the overlay's last standing plus the
//! last phase's step. The wave's part of an epoch is the one refine's, read at the standing where
//! the epoch opens: the wave's maps are deposited once an epoch, by the normal law.
//!
//! [definition; agent-inferred] **The receiving letters** (campaign 2; Lean
//! `Compression/Landmark/Context/Address`). The address register holds typed bundles, not bare cells: each earlier
//! cell's tick contributes its cell and the declared features' letters ([`Feature`], declared as a
//! [`FeatureFamily`] whose alphabets the tree reads as its `LetterFamily`), newest
//! bundle first, and the register restricts by dropping its oldest whole bundle. A letter is read
//! from the retained sufficient state before the cell it predicts: the register's reader
//! ([`LetterReader`]) keeps the clock of the rings its phase letters read (their phases
//! `λ_g mod d_g`, stepped by the selective step at every received cell, synchronized with the lift
//! point at the mount and after every re-keying, and checked against it at every ingest), reads each
//! tick's letter after the tick, and never reads it again; a pending ratio copies the register, its
//! clock included, at its cut, so each phase's letters of the epoch's known targets are read by a
//! copy of that clock (`bundle_causal`). A ring's phase class at its declared grain is read by
//! [`GrainCell::of`] of the phase in turns. A contact's letter is its owner's reading
//! ([`ContactReading`], `hnn::contact`): its lock address from its rings' whole windings since the
//! aeon's opening, which the reader keeps with the phases (every ring, so the carry-out that opens
//! the next aeon is its own), and its site kind from the constitution the reader last refreshed
//! from ([`LetterReader::refresh`], which the resident takes after each ingest: the kinds step only
//! between ingests, so the compare's copy and the ingest read one letter per tick).
//! The letters of a passage are replayed without the wave ([`clock_letters`]: the resident's clock
//! law with its key location and re-keying at each carry-out, the site kinds given per tick), the
//! development harness's letters (the development harness). The field's declared family ([`letter_family`]) is
//! the harness's choice: on the standing cut's development cells, at the contacts' horizon bounds,
//! no clock-only and no contact family coded below the constant control of its slots by its
//! description charge, so it is the cell-only family, and the register is campaign 1's.
//!
//! [definition; agent-inferred] **The combined face** (the region table's combined read, with the tree's
//! face in place of the region table's). The scored logits are the tree face's grain logits
//! (`k_c/L_R` on the real rows, zero on the imaginary rows: [`grain_logits`]) plus the wave's
//! `R P_R^(τ_R) v_R` ([`ReceivingRead::combined`]). The wave part is the refine's; the tree part
//! needs each phase's address, so it is read at **compare**, per phase
//! ([`ReceivingPhases::tree_faces`], [`ReceivingPhases::combine`]). The tree logits lie on the
//! grain, so each class's grain cell is the wave's shifted by `k_c/L_R` and its fibre is the
//! wave's. The ratio's covector on the combined face flows back through `R` alone
//! (`hnn::port::Word::pull_back`; Lean `HNN/RegionCounts.combined_face_pullback` holds for any
//! stored grain logits): the tree part is a stored face, deposited by its own law (the reached
//! comparisons' cells on their opened paths, `hnn::constitution::LandmarkStep`).
//!
//! [definition; agent-inferred] **The scored face is the receiver's population**
//! ([`receiving_population`], the primary's ruling A; THE_REBUILD U1): the population at the
//! receiving port (`receiver::population::port`) over the tree's face and the combined face at
//! ½/½, its weights read from the two families' likelihoods in Θ at the receiving locus, as a tree
//! node weighs its own face against its split, received after every cell in cell order, within an
//! epoch too ([`score`]). The wave keeps learning from the combined face's covector.
//!
//! [definition] **Exact inside, grain only at the face.** The logits are exact rationals. The grain
//! reading returns the carry `n_c`, the phase class `k_c ∈ ℤ/L_R` and the fibre `ε_c`, the
//! receiver's unresolved remainder, which is returned and never rounded (guard 15). The normalized
//! face `p̂ ∝ 2^(n + k/L_R)` lives in `ℚ(θ_R)`, `θ_R^(L_R) = 2`, and is built from the cells by the
//! ratio module's carried power (addition 4); this module stops at the cells.
//!
//! | Lean | Rust |
//! |---|---|
//! | `HNN/Ratio.face_constant_on_fibre` (the face reads only `(n, k)`; the owner's, `receiver::face`) | [`GrainCell`] |
//! | `HNN/Ratio.grain_of_tolerance` (`L_R = ⌈1/ε_bits⌉`) | [`ReceivingPhases::declare`] |
//! | `Aeon/Clock/Epoch.{forward_epoch_is_window, crossingTicks_forwardWord, mem_epoch_digitTicks, odometer_tower}` (the receiver's spans of cells are the digit clock's epochs) | [`ReceivingPhases::windows`] |
//! | `HNN/RegionCounts.{grain_face_residual, grain_code_residual}` (the grain exponent is `receiver::face::grain_exponent`'s, `grainExponent_spec`, `grain_log_iff_pow_bounds`) | [`grain_logits`] |
//! | `receiver::reception::ReceiverFace::read` with `C_S = R P_R^(τ_R) Π_R` | [`ReceivingPhases::read`] |
//! | `HNN/RegionCounts.{combinedLogits, combined_face_pullback, combined_code_pullback}` | [`ReceivingRead::combined`], [`ReceivingPhases::combine`] |
//! | `Compression/Landmark/Context/Tree.{unfounded_reads_prior, founded_tree_same_law, release_rule}` (the typed suffix address, kept whole by the collapse) | [`ActiveAddress`], [`ReceivingPhases::tree_faces`] |
//! | `Compression/Landmark/Context/LocalWeighing.two_face_prior` at `π = ½` and `Tree.{sequential_mixture, sequential_mixture_bounds}` (the two-family population is the two-face mixture stepped cell by cell, within one bit of the better face); `Population.population_mixture_enclosed` (the combined face read through its enclosure) | [`receiving_population`], [`score`] |
//! | `Compression/Landmark/Context/Address.{bundle_causal, bundle_restrict, feature_scale_square, address_descends_retention, phase_partition_finite}` (the typed bundles read from the retained clock before the cell they predict) | [`LetterReader`], [`ActiveAddress`], [`clock_letters`] |

use std::ops::Range;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive, Zero};

use crate::aeon::{ClockLift, epochs};
use crate::compression::cost::ceil_log2;
use crate::compression::landmark::context::{
    Bundle, LandmarkDeclaration, LandmarkFace, Landmarks, Letter, LetterFamily, Splits, code_length,
};
use crate::hnn::HnnError;
use crate::hnn::contact::{ContactReading, LockDeclaration, lock_address, site_kinds};
use crate::hnn::field::{ConstitutionRead, Current, Field, ReceiverDeclaration, ring_digit};
use crate::hnn::keys;
use crate::hnn::propagation::Operands;
use crate::hnn::ratio::{Face, Faces};
use crate::hnn::realization::{apply_rows, indexed};
use crate::hnn::word::Word;
use crate::navigator::Clock;
use crate::navigator::trace::SiteKind;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::exponentiated::CarriedPower;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer};
use crate::receiver::face::GrainCell;
use crate::receiver::population::{PopulationError, PortPopulation};

// -------------------------------------------------------------------------------------------
// the grain

/// [definition] **The tree face's grain logits**, realified `[k_0/L_R, 0, k_1/L_R, 0, …]` (Lean
/// `HNN/RegionCounts.grainLogits`): each class's grain exponent over the grain on its real row,
/// zero on its imaginary row.
pub fn grain_logits(face: &LandmarkFace) -> Vec<Rat> {
    let grain = BigInt::from(face.grain);
    face.exponents
        .iter()
        .flat_map(|k| [Rat::new(k.clone(), grain.clone()), Rat::zero()])
        .collect()
}

/// **The tree face at the grain**: the code length `−log₂ p̂(c)` of one class, enclosed, under the
/// face of the tree's grain logits alone, `θ^(k_c)/Σ_d θ^(k_d)` in `ℚ(θ)` (`hnn::ratio::Face`), the
/// face the combined read opens at when the wave reads zero. It is not the tree's executed face
/// `q_T(c)`, which the receiver's population weighs ([`Scored::tree`] reads that one): the two differ by the
/// grain's rounding of the exponents and the renormalization.
pub fn tree_code_length(face: &LandmarkFace, class: usize) -> Result<ExactInterval, HnnError> {
    let read = ReceivingRead::of_logits(grain_logits(face), face.grain);
    Face::of_read(&read, face.grain)?.code_length(class)
}

/// [definition] **One receiving read**: the exact realified logits `f`, each class's grain cell of
/// `Re f_c`, and each class's phase `φ^H_c = Im f_c / 2` in turns.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingRead {
    pub logits: Vec<Rat>,
    pub cells: Vec<GrainCell>,
    pub phases: Vec<Rat>,
}

impl ReceivingRead {
    /// **A read of given realified logits at a grain**: each class's real logit read at the grain
    /// with its fibre, and its imaginary logit halved into turns. The classes are read alone and run
    /// together (`hnn::realization`).
    pub fn of_logits(logits: Vec<Rat>, grain: u64) -> Self {
        let classes = logits.len() / 2;
        let cells = indexed(classes, |class| {
            Ok::<_, HnnError>(GrainCell::of(&logits[2 * class], grain))
        })
        .expect("a grain reading refuses nothing");
        let phases = logits.chunks(2).map(|pair| &pair[1] / integer(2)).collect();
        Self {
            logits,
            cells,
            phases,
        }
    }

    /// **The combined read** (module header): the wave's exact logits `R P_R^(τ_R) v_R` plus the
    /// tree face's grain logits, read at the grain. Refused when the two disagree in length or
    /// grain. The host reference and every device realization form their faces here.
    pub fn combined(wave: Vec<Rat>, tree: &LandmarkFace, grain: u64) -> Result<Self, HnnError> {
        let stored = grain_logits(tree);
        if stored.len() != wave.len() || tree.grain != grain {
            return Err(HnnError::Shape {
                what: "the tree face's grain logits against the wave's logits",
                expected: wave.len(),
                found: stored.len(),
            });
        }
        let logits = wave
            .into_iter()
            .zip(stored)
            .map(|(wave, stored)| {
                if stored.is_zero() {
                    wave
                } else {
                    wave + stored
                }
            })
            .collect();
        Ok(Self::of_logits(logits, grain))
    }
}

// -------------------------------------------------------------------------------------------
// the tree's read over an epoch on the host: the phases run together

/// **The class faces of an epoch's splits** (`LandmarkFace::of_splits` per phase): the phases read
/// alone and run together (`hnn::realization`: each reads its own splits and writes its own face).
/// The host's read over an epoch and every device realization's form their faces here.
pub fn faces_of_splits(
    declaration: &LandmarkDeclaration,
    splits: &[Splits],
    grain: u64,
) -> Result<Vec<LandmarkFace>, HnnError> {
    indexed(splits.len(), |j| {
        Ok(LandmarkFace::of_splits(declaration, &splits[j], grain)?)
    })
}

/// [definition; agent-inferred] **An epoch's splits in cell order, the phases run together** (the
/// host realization of `compression::landmark::context::Landmarks::window`): the tree builds the
/// epoch's working overlays in cell order, and each phase then reads its own overlay alone
/// (`hnn::realization`: nothing is written, so the reads commute). The quantity a card's read
/// returns.
pub fn window_splits(
    tree: &Landmarks,
    addresses: &[Vec<Letter>],
    known: &[usize],
) -> Result<Vec<Splits>, HnnError> {
    let window = tree.window(addresses, known)?;
    indexed(window.phases(), |j| Ok(window.splits(j)))
}

/// **An epoch's all-class faces in cell order** at `grain` ([`window_splits`], then
/// [`faces_of_splits`]): phase `j` at the standing after the deposits of the known earlier phases.
pub fn window_faces(
    tree: &Landmarks,
    addresses: &[Vec<Letter>],
    known: &[usize],
    grain: u64,
) -> Result<Vec<LandmarkFace>, HnnError> {
    faces_of_splits(
        tree.declaration(),
        &window_splits(tree, addresses, known)?,
        grain,
    )
}

// -------------------------------------------------------------------------------------------
// the receiving letters: the features, the HNN's letter family, the clock register and the
// active suffix address

/// [definition] **One declared feature slot of a bundle**: what a slot's letter reads from the
/// retained clock and constitution. The tree reads only the slot's alphabet
/// (`compression::landmark::context::LetterFamily`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum Feature {
    /// Ring `ring`'s phase class `⌊g·phase⌋ mod g` at its declared grain `g`.
    Phase { ring: usize, grain: u64 },
    /// Contact `contact`'s reading (`hnn::contact::ContactReading`): its lock address in the lock
    /// family at its derived bound `(P, Q)`, and its site kind.
    Contact {
        contact: usize,
        bound: LockDeclaration,
    },
}

impl Feature {
    /// **A contact's letter**, its bound derived from the field (`LockDeclaration::derived`: `Q`
    /// the greatest denominator whose first return, `q` turns of the contact's second ring, Lean
    /// `Aeon/Clock/Lock.cycle_iff_period_dvd`, is observable within the aeon, and `P` the first
    /// ring's alike; Lean `Compression/Landmark/Context/Address.lock_partition_finite`), never a
    /// literal.
    pub fn contact(field: &Field, contact: usize) -> Self {
        Feature::Contact {
            contact,
            bound: LockDeclaration::derived(field, contact),
        }
    }

    /// **The slot's finite alphabet**: `g` phase classes, or the contact's letters (its lock
    /// family's letters times the five site kinds, `hnn::contact::ContactReading::letters`).
    pub fn size(&self) -> Result<u64, HnnError> {
        match self {
            Feature::Phase { grain, .. } => Ok(*grain),
            Feature::Contact { bound, .. } => ContactReading::letters(bound),
        }
    }

    /// A contact reading's value in this slot (`hnn::contact::ContactReading::letter`).
    pub fn contact_value(&self, reading: &ContactReading) -> Result<u64, HnnError> {
        match self {
            Feature::Contact { bound, .. } => reading.letter(bound),
            Feature::Phase { .. } => Err(HnnError::Shape {
                what: "a contact slot for a contact reading",
                expected: 1,
                found: 0,
            }),
        }
    }
}

/// [definition] **The HNN's declared letter family**: the feature slots each bundle carries after
/// its cell, in order, and the tree's family of their alphabets
/// (`compression::landmark::context::LetterFamily`, which the receiver's tree is declared with).
/// The empty family is the cell-only tree (campaign 1).
#[derive(Clone, Debug, Default, PartialEq, Eq, Hash)]
pub struct FeatureFamily {
    features: Vec<Feature>,
    letters: LetterFamily,
}

impl FeatureFamily {
    /// The cell-only family.
    pub fn cells() -> Self {
        Self::default()
    }

    /// **Declare a family**: its slots' alphabets are the features' ([`Feature::size`]), refused
    /// as the tree refuses them (`LetterFamily::new`: a slot of one letter carries nothing, and the
    /// slots' product fits 32 bits).
    pub fn new(features: Vec<Feature>) -> Result<Self, HnnError> {
        let sizes = features
            .iter()
            .map(Feature::size)
            .collect::<Result<Vec<u64>, HnnError>>()?;
        Ok(Self {
            letters: LetterFamily::new(sizes)?,
            features,
        })
    }

    /// [definition; agent-inferred] **The constant-slot control of `slots` slots**: each slot reads
    /// ring 0's phase class at grain 1, one letter at every tick, over the tree's constant control
    /// (`LetterFamily::constant_control`). A development harness's control, never a declared family.
    pub fn constant_control(slots: usize) -> Self {
        Self {
            features: vec![Feature::Phase { ring: 0, grain: 1 }; slots],
            letters: LetterFamily::constant_control(slots),
        }
    }

    pub fn features(&self) -> &[Feature] {
        &self.features
    }

    /// The tree's family of the slots' alphabets.
    pub fn letters(&self) -> &LetterFamily {
        &self.letters
    }

    /// `r`, the feature slots.
    pub fn slots(&self) -> usize {
        self.features.len()
    }

    pub fn is_empty(&self) -> bool {
        self.features.is_empty()
    }

    /// Whether a slot reads a contact (its readings need the constitution's site kinds).
    pub fn reads_contacts(&self) -> bool {
        self.features
            .iter()
            .any(|feature| matches!(feature, Feature::Contact { .. }))
    }
}

/// One ring's clock law as the register reads it: its period, the field's port chart for each
/// exterior code and its lock on those ports (`hnn::field::Ring::{port, fits}`, one owner of the
/// chart) and its navigator's clock at rest (`hnn::field::Ring::clock_at`), from which the
/// register's clock restarts at an aeon's opening.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ClockRing {
    period: u64,
    ports: Vec<usize>,
    lock: Vec<bool>,
    rest: Clock,
}

/// [definition; agent-inferred] **The letters' reader** (module header, "The receiving letters"):
/// the declared family, the clock law of the rings its letters read (rings `0 ..= g_max` in carry
/// order, since a ring's step reads its predecessors' carries: Lean
/// `HNN/Moment.selective_position`; every ring when a contact is read, so the joint clock's
/// carry-out, which opens the next aeon, is the reader's own), their phases `λ_g mod d_g` and whole
/// windings since the aeon's opening at the register's cut, and each contact's site kind as the
/// constitution read at the reader's last refresh. It is the retained sufficient state the letters
/// are read from (Lean `Compression/Landmark/Context/Address.address_descends_retention`): a tick's letter is read
/// after the tick, before the cell it predicts, and nothing of the past is kept.
///
/// [definition; agent-inferred] **A contact's letter** is its owner's reading
/// (`hnn::contact::ContactReading`): its lock address from its two rings' windings since the
/// aeon's opening (`hnn::contact::lock_address` at the derived bound; the carry-out resets them,
/// as the aeon's opening moves there), and its site kind from the kinds held
/// (`hnn::contact::site_kinds`). The kinds are the constitution's at the reader's last
/// [`LetterReader::refresh`], which the resident takes after each ingest, never inside one: a
/// deposit between an epoch's cut and its ingest therefore reaches no letter of that epoch's
/// ticks, so the letters the compare reads by a copy of the register ([`ActiveAddress::phase`])
/// are the letters the register reads at the ingest, and the site kinds step only between ticks,
/// as a re-keying does (Lean `bundle_causal`: the letters already read keep their ticks' values).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LetterReader {
    family: FeatureFamily,
    rings: Vec<ClockRing>,
    /// [definition; agent-inferred, U5] Each kept ring's clock, its navigator's `navigator::Clock`
    /// (`hnn::field::Ring::clock_at`): its digit the phase `λ_g mod d_g`, its jumps the whole
    /// windings since the aeon's opening (read only by contact letters). The register keeps the
    /// ring's own clock, not a copy of its arithmetic, so its carries are the clock's jumps as the
    /// lift point's are (`hnn::field::Field::selective_step`).
    clocks: Vec<Clock>,
    /// Each contact's site kind at the last refresh; `None` before one (a contact family refuses).
    kinds: Option<Vec<SiteKind>>,
    /// Each contact's ends `(g, h)`, for the contact slots.
    ends: Vec<(usize, usize)>,
}

impl LetterReader {
    /// The cell-only family's reader: no clock is read.
    pub fn cells() -> Self {
        Self {
            family: FeatureFamily::cells(),
            rings: Vec::new(),
            clocks: Vec::new(),
            kinds: None,
            ends: Vec::new(),
        }
    }

    /// **The reader of a declared family at a lift point that opens an aeon** (the mount, or the
    /// re-keyed lift point after a carry-out): the windings since the opening start at zero.
    /// Refused at a phase letter of a ring outside the field, at a grain that is zero, or at a
    /// contact slot of a contact outside it. A family with contact letters reads its site kinds
    /// from the first [`LetterReader::refresh`].
    pub fn of(field: &Field, family: FeatureFamily, current: &Current) -> Result<Self, HnnError> {
        let mut reach = 0usize;
        for feature in family.features() {
            match *feature {
                Feature::Phase { ring, grain } => {
                    if ring >= field.rings().len() {
                        return Err(HnnError::RingOutside {
                            ring,
                            rings: field.rings().len(),
                        });
                    }
                    if grain == 0 {
                        return Err(HnnError::NonpositiveDeclaration);
                    }
                    reach = reach.max(ring + 1);
                }
                Feature::Contact { contact, .. } => {
                    if contact >= field.contacts().len() {
                        return Err(HnnError::Shape {
                            what: "a contact letter of a declared contact",
                            expected: field.contacts().len(),
                            found: contact,
                        });
                    }
                    reach = field.rings().len();
                }
            }
        }
        let rings: Vec<ClockRing> = field.rings()[..reach]
            .iter()
            .map(|ring| ClockRing {
                period: ring.period(),
                ports: (0..field.alphabet()).map(|code| ring.port(code)).collect(),
                lock: (0..ring.period() as usize)
                    .map(|port| ring.fits(port))
                    .collect(),
                rest: ring.navigator().clock().clone(),
            })
            .collect();
        let mut reader = Self {
            family,
            clocks: rings.iter().map(|ring| ring.rest.clone()).collect(),
            rings,
            kinds: None,
            ends: field
                .contacts()
                .iter()
                .map(|contact| contact.ends())
                .collect(),
        };
        reader.synchronize(field, current)?;
        Ok(reader)
    }

    pub fn family(&self) -> &FeatureFamily {
        &self.family
    }

    /// **Take the rings' phases from a lift point** (at the mount, and after a re-keying, which
    /// keeps every winding): each kept ring's clock at the lift point's phase class with its
    /// windings since the opening kept.
    pub fn synchronize(&mut self, field: &Field, current: &Current) -> Result<(), HnnError> {
        for (ring, clock) in self.clocks.iter_mut().enumerate() {
            let declared = &self.rings[ring];
            let ticks = clock.winding() * BigUint::from(declared.period)
                + BigUint::from(current.phase(field, ring)?);
            *clock = declared.rest.clone();
            clock.advance(&ticks);
        }
        Ok(())
    }

    /// **Read the contacts' site kinds from a constitution** (`hnn::contact::site_kinds`): the
    /// kinds every later tick's contact letter carries until the next refresh (the resident's, after
    /// each ingest). A family without contact letters reads nothing.
    pub fn refresh(
        &mut self,
        field: &Field,
        constitution: &impl ConstitutionRead,
    ) -> Result<(), HnnError> {
        if self.family.reads_contacts() {
            self.kinds = Some(site_kinds(field, constitution)?);
        }
        Ok(())
    }

    /// **Hold given site kinds** (the development harness's replay of a passage's kinds, one per
    /// contact), refused at a count that is not the field's contacts'.
    pub fn hold_kinds(&mut self, kinds: Vec<SiteKind>) -> Result<(), HnnError> {
        if kinds.len() != self.ends.len() {
            return Err(HnnError::Shape {
                what: "one site kind per declared contact",
                expected: self.ends.len(),
                found: kinds.len(),
            });
        }
        self.kinds = Some(kinds);
        Ok(())
    }

    /// Whether the register's clock is the lift point's: every kept ring's phase, and, where
    /// contacts are read, its windings since the aeon's opening (`opening`, the resident's opening
    /// lift point, or the carry-out's lift point when the ingest just carried out; the resident
    /// checks it at every ingest).
    pub fn agrees(&self, field: &Field, current: &Current, opening: &[BigInt]) -> bool {
        let Ok(opening) = Current::at(field, opening.to_vec()) else {
            return false;
        };
        let contacts = self.family.reads_contacts();
        self.clocks.iter().enumerate().all(|(ring, clock)| {
            current.phase(field, ring).ok() == Some(ring_digit(clock))
                && (!contacts
                    || match (current.winding(field, ring), opening.winding(field, ring)) {
                        (Ok(now), Ok(then)) => now - then == BigInt::from(clock.winding().clone()),
                        _ => false,
                    })
        })
    }

    /// **One cell's selective step on the kept rings** (`hnn::field::Field::selective_step`):
    /// ring `g`'s clock advances `[port_g(x) ∈ N_g]` plus its predecessor's carry, and its jumps
    /// are the carry it sends on. Returns whether the last ring carried out.
    fn step(&mut self, cell: usize) -> bool {
        let mut carry = 0u64;
        for (ring, clock) in self.rings.iter().zip(self.clocks.iter_mut()) {
            let fits = ring
                .ports
                .get(cell)
                .and_then(|&port| ring.lock.get(port))
                .copied()
                .unwrap_or(false);
            carry = clock
                .advance(&BigUint::from(u64::from(fits) + carry))
                .to_u64()
                .expect(
                    "a ring of period at least 2 advanced at most two ticks jumps at most once",
                );
        }
        carry == 1
    }

    /// **Ring `g`'s phase class at grain `g_R`**: `⌊g_R·phase⌋ mod g_R` of the phase `λ_g/d_g` in
    /// turns (`GrainCell::of`, its fibre the remainder; Lean `phase_partition_finite`).
    fn class(&self, ring: usize, grain: u64) -> u64 {
        let period = self.rings[ring].period;
        GrainCell::of(
            &Rat::new(
                BigInt::from(ring_digit(&self.clocks[ring])),
                BigInt::from(period),
            ),
            grain,
        )
        .phase
    }

    /// **Contact `a`'s reading after the tick**: its lock address from its rings' windings since
    /// the aeon's opening at its bound, and its site kind as held. Refused before a refresh.
    fn contact(&self, contact: usize, bound: &LockDeclaration) -> Result<ContactReading, HnnError> {
        let kinds = self.kinds.as_ref().ok_or(HnnError::Shape {
            what: "the site kinds a contact letter reads (the register's refresh)",
            expected: self.ends.len(),
            found: 0,
        })?;
        let (g, h) = self.ends[contact];
        Ok(ContactReading {
            contact,
            lock: lock_address(
                &BigInt::from(self.clocks[g].winding().clone()),
                &BigInt::from(self.clocks[h].winding().clone()),
                bound,
            ),
            kind: kinds[contact],
        })
    }

    /// **The letter of one tick**: the cell's selective step, then its bundle read after the tick
    /// (the cell alone for the cell-only family), each phase slot from the clock and each contact
    /// slot from its reading; at the joint clock's carry-out the windings then restart, as the next
    /// aeon opens there.
    pub fn tick(&mut self, cell: usize) -> Result<Letter, HnnError> {
        let carry_out = self.step(cell);
        if self.family.is_empty() {
            return Ok(Letter::Cell(cell));
        }
        let values = self
            .family
            .features()
            .iter()
            .map(|feature| match feature {
                Feature::Phase { ring, grain } => Ok(self.class(*ring, *grain)),
                Feature::Contact { contact, bound } => {
                    feature.contact_value(&self.contact(*contact, bound)?)
                }
            })
            .collect::<Result<Vec<u64>, HnnError>>()?;
        if carry_out && self.family.reads_contacts() {
            // The next aeon opens here: each clock restarts at its phase class, no windings.
            for (ring, clock) in self.rings.iter().zip(self.clocks.iter_mut()) {
                let phase = BigUint::from(ring_digit(clock));
                *clock = ring.rest.clone();
                clock.advance(&phase);
            }
        }
        Ok(Letter::Bundle(Bundle {
            cell,
            features: self.family.letters().encode(&values)?,
        }))
    }

    /// Its exact bits: each kept ring's phase, `⌈log₂ d_g⌉`, and, where contacts are read, each
    /// kept ring's windings since the opening (fewer than `∏_(j>g) d_j`, `⌈log₂ ∏_(j>g) d_j⌉`) and
    /// each contact's site kind (`⌈log₂ 5⌉`).
    pub fn bits(&self) -> u64 {
        let phases: u64 = self
            .rings
            .iter()
            .map(|ring| ceil_log2(&BigUint::from(ring.period)))
            .sum();
        if !self.family.reads_contacts() {
            return phases;
        }
        let windings: u64 = (0..self.rings.len())
            .map(|g| {
                let bound: BigUint = self.rings[g + 1..]
                    .iter()
                    .map(|ring| BigUint::from(ring.period))
                    .product();
                ceil_log2(&bound)
            })
            .sum();
        phases
            + windings
            + self.ends.len() as u64 * ceil_log2(&BigUint::from(crate::hnn::contact::SITE_KINDS))
    }
}

/// [definition; agent-inferred] **The receiving parametron's active suffix address** (module
/// header): the last `D` ticks' letters received, newest bundle first, `Boundary` before the
/// passage's first cell, and the reader of the next letters (the clock at the register's cut).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActiveAddress {
    letters: Vec<Letter>,
    reader: LetterReader,
}

impl ActiveAddress {
    /// **The address before any cell**, the cell-only family: `D` boundary letters.
    pub fn boundary(depth: usize) -> Self {
        Self {
            letters: vec![Letter::Boundary; depth],
            reader: LetterReader::cells(),
        }
    }

    /// **The resident's address register** for a field at a lift point and its constitution: at
    /// the deepest declared receiver's depth, each receiver reading its own first `D` letters, with
    /// the field's declared letter family ([`letter_family`]) and the constitution's site kinds.
    pub fn of_field(
        field: &Field,
        current: &Current,
        constitution: &impl ConstitutionRead,
    ) -> Result<Self, HnnError> {
        let depth = field
            .receivers()
            .iter()
            .map(|receiver| receiver.depth)
            .max()
            .unwrap_or(0);
        let mut reader = LetterReader::of(field, letter_family(field), current)?;
        reader.refresh(field, constitution)?;
        Ok(Self {
            letters: vec![Letter::Boundary; depth],
            reader,
        })
    }

    /// **A register of depth `D` with a declared reader**, before any cell.
    #[cfg(test)]
    pub(crate) fn of_reader(depth: usize, reader: LetterReader) -> Self {
        Self {
            letters: vec![Letter::Boundary; depth],
            reader,
        }
    }

    /// `D`.
    pub fn depth(&self) -> usize {
        self.letters.len()
    }

    /// The letters, newest first.
    pub fn letters(&self) -> &[Letter] {
        &self.letters
    }

    /// The reader of the next letters.
    pub fn reader(&self) -> &LetterReader {
        &self.reader
    }

    /// **Receive one cell**: its tick's letter, read by the register's reader after the tick (its
    /// contacts' readings included), becomes the newest, and the oldest leaves.
    pub fn receive(&mut self, cell: usize) -> Result<(), HnnError> {
        let letter = self.reader.tick(cell)?;
        if !self.letters.is_empty() {
            self.letters.pop();
            self.letters.insert(0, letter);
        }
        Ok(())
    }

    /// **Take the clock from a lift point** after a re-keying (the letters already read keep their
    /// ticks' values: Lean `bundle_causal`).
    pub fn synchronize(&mut self, field: &Field, current: &Current) -> Result<(), HnnError> {
        self.reader.synchronize(field, current)
    }

    /// [definition; agent-inferred, October 4; the reception carry §10] **The register's text**, a
    /// part of a continuing state: `address` with its letters newest first (`b` the boundary, `c` a
    /// cell's code, `f` a bundle's cell and features), and `clocks` with each read ring's ticks
    /// since the aeon's opening. The reader's family, rings and ends are the field's, and its site
    /// kinds are the constitution's, read again at the restore.
    pub fn write(&self, s: &mut String) {
        use crate::hnn::state_text::line;
        line(
            s,
            "address",
            self.letters.iter().map(|letter| match letter {
                Letter::Boundary => "b".to_string(),
                Letter::Cell(code) => format!("c{code}"),
                Letter::Bundle(bundle) => format!("f{}.{}", bundle.cell, bundle.features),
            }),
        );
        line(s, "clocks", self.reader.clocks.iter().map(Clock::ticks));
    }

    /// **The register continued from its text** ([`ActiveAddress::write`]) on a register of the
    /// same field: refused, typed, where the depth or the clocks' count differs or a letter is out
    /// of its form.
    pub fn continued<'a>(
        mut self,
        head: &str,
        next: crate::hnn::state_text::Next<'_, 'a>,
    ) -> Result<Self, HnnError> {
        use crate::hnn::state_text::{keyed, refused, value, values};
        let what = "the address register";
        let letters = keyed(head, "address", what)?
            .into_iter()
            .map(|word| {
                Ok(match (word.get(..1), word.get(1..)) {
                    (Some("b"), Some("")) => Letter::Boundary,
                    (Some("c"), Some(code)) => Letter::Cell(value(Some(&code), what)?),
                    (Some("f"), Some(rest)) => {
                        let (cell, features) = rest.split_once('.').ok_or(HnnError::ContinuingState { what })?;
                        Letter::Bundle(Bundle {
                            cell: value(Some(&cell), what)?,
                            features: value(Some(&features), what)?,
                        })
                    }
                    _ => return refused(what),
                })
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let ticks: Vec<BigUint> = values(&keyed(next("the register's clocks")?, "clocks", what)?, what)?;
        if letters.len() != self.letters.len() || ticks.len() != self.reader.clocks.len() {
            return refused("the address register against the field's declaration");
        }
        self.letters = letters;
        for ((clock, ring), ticks) in self.reader.clocks.iter_mut().zip(&self.reader.rings).zip(&ticks) {
            *clock = ring.rest.clone();
            clock.advance(ticks);
        }
        Ok(self)
    }

    /// **Read the contacts' site kinds from the published constitution** (the resident's, after
    /// each ingest: [`LetterReader::refresh`]).
    pub fn refresh(
        &mut self,
        field: &Field,
        constitution: &impl ConstitutionRead,
    ) -> Result<(), HnnError> {
        self.reader.refresh(field, constitution)
    }

    /// **The address's first `depth` letters** (a receiver of a shallower tree), with its reader,
    /// refused past the register's depth.
    pub fn truncated(&self, depth: usize) -> Result<Self, HnnError> {
        if depth > self.letters.len() {
            return Err(HnnError::Shape {
                what: "a receiver's address depth within the resident's register",
                expected: self.letters.len(),
                found: depth,
            });
        }
        Ok(Self {
            letters: self.letters[..depth].to_vec(),
            reader: self.reader.clone(),
        })
    }

    /// **Phase `j`'s address** (module header; Lean `Compression/Landmark/Context/Address.bundle_causal`): the
    /// letters of the epoch's cells before phase `j` that are known, newest first (read by a copy
    /// of the register's reader, its clock and held site kinds, stepped over `known[0], …,
    /// known[j−1]`, at most the `known.len()` of them), then this suffix, truncated to its depth. At
    /// a compare every earlier target is known, so this is `compression::landmark::context::letter_address` of the
    /// passage's letters at `p + j`, contact letters included (the register reads the same kinds at
    /// the epoch's ingest: [`LetterReader`]); at a release no cell of the epoch is known and every
    /// phase reads the address where the epoch opens (`hnn::port`'s release). The target of phase
    /// `j` is never read.
    pub fn phase(&self, known: &[usize], j: usize) -> Result<Vec<Letter>, HnnError> {
        let depth = self.letters.len();
        let mut reader = self.reader.clone();
        let mut window = known[..j.min(known.len())]
            .iter()
            .map(|&cell| reader.tick(cell))
            .collect::<Result<Vec<Letter>, HnnError>>()?;
        window.reverse();
        Ok(window
            .into_iter()
            .chain(self.letters.iter().copied())
            .take(depth)
            .collect())
    }

    /// **Its exact bits**: each letter one of the family's bundle codes with the boundary
    /// (`1 + |A| Π_i s_i`, [`LetterFamily::bundle_codes`]; `|A| + 1` for the cell-only family), and
    /// the reader's state.
    pub fn bits(&self, alphabet: usize) -> u64 {
        self.letters.len() as u64
            * ceil_log2(&BigUint::from(
                self.reader.family.letters().bundle_codes(alphabet),
            ))
            + self.reader.bits()
    }
}

/// [definition; agent-inferred] **The field's declared letter family** (campaign 2, decided on the
/// development cells by the development harness, the notebook's retired
/// [`hnn_landmark`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/hnn_landmark.rs)):
/// the receiving letters every receiver's tree is addressed by. The harness's receipt (the notebook
/// [README](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/README.md)
/// at that commit, its `hnn_landmark` row) chose the cell-only family: at the horizon bounds no
/// clock-only family and no contact
/// family coded below the constant-slot control of its slots by its description charge (every
/// `Δ_letters` decided positive), so no letter carried information the preceding cells do not.
pub fn letter_family(_field: &Field) -> FeatureFamily {
    FeatureFamily::cells()
}

/// [definition; agent-inferred, U5] **The receiver's epochs over `n` cells at aperture `A`**
/// ([`ReceivingPhases::windows`], module header): the epochs of the cell clock's forward aeon of
/// `n` cells at the receiver's section of grain `A`, each as the span of cells whose leaving
/// micro-state it holds (Lean `Aeon/Clock/Epoch.forward_epoch_is_window`: the forward walk's ticks
/// at the section are the digit clock's, and its epoch `k` is `[kA, (k + 1)A)`); a last epoch with
/// no cell is not read. Refused at `A = 0`, which is no
/// section (`aeon::AeonError::ZeroPeriod`).
pub fn receiving_windows(cells: usize, aperture: usize) -> Result<Vec<Range<usize>>, HnnError> {
    // One cell a tick: the cell clock's declared duration is the cell.
    let cell_clock = ClockLift::of_clocks(&[Clock::unwound(Rat::one())?]);
    let aeon = cell_clock.forward(vec![BigInt::zero()], &[BigInt::from(cells)])?;
    let receiver = cell_clock.ring_section(0, BigUint::from(aperture))?;
    Ok(epochs(&aeon, receiver)
        .intervals()
        .into_iter()
        .map(|span| span.start..span.end.min(cells))
        .filter(|span| !span.is_empty())
        .collect())
}

/// [definition; agent-inferred] **The letters of a passage replayed without the wave** (the
/// development harness's letters, the development harness): the resident's clock law. Each cell steps the lift
/// point (`Current::step`) and its tick's letter is read after the step; at the joint clock's
/// carry-out the keys are located on the closing crib (its last `W_crib` cells, the aeon's own,
/// read at the declared offset: `keys::locate_closing`, as the exposure locates them) and re-key
/// the lift point, which the reader takes. A family with contact letters reads its site kinds from
/// `kinds`, the kinds the register held at each cell's tick (one entry per cell, the resident's
/// refreshes of a development pass: the exposure's constitution curve); it is refused without them.
pub fn clock_letters(
    field: &Field,
    family: &FeatureFamily,
    cells: &[usize],
    kinds: &[Vec<SiteKind>],
) -> Result<Vec<Letter>, HnnError> {
    if family.reads_contacts() && kinds.len() < cells.len() {
        return Err(HnnError::Shape {
            what: "the site kinds held at each tick of a contact family's passage",
            expected: cells.len(),
            found: kinds.len(),
        });
    }
    let mut current = Current::at_rest(field);
    let mut reader = LetterReader::of(field, family.clone(), &current)?;
    let crib = field.crib();
    let mut aeon_start = 0usize;
    let mut letters = Vec::with_capacity(cells.len());
    for (at, &cell) in cells.iter().enumerate() {
        if family.reads_contacts() && reader.kinds.as_ref() != Some(&kinds[at]) {
            reader.hold_kinds(kinds[at].clone())?;
        }
        let step = current.step(field, cell)?;
        letters.push(reader.tick(cell)?);
        if step.carry_out {
            let end = at + 1;
            let from = end.saturating_sub(crib.window).max(aeon_start);
            if end - from > crib.offset {
                let location =
                    keys::locate_closing(field, &current, &cells[from..end], crib.offset)?;
                location.rekey(field, &mut current)?;
                reader.synchronize(field, &current)?;
            }
            aeon_start = end;
        }
    }
    Ok(letters)
}

/// [definition; agent-inferred] **The landmark tree a receiver declares** (module header): the
/// field's exterior chart `|A|` (the cell emitted as its odometer digits), the receiver's depth `D`
/// with no forced split, the field's declared population (the passage the tree's certificates hold
/// within), the receiver's grain `L_R = ⌈1/ε_bits⌉`, the field's letter family
/// ([`letter_family`], its slots' alphabets) and the receiver's declared stop-weight law (the declared stop prior), from which the
/// owner derives its widths (the path lattice `M_p`, the β carrier `W` and, past `u128`, the
/// carrier's rebase `R`).
pub fn landmark_declaration(
    field: &Field,
    receiver: &ReceiverDeclaration,
) -> Result<LandmarkDeclaration, HnnError> {
    landmark_declaration_with(field, receiver, letter_family(field).letters().clone())
}

/// **The landmark tree a receiver declares with a given family** (the harness's and the tests').
pub fn landmark_declaration_with(
    field: &Field,
    receiver: &ReceiverDeclaration,
    family: LetterFamily,
) -> Result<LandmarkDeclaration, HnnError> {
    Ok(LandmarkDeclaration {
        alphabet: field.alphabet(),
        depth: receiver.depth,
        forced: 0,
        population: field.population(),
        grain: grain_of(&receiver.tolerance)?,
        family,
        prior: receiver.prior.clone(),
        capacity: crate::compression::landmark::context::Capacity::Unbounded,
        mass: receiver.mass,
        base: receiver.base,
    })
}

/// `L_R = ⌈1/ε_bits⌉`, refused at a tolerance that is not positive or whose grain passes the word.
fn grain_of(tolerance: &Rat) -> Result<u64, HnnError> {
    if *tolerance <= Rat::zero() {
        return Err(HnnError::Tolerance {
            tolerance: tolerance.clone(),
        });
    }
    tolerance
        .recip()
        .ceil()
        .to_integer()
        .to_u64()
        .ok_or(HnnError::Tolerance {
            tolerance: tolerance.clone(),
        })
}

// -------------------------------------------------------------------------------------------
// the receiving face: the receiver's population over the tree and the combined face

/// [definition] **One reached comparison's step of the receiving face**: its receiving ring and
/// its two families' faces of the target, the tree's executed face `q_T(x)` (exact, dyadic) and the
/// combined face's exact enclosure `q_C(x) ∈ [lo, hi]` in the real chart of `ℚ(θ)`, which the
/// receiver's population receives ([`ReceivingStep::faces`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingStep {
    pub ring: usize,
    pub tree: Rat,
    pub combined: ExactInterval,
}

impl ReceivingStep {
    /// **The families' faces of the target**, in the receiver's family order ([`TREE`],
    /// [`COMBINED`]): the tree's exact face as a point, and the combined face's enclosure.
    pub fn faces(&self) -> [ExactInterval; 2] {
        [
            ExactInterval::point(self.tree.clone()),
            self.combined.clone(),
        ]
    }
}

/// [definition] **An epoch scored by the receiving face**: each phase's code length under the
/// receiver's population (the model's), and under the tree's executed face `q_T` alone (the face the
/// population weighs, `compression::landmark::context::code_length` of `q_T(t_j)`), and the steps its
/// deposit applies in cell order.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Scored {
    pub model: Vec<ExactInterval>,
    pub tree: Vec<ExactInterval>,
    pub steps: Vec<ReceivingStep>,
}

/// The receiver's population's first family: the landmark tree's executed face `q_T`.
pub const TREE: usize = 0;

/// The receiver's population's second family: the combined face `q_C` (the tree's grain logits
/// plus the wave).
pub const COMBINED: usize = 1;

/// [definition; agent-inferred] **The receiver's population** (`receiver::population::port`; the
/// primary's ruling A, THE_REBUILD U1): the population at the receiving port over its two families,
/// the tree's executed face ([`TREE`]) and the combined face ([`COMBINED`]), at matched priors, one
/// bit of description each, so `π = ½/½` and nothing is reserved. [agent-inferred] One bit each:
/// the prior ruling A's mixture opened at (`β_0 = 1`), declared as the two families' equal
/// descriptions.
///
/// ```text
/// q_t(x) = w_T q_T(x) + w_C q_C(x),   w_f = L_f/(L_T + L_C),   L_f = ∏_(s<t) P_f(x_s)
/// ∏_t q_t = ½ L_T + ½ L_C,            min(L_T, L_C) ≤ L_model ≤ min(L_T, L_C) + 1 bit
/// ```
///
/// The receiver's scored face is weighed like a landmark (ruling A, from the landmark tree's own
/// law, which weighs every landmark by its code-length evidence and not by a rule), as a tree node
/// weighs its own face against its split: at `π = ½` the population is that two-face mixture (Lean
/// `Compression/Landmark/Context/LocalWeighing.two_face_prior`, `priorMix (1/2) = seqMix`; the
/// telescope and the bounds are `Tree.{sequential_mixture, sequential_mixture_bounds}`), which hold
/// only when each cell's weights are the likelihoods after every earlier cell: phase `j` of an
/// epoch reads the population after phases `< j`. Its weights are read from the families'
/// likelihoods, held in `Θ` at the receiving locus, never from a carried ratio: `q_C(x)` lives in
/// `ℚ(θ)` and enters as its exact enclosure (Lean `Population.population_mixture_enclosed`), so the
/// population's code encloses the true mixture's and no chart drift enters it. The wave still
/// learns from its own comparison, the covector of `q_C` against the target, and the tree's face
/// is stored, not pulled back; the population is scored on the host at compare, beside the tree
/// read, on every realization.
///
/// It replaced the carried-ratio mixture `hnn::receiving::Mixture` (THE_REBUILD U1, first loop;
/// history at `19f1eb61`), whose `β` stepped the same law on the chart `q̃_C = lo` with rebases: on
/// the standing cut, host and card, every phase's two codes lay within that chart's certified drift,
/// the bound Lean `Population.{executed_face_within_population, executed_mixture_within_population}`
/// proves. The fixed-share switching law across epochs (Lean
/// `Compression/Landmark/Context/LocalWeighing`) is realized by the population's dormant families
/// (`receiver::population::Dormancy`), not here.
pub fn receiving_population() -> PortPopulation {
    PortPopulation::new(&[1, 1]).expect("two families of one bit each fit Kraft's sum")
}

/// **Score an epoch in cell order** (the receiver's population; Lean
/// `Compression/Landmark/Context/Tree.sequential_mixture`): phase `j` reads the population after the
/// epoch's earlier phases' faces (their targets are known at compare), the tree's face
/// `q_T,j(t_j)` and the combined face's exact enclosure `q_C,j(t_j) ∈ [lo, hi]`, so its code length
/// is the population's code of the target, enclosed ([`PortPopulation::code_of`]); its step is
/// received on a local copy of the population and staged, so the deposit, which receives the staged
/// steps in cell order, reaches the same population. The tree's own code length `−log₂ q_T,j(t_j)`
/// is returned beside it. Refused unless there is one combined face, one tree face and one target
/// per phase.
pub fn score(
    population: &PortPopulation,
    ring: usize,
    combined: &Faces,
    trees: &[LandmarkFace],
    targets: &[usize],
) -> Result<Scored, HnnError> {
    if combined.faces.len() != trees.len() || trees.len() != targets.len() {
        return Err(HnnError::Shape {
            what: "one combined face, one tree face and one target per phase",
            expected: trees.len(),
            found: targets.len(),
        });
    }
    let mut local = population.clone();
    let mut scored = Scored {
        model: Vec::with_capacity(targets.len()),
        tree: Vec::with_capacity(targets.len()),
        steps: Vec::with_capacity(targets.len()),
    };
    for ((face, tree), &target) in combined.faces.iter().zip(trees).zip(targets) {
        let q_tree = tree
            .probabilities
            .get(target)
            .ok_or(HnnError::CellOutside {
                code: target,
                alphabet: tree.probabilities.len(),
            })?
            .clone();
        scored.tree.push(code_length(&q_tree)?);
        let step = ReceivingStep {
            ring,
            tree: q_tree,
            combined: face_enclosure(face, target)?,
        };
        scored
            .model
            .push(local.code_of(&step.faces()).map_err(population_refusal)?);
        local.receive(&step.faces()).map_err(population_refusal)?;
        scored.steps.push(step);
    }
    Ok(scored)
}

/// A refusal of the receiver's population, as the HNN's.
pub(crate) fn population_refusal(refusal: PopulationError) -> HnnError {
    match refusal {
        PopulationError::Hnn(error) => *error,
        _ => HnnError::Shape {
            what: "the receiver's population: faces in the unit interval, some family alive",
            expected: 1,
            found: 0,
        },
    }
}

/// **The exact enclosure of one class's face** `p̂_c = 2^(n_c − n_top) θ^(k_c)/Z` in the real chart
/// `θ ↦ 2^(1/L)` at the carried power's reading bits: the carried power's enclosure over the
/// normalizer's.
fn face_enclosure(face: &Face, class: usize) -> Result<ExactInterval, HnnError> {
    let cells = face.cells();
    let cell = cells.get(class).ok_or(HnnError::CellOutside {
        code: class,
        alphabet: cells.len(),
    })?;
    let top = cells
        .iter()
        .map(|cell| cell.carry.clone())
        .max()
        .expect("a face over at least one class");
    let power = CarriedPower::new(&cell.carry - &top, cell.phase, face.grain())?
        .value()?
        .enclosure()?;
    let normalizer = face.normalizer().enclosure()?;
    ExactInterval::new(
        &power.lower / &normalizer.upper,
        &power.upper / &normalizer.lower,
    )
    .map_err(|_| HnnError::Shape {
        what: "an ordered enclosure of a face",
        expected: 0,
        found: 1,
    })
}

// -------------------------------------------------------------------------------------------
// the receiving phases

/// [definition] **The receiving phases** of one admitted receiver. See the module header.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceivingPhases {
    ring: usize,
    first_epoch: usize,
    aperture: usize,
    grain: u64,
    tolerance: Rat,
    depth: usize,
    rank: usize,
}

impl ReceivingPhases {
    /// **Declare an admitted receiver's phases** at the medium `(Θ, λ)`: its first epoch from the
    /// source rings, its grain from its code tolerance, and its observability rank over the word,
    /// refusing an aperture beyond it.
    pub fn declare(
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        receiver: &ReceiverDeclaration,
    ) -> Result<Self, HnnError> {
        if receiver.ring >= field.rings().len() {
            return Err(HnnError::RingOutside {
                ring: receiver.ring,
                rings: field.rings().len(),
            });
        }
        let grain = grain_of(&receiver.tolerance)?;
        if receiver.aperture == 0 {
            return Err(HnnError::Observability {
                aperture: 0,
                rank: 0,
            });
        }
        let first_epoch = field
            .first_epoch(receiver.ring)
            .ok_or(HnnError::Unreached {
                ring: receiver.ring,
            })?;
        let mut phases = Self {
            ring: receiver.ring,
            first_epoch,
            aperture: receiver.aperture,
            grain,
            tolerance: receiver.tolerance.clone(),
            depth: receiver.depth,
            rank: 0,
        };
        phases.rank = phases.observability(field, constitution, current)?;
        if phases.aperture > phases.rank {
            return Err(HnnError::Observability {
                aperture: phases.aperture,
                rank: phases.rank,
            });
        }
        Ok(phases)
    }

    /// **The receiving ring's observability rank over the word**: the rank of the exact law's linear
    /// map from the source rings' open storage to the anchors `(v_R(e_0), …, v_R(e_last))`, one
    /// word per source coordinate. [agent-inferred] The rank is the medium's, read under the exact
    /// law ([`Operands::exact_at_cut`]): the executed word carries its transients on a lattice and
    /// is linear only up to its released remainders, so a rank read through it would count the
    /// splits, not the medium.
    pub fn observability(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
    ) -> Result<usize, HnnError> {
        let operands = Operands::exact_at_cut(field, constitution, current)?;
        let mut columns: Vec<Vec<Rat>> = Vec::new();
        for &source in field.sources() {
            for coordinate in 0..field.ring(source).width() {
                let mut storage: Vec<Vec<Rat>> = field
                    .rings()
                    .iter()
                    .map(|ring| vec![Rat::zero(); ring.width()])
                    .collect();
                storage[source][coordinate] = integer(1);
                let mut word = Word::on_operands(field, operands.clone(), storage)?;
                columns.push(word.forward(self)?.concat());
            }
        }
        let rows = columns.first().map_or(0, Vec::len);
        let matrix = ExactRatMatrix::shaped(
            rows,
            columns.len(),
            (0..rows)
                .map(|row| columns.iter().map(|column| column[row].clone()).collect())
                .collect(),
        )?;
        Ok(matrix.rank()?)
    }

    pub fn ring(&self) -> usize {
        self.ring
    }

    /// `e_0`.
    pub fn first_epoch(&self) -> usize {
        self.first_epoch
    }

    /// `A`.
    pub fn aperture(&self) -> usize {
        self.aperture
    }

    /// `e_last = e_0 + A − 1`.
    pub fn last_epoch(&self) -> usize {
        self.first_epoch + self.aperture - 1
    }

    /// `e_max = e_0 + A`: the junction steps the word evaluates.
    pub fn junction_steps(&self) -> usize {
        self.first_epoch + self.aperture
    }

    /// The receiving epochs `e_0 … e_last`: the word clock's ticks at which the receiver reads
    /// (module header, "The receiver reads the passage by epochs").
    pub fn epochs(&self) -> Range<usize> {
        self.first_epoch..self.first_epoch + self.aperture
    }

    /// [definition; agent-inferred, U5] **The receiver's epochs over a passage of `n` cells**
    /// (module header, "The receiver reads the passage by epochs"): the epochs of the cell clock's
    /// forward aeon at the receiver's section. The cell clock is the source's unwound navigator
    /// clock, one tick a cell (`navigator::Clock::unwound`, period one, lifted by
    /// `aeon::ClockLift::of_clocks`); the receiver's section is its sub-section at grain `A`, the
    /// aperture (`aeon::ClockLift::ring_section`), the digit clock of base `A`. So the receiver's
    /// span `k` is epoch `k` ([`crate::aeon::Epochs::intervals`]), its cells those whose leaving
    /// micro-state lies in it, `[kA, min((k + 1)A, n))`; cell `c` is read in its epoch `⌊c/A⌋`, and
    /// the epochs that close are the section's flux `⌊n/A⌋` (Lean
    /// `Aeon/Clock/Epoch.{epochOf_digitTicks, forward_epoch_is_window, odometer_tower}`). A last
    /// epoch that holds no cell (`A | n`, the last micro-state alone) is not read.
    pub fn windows(&self, cells: usize) -> Result<Vec<Range<usize>>, HnnError> {
        receiving_windows(cells, self.aperture)
    }

    /// [definition; agent-inferred, October 4; the reception carry §10] **The phases with the rank
    /// read at their declaring medium**: a restored resident's admitted family keeps the rank its
    /// declaration read, not one read at the restored medium.
    pub(crate) fn with_rank(self, rank: usize) -> Self {
        Self { rank, ..self }
    }

    /// `L_R = ⌈1/ε_bits⌉`.
    pub fn grain(&self) -> u64 {
        self.grain
    }

    /// The declared code tolerance `ε_bits`.
    pub fn tolerance(&self) -> &Rat {
        &self.tolerance
    }

    /// `D`, the depth of the landmark tree's address (the landmark tree).
    pub fn depth(&self) -> usize {
        self.depth
    }

    /// **The observability rank reported at declaration**: a reading at the declaring medium
    /// `(Θ, λ)` only. A later class configuration (the rings' phases after ingest, the sheet
    /// classes after deposits) can have a lower rank; nothing re-reads it, and no law consumes it
    /// past the declaration's refusal of a wider aperture.
    pub fn rank(&self) -> usize {
        self.rank
    }

    /// **The wave's read at one receiving epoch**: `R · P_R^(τ_R) v_R`, each class's real logit read
    /// at the grain with its fibre, and its imaginary logit halved into turns. The tree part is
    /// added at compare ([`ReceivingPhases::combine`]).
    pub fn read(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        anchor: &[Rat],
    ) -> Result<ReceivingRead, HnnError> {
        let ring = field.ring(self.ring);
        if anchor.len() != ring.width() {
            return Err(HnnError::Shape {
                what: "receiving anchor",
                expected: ring.width(),
                found: anchor.len(),
            });
        }
        let map = constitution
            .receiving_map(self.ring)
            .ok_or(HnnError::MissingReceivingMap { ring: self.ring })?;
        if map.rows() != 2 * field.alphabet() || map.columns() != ring.width() {
            return Err(HnnError::Shape {
                what: "receiving map R",
                expected: 2 * field.alphabet() * ring.width(),
                found: map.rows() * map.columns(),
            });
        }
        // The map's rows, then the classes' grain cells, each read alone, run together
        // (`hnn::realization`); the map has `2|A|` rows, so the classes pair them exactly.
        let wave = apply_rows(map, &ring.rotate(anchor, &current.lift()[self.ring]))?;
        Ok(ReceivingRead::of_logits(wave, self.grain))
    }

    /// **The epoch's phase addresses** (module header): phase `j` at
    /// [`ActiveAddress::phase`] of the epoch's known targets. Refused when the suffix is not of
    /// the receiver's depth.
    pub fn addresses(
        &self,
        address: &ActiveAddress,
        known: &[usize],
    ) -> Result<Vec<Vec<Letter>>, HnnError> {
        if address.depth() != self.depth {
            return Err(HnnError::Shape {
                what: "the active suffix address against the receiver's depth",
                expected: self.depth,
                found: address.depth(),
            });
        }
        (0..self.aperture)
            .map(|j| address.phase(known, j))
            .collect()
    }

    /// **The tree faces of one epoch, in cell order** (module header): the receiving parametron's
    /// tree read at each phase's address, every class's executed face with its grain exponent,
    /// phase `j` at the standing after the deposits of the known earlier phases' targets
    /// ([`window_faces`] over `compression::landmark::context::Landmarks::window`: a working
    /// overlay, the published tree unchanged; at a release nothing is known and every phase reads
    /// the published standing). The phases then read together (`hnn::realization`). Refused when
    /// the constitution carries no tree on the receiving ring.
    pub fn tree_faces(
        &self,
        constitution: &impl ConstitutionRead,
        address: &ActiveAddress,
        known: &[usize],
    ) -> Result<Vec<LandmarkFace>, HnnError> {
        let tree = constitution
            .landmarks(self.ring)
            .ok_or(HnnError::MissingReceivingMap { ring: self.ring })?;
        let addresses = self.addresses(address, known)?;
        window_faces(tree, &addresses, known, self.grain)
    }

    /// **The combined faces of one epoch** (module header): each phase's wave logits plus its tree
    /// face's grain logits, read at the grain. Refused unless there is one tree face per phase.
    pub fn combine(&self, waves: &Faces, trees: &[LandmarkFace]) -> Result<Faces, HnnError> {
        if waves.logits.len() != trees.len() {
            return Err(HnnError::Shape {
                what: "one tree face per receiving phase",
                expected: waves.logits.len(),
                found: trees.len(),
            });
        }
        let reads = indexed(trees.len(), |j| {
            ReceivingRead::combined(waves.logits[j].clone(), &trees[j], self.grain)
        })?;
        Faces::of_reads(&reads, self.grain)
    }
}
