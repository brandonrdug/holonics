//! **The duplex: the helical code's first native consumer** (the
//! [record](../../../../../research/records/2026-10-08_THE_HELICAL_CODE_IS_HOW_HOLONS_HOLARCHIES_EPOCHS_AND_AEONS_ENCODE.md),
//! §5 item 4, "The first consumer, step 1"; the
//! [guide](../../../../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode); #63, #73, #62).
//!
//! [definition] The computational object is the helical pair interaction: a contact between strand
//! position `k` and partner position `n − 1 − k`. Of the winding guide's six general objects this
//! owner touches the **helix** ([`CarryHelix`]: a circle plus its carry), the **pair** (the
//! contacts) and **faces and placement** (the receiver's reading `E` of the placed lifts). Cell
//! holonomy, the tube and the tower thread stay attached and untouched. It is one file beside the
//! located transport and founds no subsystem: it consumes [`LocatedTransport`], [`PairContact`] and
//! [`pair_lock`], [`Encoding`], and `width_over_readings` → [`LawfulOptions::assemble`] →
//! [`release`].
//!
//! **Lifts: the helix is a circle plus its carry.**
//!
//! ```text
//! ℓ_0 = key mod D            ℓ_(k+1) = ℓ_k + A(u_k)              absolute, never reduced
//! ℓ = (ℓ div D)·D + (ℓ mod D)      phase ℓ mod D = the circle      winding ℓ div D = the carry
//! ```
//!
//! [definition] The receiving chart reads phases, `emit(ℓ mod D) = λ(c(ℓ))`. The whole windings are
//! what the quotient to `ℤ/D` would discard, so every support below keeps the unreduced `ℓ` and
//! takes the quotient only after the terminal carry probe is read ([`LocatedTransport::lifts`]).
//! Two frames of coprime periods meet in one phase per residue pair ([`CarryHelix::of_residues`],
//! Lean `HNN/Prediction.joint_residue_determines_position`); the absolute position needs the
//! winding.
//!
//! **The pairing** ([`Pairing`]).
//!
//! ```text
//! σ∘σ = id, σ(a) ≠ a        σ̄(w)_k = σ(w_(n−1−k))        σ̄∘σ̄ = id        σ̄(vw) = σ̄(w)σ̄(v)
//! ```
//!
//! [proved-derived; Lean `Transport/HelicalCode.{complementReverse_involutive, complementReverse_append}`]
//! A word equal to its own pairing has even length and is its first half followed by that half's
//! pairing (`even_length_of_fixed`, `fixed_eq_take_append`); the owner's tests count them.
//!
//! **The partner is paired before the quotient** ([`Duplex::place`]). The strand must first be a
//! passage of the transport, `emit(ℓ_k mod D) = u_k` for every `k < n`; otherwise the located
//! defect is returned and never a duplex. The partner word is `σ̄(u)`, and its `n + 1` absolute
//! lifts are
//!
//! ```text
//! ℓ′_k = R(ℓ_n mod D) + (ℓ_n − ℓ_(n−k)),   k = 0..=n,   R = reflect_key
//! ℓ′_k mod D = R(ℓ_(n−k) mod D)            ℓ′_(k+1) − ℓ′_k = A(u_(n−1−k))
//! ```
//!
//! The partner ends at the phase `ℓ′_n mod D = R(ℓ_0) = reflect_key(key)`: only the phase, not the
//! integer `ℓ′_n = R(ℓ_n mod D) + ℓ_n − ℓ_0`. Partner letter `k` is carried by the step
//! `ℓ′_k → ℓ′_(k+1)` and read at its arrival: the reversed step is keyed by the arrival's class.
//! Both equations are checked at the consumer for every `k < n`, on phases (`step` and `emit` take
//! and return phases modulo `D`):
//!
//! ```text
//! reflected.step(ℓ′_(k+1) mod D) = ℓ′_k mod D          σ(reflected.emit(ℓ′_(k+1) mod D)) = σ̄(u)_k
//! ```
//!
//! [agent-inferred] This is the dyad-conjugated inverse step `F′ = R∘F⁻¹∘R`, the reflected
//! transport's step `R∘F∘R` run backward. [`LocatedTransport::reflected`] is the dihedral **gauge**
//! of the receiving chart (the mirror chart, which regenerates the same passage), not the pairing;
//! the pairing reverses the passage and complements its labels. No inverse branch of `F` is chosen:
//! the partner is formed from the actual strand, and each strand is the other's key. Since each
//! `T_c` is a cyclic shift, `T_c⁻¹ = T_cᵀ` holds in these native coordinates only. That is not a
//! claim about a physical paired return, which keeps `R`, the reversed order, the complemented
//! boundary labels and the producing frames.
//!
//! **Contacts, kinematic only** ([`ContactChart`]).
//!
//! ```text
//! v₋(b) = v₊(σ(b))        slip(a, b) = v₊(a) − v₋(b)  (unit rates)        slip = 0 ⇔ b = σ(a)
//! ```
//!
//! [proved-derived] With `v₊` injective on the contact alphabet and `σ` an involution, the slip of
//! the pair of translations `(v₊(a), v₋(b))` vanishes exactly when they lock, `v₊(a) = v₊(σ(b))`,
//! that is when `b = σ(a)`. The same chart on both sides would lock equal letters, not complements.
//! It is read through [`PairContact`] and [`pair_lock`] at unit rates. No power claim is made: power
//! is read only through a declared `ContactMaterial` of positive weight that is
//! `definite_on_slips`, and none is declared in this step.
//!
//! **The receiver's class** ([`Receiver`], [`ReceiverClass`]). `E` is founded once from the passage
//! chart of the located transport opened at the development keys, outside any acceptance word, and
//! is the receiver's own quotient (never an authored table). For a word placed from a key,
//!
//! ```text
//! class_R(w) = ( (E e_(ℓ_k mod D))_(k=0..=n),  ℓ_n div D )
//! ```
//!
//! every receiving state, the terminal included, and the terminal carry probe. [definition] It is a
//! read-only receipt tuple produced at the reading and compared, never stored as a retained
//! per-occurrence chain; the continuing retained object stays the future-sufficient quotient. A
//! substitution at `i` carries the shift `Δ = A(u′_i) − A(u_i)`, a signed integer
//! ([`carried_shift`]), and moves every later absolute lift by `Δ`. A state outside the reached
//! span refuses with `EncodingError::Unreached`; nothing is substituted for it.
//!
//! **The channel and the inner code** ([`Damage`]). Substitutions at declared contacts on either
//! strand, at equal length. The slipped contacts are
//!
//! ```text
//! slipped(x′, y′) = { k : y′_(n−1−k) ≠ σ(x′_k) }
//! ```
//!
//! [proved-derived; Lean `Transport/HelicalCode.{slipped_contacts_eq, slipped_repairs_distinct}`]
//! With the partner intact the slipped set is exactly the strand's substituted positions, and
//! symmetrically; at each slipped contact the two repairs differ. A coordinated complementary
//! substitution (`u_k → a`, `p_(n−1−k) → σ(a)`) slips nothing.
//!
//! **The repair family, exact and carried** ([`Decoder`]). At each contact the local factor is
//! `F_k = {u′_k}` when it does not slip and `F_k = {u′_k, σ(p′_(n−1−k))}` when it does (a declared
//! template side collapses each slipped factor to its side's letter). The supports keep the full
//! carried positions, never reduced modulo `D`:
//!
//! ```text
//! X_0 = {key mod D}        X_(k+1) = { x + A(a) : x ∈ X_k, a ∈ F_k }       x ∈ ℕ, back-pointers
//! ```
//!
//! [proved-derived] `E` reads `x mod D` and the carry probe reads `x div D`; the quotient is taken
//! only after every admitted terminal and carry receiver is included. With `0 ≤ A(a) < D`, every
//! step moves a lift by at most `D − 1`, so `X_k ⊆ [x_0, x_0 + k(D − 1)]` and
//!
//! ```text
//! |X_k| ≤ min( ∏_(j<k) |F_j|,  k(D − 1) + 1 )      whatever the number of slipped contacts
//! ```
//!
//! A rolling exact support needs two such sets (the previous and the next); this owner keeps every
//! level with its back-pointers so that the witnesses are actual members. The forward work is
//! `Σ_(k<n) |X_k||F_k|` transitions, each an ordered-map lookup. This is polynomial for this
//! declared independent channel, not a general claim that families are cheap (a coupled constraint,
//! or a wider channel, has its own bound). The exact member count is kept beside the supports
//! (`∏|F_k|` for the free family), and the work is counted, not timed.
//!
//! [proved-derived] **Coordinates, never pooled.** The class is the tuple
//! `(E(x_0 mod D), …, E(x_n mod D), x_n div D)`. Release compares the same coordinate across the
//! supported alternatives: `E(X_k) = {E e_(x mod D) : x ∈ X_k}` for each position `k`, and
//! `winding(X_n) = {x div D : x ∈ X_n}`. Readings of different positions are never pooled (one
//! trajectory's readings legitimately vary from position to position). In the supremum norm on the
//! full tuple,
//!
//! ```text
//! diameter(class_R(F)) = max( diam E(X_0), …, diam E(X_n), diam winding(X_n) )
//! ```
//!
//! This holds because every supported state extends to an actual family member: two members differ
//! at a coordinate by at most that coordinate's diameter, and any two supported states of one
//! coordinate are realized by two members. The family is released exactly when this diameter is
//! zero, that is when every coordinate's set is a singleton, and the family is nonempty.
//!
//! [definition] **Release.** Two width routes, each named for what its owner checks.
//! `width_over_readings` (`receiver::face`) computes the exact diameter of the finite family it is
//! handed and enforces its family ceiling: it reads each coordinate's complete support set, the
//! complete distinct readings of that coordinate (equal states read equal, so duplicates add
//! nothing and the diameter is unchanged), never a sample. The consumer computes the maximum over
//! the coordinates and carries that aggregate as `ReceiverWidth::declared`, which checks only the
//! structural coherence of what the caller computed (a non-negative diameter, a witness coherent
//! with the count read); the aggregate names the coordinate that attains it. It goes to
//! [`LawfulOptions::assemble`] and [`release`] at tolerance zero, as the repair owner's `decide`
//! does. The diameter equation above, the complete support, the nonempty family and the witness
//! extensions are the consumer's own, and each is pinned by a test. Released returns the class
//! every member reads. A nonempty, nonconstant family is held, naming the slipped contacts and two
//! actual witness members: the coordinate attaining the maximum supplies two supported states
//! (the pair its `width_over_readings` attains), and each is completed to a full member by walking
//! its back-pointers to the key and a supported extension to the terminal. The two witnesses
//! attain the family's diameter and their classes differ.
//!
//! [definition; agent-inferred] **The fit-constrained variant** ([`Fit::Transport`]): the admitted
//! antecedents must be passages of the transport, so a transition from `x` by `a` is kept only
//! when `emit(x mod D) = a`. Fitting couples the factors, so only supported extendable prefixes
//! count: a forward pass from the key (one emission read a transition) and a backward pass over
//! the same transitions from the terminal level keep the states that extend to a complete admitted
//! repair. The added cost is that backward sweep, `Σ_(k<n) |X_k||F_k|` again, and no more memory.
//! An empty family is never released and owes no witness: [`Decoder::decode`] returns the typed
//! defect [`DuplexDefect::NoCompatibleSource`], naming the slipped contacts.
//!
//! [agent-inferred] **Coverage and the residual.** The product of the local factors is the complete
//! family of the covered repairable channel only: at each contact at most one strand changed, so
//! the truth's letter is in `F_k`. On that channel the truth is a member, release is exactly
//! constancy of the full family, and a released class is the truth's class. A coordinated
//! complementary change is outside the coverage. It leaves no slip, so its local factor is the
//! singleton observed letter, the truth is not in the family, and the online decoder gives no truth
//! guarantee there: released returns the observed class, which may differ from the truth's. Only a
//! harness holding the truth counts it ([`Absorption`]): absorbed when the damaged word's class
//! equals the truth's (its reached difference lies in the receiver's kernel), residual when the
//! class differs and was released anyway. A contact changed on both strands but not
//! complementarily slips with two candidates that need not contain the truth, also outside the
//! coverage. The binary local factors are not the preimage family of a channel that also admits
//! unwitnessed coordinated substitutions, and nothing here claims they are. The receiver's kernel
//! is never enlarged to hide a defect.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | `σ̄(w) = σ(w)ᴿ`, `σ̄(vw) = σ̄(w)σ̄(v)`, `σ̄∘σ̄ = id` | `Transport/HelicalCode.{complementReverse, complementReverse_append, complementReverse_involutive}` | [`Pairing`] |
//! | a self-paired word has even length | `Transport/HelicalCode.{even_length_of_fixed, fixed_eq_take_append}` | the owner's tests |
//! | the pairing read through a frame is again a fixed-point-free involution | `Transport/HelicalCode.{phaseTransport_pairing, phaseTransport_reciprocal}`, `Transport/HelicalPairInteraction.reflectedReturn_no_fixed_point` | [`Duplex::place`] (the mirror chart's frame) |
//! | the slipped contacts are the substituted positions | `Transport/HelicalCode.{slipped_contacts_eq, slipped_repairs_distinct}` | [`Pairing::slipped`], [`ContactChart::slipped`] |
//! | a lock is zero slip at the rate ratio | `Transport/HelicalPairInteraction.lock_iff_zero_power` | [`ContactChart::locked`] |
//! | the unique phase of a residue tuple | `HNN/Prediction.joint_residue_determines_position` | [`CarryHelix::of_residues`] |
//! | the absolute lifts keep the carry | `Geometry/PhaseCarry.winding_add` | [`LocatedTransport::lifts`] |
//! | the class, and release at width zero | `HNN/Encoding.hankel_identification`, `Foundation/ReceiverRelease.width_eq_zero_iff` | [`Receiver`], [`Decoder`] |
//! | the family diameter is the maximum over coordinates | owed (#62) | [`Decoder::decode`], the owner's brute-force test |
//! | the carried support bound `card X_k ≤ min(∏_(j<k) card F_j, k(D − 1) + 1)` | owed (#62) | [`Decoder::decode`], the owner's exact-support test |

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use thiserror::Error;

use crate::compression::CompressionError;
use crate::geometry::RatVec3;
use crate::geometry::screw::{ScrewGenerator, ScrewPair, SituatedScrew};
use crate::hnn::encoding::{Encoding, EncodingError, PassageChart};
use crate::holon::contact::{ContactError, PairContact, pair_lock};
use crate::ratio::Rat;
use crate::receiver::face::{
    DiameterNorm, ExactFace, ReceiverWidth, WidthRefusal, WidthWitness, width_over_readings,
};
use crate::receiver::release::{
    BeyondTolerance, DecisionRule, LawfulOptions, ReleaseReturn, WithinTolerance, release,
};

use super::transport::{CarryHelix, LocatedTransport};

// -------------------------------------------------------------------------------------------
// the defects

/// [definition] **Every defect and refusal of the duplex.** A located defect is content, not a
/// panic: the positions where a strand's fit fails, the partner equation that fails, a declaration
/// the owner refuses, or a refusal of an owner it consumes.
#[derive(Debug, Error, PartialEq)]
pub enum DuplexDefect {
    /// The strand is no passage of the transport: `emit(ℓ_k mod D) ≠ Some(u_k)` at these positions,
    /// the lifts stepped by the word's own letters.
    #[error("the strand is no passage of the transport: its fit fails at positions {positions:?}")]
    Unfit { positions: Vec<usize> },
    /// A partner equation failed at the consumer (it cannot on a strand that fits).
    #[error("the partner's equation fails at position {position}: {equation}")]
    Partner {
        position: usize,
        equation: &'static str,
    },
    /// A declaration the owner refuses.
    #[error("the declaration is refused: {reason}")]
    Declared { reason: &'static str },
    /// A supported state that extends to no member of the family (it cannot after the pruning).
    #[error("the supported state at level {level} extends to no member of the family")]
    Unextendable { level: usize },
    /// The fit-constrained family is empty: no passage of the transport from the key is a member
    /// of the product of the local factors, whose slipped contacts are named. Nothing is released
    /// and no witness is owed (witnesses are owed only to a nonempty, nonconstant family).
    #[error(
        "the transport admits no compatible source for the observed duplex (slipped contacts {slipped:?})"
    )]
    NoCompatibleSource { slipped: Vec<usize> },
    #[error(transparent)]
    Compression(#[from] CompressionError),
    #[error(transparent)]
    Encoding(#[from] EncodingError),
    #[error(transparent)]
    Contact(#[from] ContactError),
}

// -------------------------------------------------------------------------------------------
// the pairing

/// [definition] **The pairing** `σ`: a fixed-point-free involution of the classes (module header),
/// the half-turn of the chart's alphabet that complements a strand's letter into its partner's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pairing {
    sigma: Vec<usize>,
}

impl Pairing {
    /// A pairing; refused unless every entry is a class, `σ(σ(a)) = a` and `σ(a) ≠ a` for every
    /// class `a` (so there is an even number of classes).
    pub fn new(sigma: Vec<usize>) -> Result<Self, CompressionError> {
        if sigma.is_empty() {
            return Err(CompressionError::EmptyFamily {
                what: "a pairing's classes",
            });
        }
        let classes = sigma.len();
        for (a, &b) in sigma.iter().enumerate() {
            if b >= classes {
                return Err(CompressionError::IndexOutside {
                    index: b,
                    population: classes,
                });
            }
            if b == a {
                return Err(CompressionError::Helix {
                    reason: "a pairing has no fixed class: σ(a) ≠ a",
                });
            }
            if sigma[b] != a {
                return Err(CompressionError::Helix {
                    reason: "a pairing is an involution: σ(σ(a)) = a",
                });
            }
        }
        Ok(Self { sigma })
    }

    /// The class count `|A|`.
    pub fn classes(&self) -> usize {
        self.sigma.len()
    }

    /// `σ(a)`, when `a` is a class.
    pub fn pair(&self, class: usize) -> Option<usize> {
        self.sigma.get(class).copied()
    }

    /// `σ(a)` as a refusal-typed read.
    fn image(&self, class: usize) -> Result<usize, CompressionError> {
        self.pair(class).ok_or(CompressionError::IndexOutside {
            index: class,
            population: self.classes(),
        })
    }

    /// **The complement-reverse** `σ̄(w)_k = σ(w_(n−1−k))` (module header): an anti-automorphism of
    /// words and an involution. Refused with a class outside the alphabet.
    pub fn complement_reverse(&self, word: &[usize]) -> Result<Vec<usize>, CompressionError> {
        word.iter().rev().map(|&class| self.image(class)).collect()
    }

    /// **The slipped contacts** `{k : y_(n−1−k) ≠ σ(x_k)}` of a strand `x` against a partner `y`
    /// (module header, the inner code). Refused with unequal lengths or a class outside the
    /// alphabet.
    pub fn slipped(
        &self,
        strand: &[usize],
        partner: &[usize],
    ) -> Result<Vec<usize>, CompressionError> {
        if strand.len() != partner.len() {
            return Err(CompressionError::Extent {
                what: "a partner as long as its strand",
                expected: strand.len(),
                found: partner.len(),
            });
        }
        let length = strand.len();
        let mut slipped = Vec::new();
        for (k, &letter) in strand.iter().enumerate() {
            let complement = self.image(letter)?;
            let across = partner[length - 1 - k];
            self.image(across)?;
            if across != complement {
                slipped.push(k);
            }
        }
        Ok(slipped)
    }
}

// -------------------------------------------------------------------------------------------
// the contacts

/// [definition] **The contact chart** (module header): an injective chart `v₊` of the classes into
/// `ℚ³`, the velocity of a strand letter's translation, and `v₋(b) = v₊(σ(b))` on the partner's
/// side. Kinematic only.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactChart {
    plus: Vec<RatVec3>,
}

impl ContactChart {
    /// A chart; refused unless it reads at least one class and `v₊` is injective.
    pub fn new(plus: Vec<RatVec3>) -> Result<Self, CompressionError> {
        if plus.is_empty() {
            return Err(CompressionError::EmptyFamily {
                what: "a contact chart's classes",
            });
        }
        for (class, vector) in plus.iter().enumerate() {
            if plus[..class].contains(vector) {
                return Err(CompressionError::NotInjective { port: class });
            }
        }
        Ok(Self { plus })
    }

    /// The class count.
    pub fn classes(&self) -> usize {
        self.plus.len()
    }

    /// `v₊(a)`.
    pub fn plus(&self, class: usize) -> Option<&RatVec3> {
        self.plus.get(class)
    }

    /// `v₋(b) = v₊(σ(b))`.
    pub fn minus(&self, pairing: &Pairing, class: usize) -> Option<&RatVec3> {
        pairing.pair(class).and_then(|image| self.plus.get(image))
    }

    /// The pair of translations `(v₊(a), v₋(b))`, situated at the origin.
    fn screw_pair(
        &self,
        pairing: &Pairing,
        a: usize,
        b: usize,
    ) -> Result<ScrewPair, CompressionError> {
        if self.plus.len() != pairing.classes() {
            return Err(CompressionError::Extent {
                what: "a contact chart over the pairing's classes",
                expected: pairing.classes(),
                found: self.plus.len(),
            });
        }
        let outside = |class: usize| CompressionError::IndexOutside {
            index: class,
            population: self.plus.len(),
        };
        let strand = self.plus(a).ok_or_else(|| outside(a))?;
        let partner = self.minus(pairing, b).ok_or_else(|| outside(b))?;
        let translation = |velocity: &RatVec3| {
            SituatedScrew::new(
                ScrewGenerator::new(RatVec3::zero(), velocity.clone()),
                RatVec3::zero(),
            )
        };
        Ok(ScrewPair::new(translation(strand), translation(partner)))
    }

    /// **The slip** `v₊(a) − v₋(b)` of a strand letter `a` against a partner letter `b`, read
    /// through [`PairContact`] at the unit rates `(1, 1)`.
    pub fn slip(&self, pairing: &Pairing, a: usize, b: usize) -> Result<RatVec3, DuplexDefect> {
        let contact = PairContact::of(self.screw_pair(pairing, a, b)?);
        Ok(contact.relative_velocity(&[Rat::one(), Rat::one()]))
    }

    /// **The lock** at the unit rate ratio `1/1`, through [`pair_lock`]: zero slip, which holds
    /// exactly when `b = σ(a)`.
    pub fn locked(&self, pairing: &Pairing, a: usize, b: usize) -> Result<bool, DuplexDefect> {
        let pair = self.screw_pair(pairing, a, b)?;
        Ok(pair_lock(&pair, &BigInt::one(), &BigInt::one())?)
    }

    /// **The slipped contacts through the contacts**: `k` slips when the contact of strand letter
    /// `x_k` with partner letter `y_(n−1−k)` does not lock. Equal to [`Pairing::slipped`].
    pub fn slipped(
        &self,
        pairing: &Pairing,
        strand: &[usize],
        partner: &[usize],
    ) -> Result<Vec<usize>, DuplexDefect> {
        if strand.len() != partner.len() {
            return Err(CompressionError::Extent {
                what: "a partner as long as its strand",
                expected: strand.len(),
                found: partner.len(),
            }
            .into());
        }
        let length = strand.len();
        let mut slipped = Vec::new();
        for (k, &letter) in strand.iter().enumerate() {
            if !self.locked(pairing, letter, partner[length - 1 - k])? {
                slipped.push(k);
            }
        }
        Ok(slipped)
    }
}

// -------------------------------------------------------------------------------------------
// the duplex

/// [definition] **A duplex**: a strand that fits the transport, with its absolute lifts, and its
/// partner `σ̄(u)` with the partner's absolute lifts (module header). Built only by
/// [`Duplex::place`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Duplex {
    key: u64,
    strand: Vec<usize>,
    lifts: Vec<u64>,
    partner: Vec<usize>,
    partner_lifts: Vec<u64>,
}

impl Duplex {
    /// **Place a strand** (module header): fit first, then the partner's lifts and the two partner
    /// equations for every `k < n`, on phases. Returns the located defect, never a duplex, when the
    /// strand is no passage of the transport from the key.
    ///
    /// [agent-inferred] The partner's step is the dyad-conjugated inverse step `F′ = R∘F⁻¹∘R`, the
    /// reflected transport's step run backward and keyed by the arrival's class. Since each `T_c` is
    /// a cyclic shift, `T_c⁻¹ = T_cᵀ` holds in these native coordinates only. That is not a claim
    /// about a physical paired return, which keeps `R`, the reversed order, the complemented
    /// boundary labels and the producing frames. The partner is formed from the actual strand, so
    /// no inverse branch of a non-injective `F` is chosen.
    pub fn place(
        transport: &LocatedTransport,
        pairing: &Pairing,
        key: u64,
        strand: &[usize],
    ) -> Result<Self, DuplexDefect> {
        if pairing.classes() != transport.classes() {
            return Err(CompressionError::Extent {
                what: "a pairing over the transport's classes",
                expected: transport.classes(),
                found: pairing.classes(),
            }
            .into());
        }
        let period = transport.helix().period();
        let length = strand.len();
        let lifts = transport.lifts(key, strand)?;
        let unfit: Vec<usize> = (0..length)
            .filter(|&k| transport.emit(lifts[k] % period) != Some(strand[k]))
            .collect();
        if !unfit.is_empty() {
            return Err(DuplexDefect::Unfit { positions: unfit });
        }
        let partner = pairing.complement_reverse(strand)?;
        let end = lifts[length];
        let base = transport.reflect_key(end);
        let mut partner_lifts = Vec::with_capacity(length + 1);
        for k in 0..=length {
            let wound = end - lifts[length - k];
            partner_lifts.push(base.checked_add(wound).ok_or(CompressionError::Helix {
                reason: "a partner lift stays within the machine word",
            })?);
        }
        let mirror = transport.reflected();
        for k in 0..length {
            let emission = partner_lifts[k] % period;
            let arrival = partner_lifts[k + 1] % period;
            if mirror.step(arrival) != Some(emission) {
                return Err(DuplexDefect::Partner {
                    position: k,
                    equation: "the mirror chart steps the partner's arrival phase to its emission phase",
                });
            }
            if mirror.emit(arrival).and_then(|class| pairing.pair(class)) != Some(partner[k]) {
                return Err(DuplexDefect::Partner {
                    position: k,
                    equation: "the complement of the mirror chart's arrival class is the partner's letter",
                });
            }
        }
        if partner_lifts[length] % period != transport.reflect_key(key) {
            return Err(DuplexDefect::Partner {
                position: length,
                equation: "the partner ends at the phase of the reflected key",
            });
        }
        Ok(Self {
            key,
            strand: strand.to_vec(),
            lifts,
            partner,
            partner_lifts,
        })
    }

    /// The key the strand was placed from.
    pub fn key(&self) -> u64 {
        self.key
    }

    /// The strand `u`.
    pub fn strand(&self) -> &[usize] {
        &self.strand
    }

    /// The strand's `n + 1` absolute lifts.
    pub fn lifts(&self) -> &[u64] {
        &self.lifts
    }

    /// The partner `σ̄(u)`.
    pub fn partner(&self) -> &[usize] {
        &self.partner
    }

    /// The partner's `n + 1` absolute lifts.
    pub fn partner_lifts(&self) -> &[u64] {
        &self.partner_lifts
    }

    /// The strand's length `n`.
    pub fn len(&self) -> usize {
        self.strand.len()
    }

    /// Whether the strand is empty.
    pub fn is_empty(&self) -> bool {
        self.strand.is_empty()
    }

    /// The contacts `(k, n − 1 − k)`: strand position and partner position.
    pub fn contacts(&self) -> Vec<(usize, usize)> {
        let length = self.len();
        (0..length).map(|k| (k, length - 1 - k)).collect()
    }
}

// -------------------------------------------------------------------------------------------
// the channel

/// [definition] **A damage** (module header, the channel): substituted letters on the strand and on
/// the partner, each at a declared contact `k`, as `(contact, new letter)`. A partner substitution
/// at contact `k` changes partner position `n − 1 − k`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Damage {
    strand: Vec<(usize, usize)>,
    partner: Vec<(usize, usize)>,
}

impl Damage {
    /// A damage of the strand and of the partner at declared contacts.
    pub fn new(strand: Vec<(usize, usize)>, partner: Vec<(usize, usize)>) -> Self {
        Self { strand, partner }
    }

    /// **A coordinated complementary damage**: at each `(contact, a)` the strand takes `a` and the
    /// partner takes `σ(a)`, so no contact slips (outside the repairable channel's coverage).
    pub fn coordinated(
        pairing: &Pairing,
        substitutions: &[(usize, usize)],
    ) -> Result<Self, CompressionError> {
        let partner = substitutions
            .iter()
            .map(|&(contact, letter)| pairing.image(letter).map(|image| (contact, image)))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Self {
            strand: substitutions.to_vec(),
            partner,
        })
    }

    /// The strand's substitutions.
    pub fn strand(&self) -> &[(usize, usize)] {
        &self.strand
    }

    /// The partner's substitutions.
    pub fn partner(&self) -> &[(usize, usize)] {
        &self.partner
    }

    /// The declared contacts of either side, sorted and without repeats.
    pub fn damaged_contacts(&self) -> Vec<usize> {
        let mut contacts: Vec<usize> = self
            .strand
            .iter()
            .chain(&self.partner)
            .map(|&(contact, _)| contact)
            .collect();
        contacts.sort_unstable();
        contacts.dedup();
        contacts
    }

    /// **The damaged words** `(x′, y′)` of a duplex. Refused unless every contact lies in the
    /// strand, every new letter is a class that differs from the letter it replaces, and a side
    /// names each contact once.
    pub fn apply(
        &self,
        duplex: &Duplex,
        pairing: &Pairing,
    ) -> Result<(Vec<usize>, Vec<usize>), DuplexDefect> {
        let length = duplex.len();
        let classes = pairing.classes();
        let mut strand = duplex.strand.clone();
        let mut partner = duplex.partner.clone();
        let mut touched = Vec::new();
        for &(contact, letter) in &self.strand {
            substitute(&mut strand, contact, letter, classes, &mut touched)?;
        }
        let mut touched = Vec::new();
        for &(contact, letter) in &self.partner {
            let position =
                length
                    .checked_sub(contact + 1)
                    .ok_or(CompressionError::IndexOutside {
                        index: contact,
                        population: length,
                    })?;
            substitute(&mut partner, position, letter, classes, &mut touched)?;
        }
        Ok((strand, partner))
    }
}

/// One substitution of a word at a position.
fn substitute(
    word: &mut [usize],
    position: usize,
    letter: usize,
    classes: usize,
    touched: &mut Vec<usize>,
) -> Result<(), DuplexDefect> {
    let current = *word.get(position).ok_or(CompressionError::IndexOutside {
        index: position,
        population: word.len(),
    })?;
    if letter >= classes {
        return Err(CompressionError::IndexOutside {
            index: letter,
            population: classes,
        }
        .into());
    }
    if letter == current {
        return Err(DuplexDefect::Declared {
            reason: "a substitution changes its letter",
        });
    }
    if touched.contains(&position) {
        return Err(DuplexDefect::Declared {
            reason: "a side's substitutions name distinct contacts",
        });
    }
    touched.push(position);
    word[position] = letter;
    Ok(())
}

// -------------------------------------------------------------------------------------------
// the receiver

/// [definition] **The receiver**: the encoding `E` founded once from the passage chart of the
/// located transport opened at the development keys (`LocatedTransport::chart`, read in the
/// receiving cells and never in the labels), and its columns `E e_phase` read once at the
/// founding. The columns are the founded map itself, read once; they are not an archive of
/// occurrences and no word is stored. A phase outside the reached span has no column, and reading
/// it refuses with `EncodingError::Unreached`.
#[derive(Clone, Debug, PartialEq)]
pub struct Receiver {
    helix: CarryHelix,
    encoding: Encoding,
    readings: Vec<Option<Vec<Rat>>>,
}

impl Receiver {
    /// **Found the receiver** on the transport's chart opened at `development_keys`. Founded
    /// outside any acceptance word: the keys, words and damage an acceptance reads are none of
    /// these openings.
    pub fn found(
        transport: &LocatedTransport,
        development_keys: &[u64],
    ) -> Result<Self, DuplexDefect> {
        let (chart, transports, coupling, openings) = transport.chart(development_keys)?;
        let passage = PassageChart::new(chart, transports, Vec::new(), coupling, openings)?;
        let encoding = Encoding::found(&passage)?;
        let mut readings = Vec::with_capacity(chart);
        for phase in 0..chart {
            let mut state = vec![Rat::zero(); chart];
            state[phase] = Rat::one();
            readings.push(match encoding.encode(&state) {
                Ok(reading) => Some(reading),
                Err(EncodingError::Unreached) => None,
                Err(other) => return Err(other.into()),
            });
        }
        Ok(Self {
            helix: transport.helix().clone(),
            encoding,
            readings,
        })
    }

    /// The founded encoding.
    pub fn encoding(&self) -> &Encoding {
        &self.encoding
    }

    /// The helix the receiver was founded on.
    pub fn helix(&self) -> &CarryHelix {
        &self.helix
    }

    /// **`E e_(x mod D)`**: the reading of a lift's phase. Refused with
    /// `EncodingError::Unreached` outside the reached span.
    pub fn reading(&self, lift: u64) -> Result<&[Rat], DuplexDefect> {
        let phase = usize::try_from(lift % self.helix.period())
            .expect("a phase below the helix ceiling fits");
        self.readings[phase]
            .as_deref()
            .ok_or(DuplexDefect::Encoding(EncodingError::Unreached))
    }

    /// **The class of a placed word** from its `n + 1` absolute lifts (module header): the reading
    /// of every phase, the terminal included, and the terminal winding.
    pub fn class(&self, lifts: &[u64]) -> Result<ReceiverClass, DuplexDefect> {
        let Some(&last) = lifts.last() else {
            return Err(CompressionError::EmptyFamily {
                what: "a class reads at least the opening lift",
            }
            .into());
        };
        let readings = lifts
            .iter()
            .map(|&lift| self.reading(lift).map(|reading| reading.to_vec()))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(ReceiverClass {
            readings,
            winding: last / self.helix.period(),
        })
    }
}

/// [definition] **A class of the receiver** (module header): the readings `E e_(ℓ_k mod D)` of the
/// `n + 1` placed lifts and the terminal winding `ℓ_n div D`. A receipt tuple, compared and never
/// retained.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverClass {
    readings: Vec<Vec<Rat>>,
    winding: u64,
}

impl ReceiverClass {
    /// The readings, one per position `0..=n`.
    pub fn readings(&self) -> &[Vec<Rat>] {
        &self.readings
    }

    /// The terminal winding `ℓ_n div D` (the carry probe).
    pub fn winding(&self) -> u64 {
        self.winding
    }

    /// **The first coordinate at which two classes differ**: a position `k`, or the number of
    /// positions for the winding; `None` when the classes are equal.
    pub fn first_difference(&self, other: &Self) -> Option<usize> {
        let shared = self.readings.len().min(other.readings.len());
        for k in 0..shared {
            if self.readings[k] != other.readings[k] {
                return Some(k);
            }
        }
        if self.readings.len() != other.readings.len() {
            return Some(shared);
        }
        (self.winding != other.winding).then_some(self.readings.len())
    }
}

/// [definition] **Absorption against known truth** (module header, coverage): acceptance-side only.
/// The decoder never calls it, because it needs the truth. A damaged word is absorbed when its
/// class equals the truth's class (its reached difference lies in the receiver's kernel) and is
/// residual otherwise, with the coordinate at which the receiver first separates it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Absorption {
    Absorbed,
    Residual { at: usize },
}

impl Absorption {
    /// The comparison of a class against the truth's class.
    pub fn between(truth: &ReceiverClass, class: &ReceiverClass) -> Self {
        match truth.first_difference(class) {
            None => Self::Absorbed,
            Some(at) => Self::Residual { at },
        }
    }
}

/// [definition] **The carried shift of a substitution** `u_i → u′_i`: the signed integer
/// `Δ = A(u′_i) − A(u_i)`, a carried representative that is not reduced modulo `D`, so
/// `−D < Δ < D`. A substitution at `i` moves every later absolute lift of the placed word by `Δ`
/// and none before it; it is zero exactly when the two letters share an advance. Refused with a
/// class outside the advances.
pub fn carried_shift(
    transport: &LocatedTransport,
    was: usize,
    now: usize,
) -> Result<i64, CompressionError> {
    let signed = |class: usize| -> Result<i64, CompressionError> {
        let advance = *transport
            .advances()
            .get(class)
            .ok_or(CompressionError::IndexOutside {
                index: class,
                population: transport.classes(),
            })?;
        i64::try_from(advance).map_err(|_| CompressionError::Helix {
            reason: "an advance fits a signed integer",
        })
    };
    Ok(signed(now)? - signed(was)?)
}

// -------------------------------------------------------------------------------------------
// the decoder

/// Which side a frame marks as the template: each slipped factor collapses to that side's letter.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Template {
    /// No frame marks a side: a slipped contact keeps both candidates.
    Unmarked,
    /// The strand is the template.
    Strand,
    /// The partner is the template.
    Partner,
}

/// Whether the admitted antecedents must be passages of the transport (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fit {
    /// The product of the local factors, and nothing more.
    Free,
    /// Only members that are passages of the transport, after backward pruning.
    Transport,
}

/// [definition] **An actual member of the repair family**: its letters and its `n + 1` absolute
/// lifts.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Member {
    pub letters: Vec<usize>,
    pub lifts: Vec<u64>,
}

/// [definition] **What a decoding read of its family**, exact counts. The sizes are those of the
/// supports `X_k` (module header): `reached` in the forward pass, `supported` after the backward
/// pass (equal in the free family). `distinct` counts the distinct readings of each coordinate:
/// the `n + 1` positions, then the winding.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FamilyReceipt {
    /// The slipped contacts.
    pub slipped: Vec<usize>,
    /// The exact member count of the complete family.
    pub members: BigUint,
    pub reached: Vec<usize>,
    pub supported: Vec<usize>,
    pub distinct: Vec<usize>,
    /// The family's diameter in the supremum norm on the full tuple; zero exactly when released.
    pub diameter: Rat,
    /// The transitions examined by the forward pass, `Σ_(k<n) |X_k||F_k|`.
    pub forward: u64,
    /// The transitions examined by the backward pass: `Σ_(k<n) |X_k||F_k|` in the fit-constrained
    /// variant, zero in the free one.
    pub backward: u64,
}

/// [definition] **A held family**: the coordinate that attains the diameter (a position, or `n + 1`
/// for the winding) and two actual witness members with their differing classes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Held {
    pub coordinate: usize,
    pub witnesses: [Member; 2],
    pub classes: [ReceiverClass; 2],
}

/// [definition] **A decoding of a nonempty family** (module header). `Released` returns the class
/// every member reads, which is the truth's class on the covered channel and is the observed class
/// outside it. `Held` names two actual witness members whose classes differ, owed only to a
/// nonconstant family. An empty family is not a decoding: it is the typed defect
/// [`DuplexDefect::NoCompatibleSource`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Decoded {
    Released {
        class: ReceiverClass,
        receipt: FamilyReceipt,
    },
    Held {
        held: Held,
        receipt: FamilyReceipt,
    },
}

impl Decoded {
    /// The exact counts the decoding read.
    pub fn receipt(&self) -> &FamilyReceipt {
        match self {
            Self::Released { receipt, .. } | Self::Held { receipt, .. } => receipt,
        }
    }
}

/// One supported state: an absolute lift, a back-pointer to a predecessor at the previous level
/// and the letter that reached it, the exact count of member prefixes that reach it, and whether it
/// extends to a complete member.
#[derive(Clone, Debug)]
struct Node {
    lift: u64,
    from: usize,
    letter: usize,
    members: BigUint,
    alive: bool,
}

/// One support `X_k`: its states in order of discovery, and an index by absolute lift.
#[derive(Clone, Debug)]
struct Level {
    nodes: Vec<Node>,
    index: BTreeMap<u64, usize>,
}

impl Level {
    fn new() -> Self {
        Self {
            nodes: Vec::new(),
            index: BTreeMap::new(),
        }
    }

    /// Reach a lift from a predecessor by a letter: a state already reached keeps its first
    /// back-pointer and adds the member count.
    fn reach(&mut self, lift: u64, from: usize, letter: usize, members: &BigUint) {
        if let Some(at) = self.index.get(&lift).copied() {
            self.nodes[at].members += members;
        } else {
            self.index.insert(lift, self.nodes.len());
            self.nodes.push(Node {
                lift,
                from,
                letter,
                members: members.clone(),
                alive: true,
            });
        }
    }

    /// Whether the level holds the lift as a state that extends to a complete member.
    fn supports(&self, lift: u64) -> bool {
        self.index
            .get(&lift)
            .is_some_and(|&at| self.nodes[at].alive)
    }
}

/// The supports `X_0 … X_n` with their back-pointers and the transitions examined.
#[derive(Clone, Debug)]
struct Support {
    levels: Vec<Level>,
    forward: u64,
    backward: u64,
}

/// One coordinate of the class: its index (a position `0..=n`, or `n + 1` for the winding), the
/// level of the support it reads, the width of its complete distinct readings and, for each
/// distinct reading, the state that represents it.
struct Coordinate {
    index: usize,
    level: usize,
    width: ReceiverWidth,
    reps: Vec<usize>,
}

/// [definition; agent-inferred] **The decoder** (module header): the receiver's founded class, the
/// located transport that steps the lifts and the pairing. It reads only observed words, never the
/// truth. The transport is the machine's located navigator (location is a separate, built
/// capability, `TransportLocation`); a harness may hand it a terrain's own transport, so that
/// location's cost is not spent here, and never hands it the truth word.
#[derive(Clone, Copy, Debug)]
pub struct Decoder<'a> {
    receiver: &'a Receiver,
    transport: &'a LocatedTransport,
    pairing: &'a Pairing,
}

impl<'a> Decoder<'a> {
    /// A decoder; refused unless the receiver was founded on the transport's helix and the pairing
    /// is over the transport's classes.
    pub fn new(
        receiver: &'a Receiver,
        transport: &'a LocatedTransport,
        pairing: &'a Pairing,
    ) -> Result<Self, DuplexDefect> {
        if receiver.helix != *transport.helix() {
            return Err(DuplexDefect::Declared {
                reason: "the receiver is founded on the transport's helix",
            });
        }
        if pairing.classes() != transport.classes() {
            return Err(CompressionError::Extent {
                what: "a pairing over the transport's classes",
                expected: transport.classes(),
                found: pairing.classes(),
            }
            .into());
        }
        Ok(Self {
            receiver,
            transport,
            pairing,
        })
    }

    /// **Decode an observed duplex** (module header): the slipped contacts, the family of local
    /// factors (collapsed by the template), its supports, the exact width of each coordinate
    /// (`width_over_readings` over that coordinate's complete distinct readings, with its family
    /// ceiling), the maximum over the coordinates carried as `ReceiverWidth::declared` (structural
    /// coherence only), and the release at tolerance zero. The key is the placement's; the words
    /// are the observed strand and partner, damaged or not. An empty family (only the
    /// fit-constrained variant can be empty) returns [`DuplexDefect::NoCompatibleSource`].
    pub fn decode(
        &self,
        key: u64,
        strand: &[usize],
        partner: &[usize],
        template: Template,
        fit: Fit,
    ) -> Result<Decoded, DuplexDefect> {
        let (slipped, admitted) = self.factors(strand, partner, template)?;
        let length = admitted.len();
        let support = self.support(key, &admitted, fit)?;
        let members = support.levels[length]
            .nodes
            .iter()
            .filter(|node| node.alive)
            .fold(BigUint::zero(), |total, node| total + &node.members);
        let mut receipt = FamilyReceipt {
            slipped,
            members,
            reached: support
                .levels
                .iter()
                .map(|level| level.nodes.len())
                .collect(),
            supported: support
                .levels
                .iter()
                .map(|level| level.nodes.iter().filter(|node| node.alive).count())
                .collect(),
            distinct: Vec::new(),
            diameter: Rat::zero(),
            forward: support.forward,
            backward: support.backward,
        };
        if receipt.members.is_zero() {
            return Err(DuplexDefect::NoCompatibleSource {
                slipped: receipt.slipped,
            });
        }
        let mut best = self.coordinate(&support, length, 0)?;
        receipt.distinct.push(best.reps.len());
        for index in 1..=length + 1 {
            let read = self.coordinate(&support, length, index)?;
            receipt.distinct.push(read.reps.len());
            if read.width.diameter() > best.width.diameter() {
                best = read;
            }
        }
        receipt.diameter = best.width.diameter().clone();
        // The aggregate: the maximum over the coordinates, which this consumer computed, carried as
        // a declared width (the owner checks its structural coherence only) and naming the
        // coordinate that attains it.
        let attaining = if best.width.is_zero() {
            WidthWitness::Point
        } else {
            WidthWitness::Coordinate {
                coordinate: best.index,
            }
        };
        let aggregate = ReceiverWidth::declared(
            "the class of the compatible family",
            "the supremum over the coordinates of each coordinate's exact diameter over its complete supported readings",
            DiameterNorm::Supremum,
            receipt.diameter.clone(),
            attaining,
            receipt.distinct.iter().sum::<usize>(),
        )
        .map_err(law)?;
        if commit(&aggregate)? {
            let first = support.levels[length]
                .nodes
                .iter()
                .position(|node| node.alive)
                .ok_or(DuplexDefect::Unextendable { level: length })?;
            let member = self.member(&support, &admitted, fit, length, first)?;
            let class = self.receiver.class(&member.lifts)?;
            return Ok(Decoded::Released { class, receipt });
        }
        let (left, right) = match best.width.attaining() {
            WidthWitness::Pair { left, right } => (*left, *right),
            _ => return Err(refusal("a positive width names the pair that attains it")),
        };
        let witnesses = [
            self.member(&support, &admitted, fit, best.level, best.reps[left])?,
            self.member(&support, &admitted, fit, best.level, best.reps[right])?,
        ];
        let classes = [
            self.receiver.class(&witnesses[0].lifts)?,
            self.receiver.class(&witnesses[1].lifts)?,
        ];
        Ok(Decoded::Held {
            held: Held {
                coordinate: best.index,
                witnesses,
                classes,
            },
            receipt,
        })
    }

    /// The slipped contacts and the local factors `F_k` of an observed duplex.
    fn factors(
        &self,
        strand: &[usize],
        partner: &[usize],
        template: Template,
    ) -> Result<(Vec<usize>, Vec<Vec<usize>>), DuplexDefect> {
        let slipped = self.pairing.slipped(strand, partner)?;
        let length = strand.len();
        let mut admitted = Vec::with_capacity(length);
        for (k, &own) in strand.iter().enumerate() {
            let implied = self.pairing.image(partner[length - 1 - k])?;
            admitted.push(if own == implied {
                vec![own]
            } else {
                match template {
                    Template::Unmarked => vec![own, implied],
                    Template::Strand => vec![own],
                    Template::Partner => vec![implied],
                }
            });
        }
        Ok((slipped, admitted))
    }

    /// The lift reached from a lift by a letter, or `None` when the fit-constrained variant
    /// refuses the transition (the transport emits another letter at the lift's phase).
    fn successor(&self, lift: u64, letter: usize, fit: Fit) -> Result<Option<u64>, DuplexDefect> {
        if fit == Fit::Transport
            && self.transport.emit(lift % self.transport.helix().period()) != Some(letter)
        {
            return Ok(None);
        }
        let advance =
            *self
                .transport
                .advances()
                .get(letter)
                .ok_or(CompressionError::IndexOutside {
                    index: letter,
                    population: self.transport.classes(),
                })?;
        let next = lift.checked_add(advance).ok_or(CompressionError::Helix {
            reason: "an absolute lift stays within the machine word",
        })?;
        Ok(Some(next))
    }

    /// **The supports** `X_0 … X_n` (module header): forward from the key with back-pointers, and in
    /// the fit-constrained variant a backward pass that keeps only the states that extend to a
    /// complete member.
    fn support(
        &self,
        key: u64,
        admitted: &[Vec<usize>],
        fit: Fit,
    ) -> Result<Support, DuplexDefect> {
        let period = self.transport.helix().period();
        let mut opening = Level::new();
        opening.reach(key % period, 0, 0, &BigUint::one());
        let mut levels = vec![opening];
        let mut forward = 0u64;
        for letters in admitted {
            let mut next = Level::new();
            {
                let here = &levels[levels.len() - 1];
                for (from, node) in here.nodes.iter().enumerate() {
                    for &letter in letters {
                        forward += 1;
                        let Some(lift) = self.successor(node.lift, letter, fit)? else {
                            continue;
                        };
                        next.reach(lift, from, letter, &node.members);
                    }
                }
            }
            levels.push(next);
        }
        let mut backward = 0u64;
        if fit == Fit::Transport {
            for k in (0..admitted.len()).rev() {
                let (head, tail) = levels.split_at_mut(k + 1);
                let next = &tail[0];
                for node in head[k].nodes.iter_mut() {
                    let mut supported = false;
                    for &letter in &admitted[k] {
                        backward += 1;
                        if let Some(lift) = self.successor(node.lift, letter, fit)? {
                            supported |= next.supports(lift);
                        }
                    }
                    node.alive = supported;
                }
            }
        }
        Ok(Support {
            levels,
            forward,
            backward,
        })
    }

    /// **One coordinate of the class** across the supported alternatives: the readings
    /// `E e_(x mod D)` of the supported states of a position, or their windings `x div D` at the
    /// terminal (`index = n + 1`). Readings of different positions are never pooled. The complete
    /// distinct values go to `width_over_readings`, which computes their exact diameter.
    fn coordinate(
        &self,
        support: &Support,
        length: usize,
        index: usize,
    ) -> Result<Coordinate, DuplexDefect> {
        let level = index.min(length);
        let period = self.transport.helix().period();
        let nodes = &support.levels[level].nodes;
        let mut faces = Vec::new();
        let mut reps = Vec::new();
        let name;
        if index <= length {
            name = format!("E e_(x mod D) at position {index}");
            let mut seen: Vec<&[Rat]> = Vec::new();
            for (at, node) in nodes.iter().enumerate() {
                if !node.alive {
                    continue;
                }
                let reading = self.receiver.reading(node.lift)?;
                if !seen.contains(&reading) {
                    seen.push(reading);
                    faces.push(ExactFace::Vector(reading.to_vec()));
                    reps.push(at);
                }
            }
        } else {
            name = String::from("the whole winding x div D at the terminal");
            let mut seen: Vec<u64> = Vec::new();
            for (at, node) in nodes.iter().enumerate() {
                if !node.alive {
                    continue;
                }
                let winding = node.lift / period;
                if !seen.contains(&winding) {
                    seen.push(winding);
                    faces.push(ExactFace::Count(BigInt::from(winding)));
                    reps.push(at);
                }
            }
        }
        let width = width_over_readings(
            &name,
            "the supported lifts of the compatible family at this coordinate",
            &faces,
            DiameterNorm::Supremum,
        )
        .map_err(law)?;
        Ok(Coordinate {
            index,
            level,
            width,
            reps,
        })
    }

    /// **An actual member through a supported state**: the letters and lifts along the
    /// back-pointers from the state at `level` to the key, completed to the terminal through a
    /// supported extension.
    fn member(
        &self,
        support: &Support,
        admitted: &[Vec<usize>],
        fit: Fit,
        level: usize,
        index: usize,
    ) -> Result<Member, DuplexDefect> {
        let length = admitted.len();
        let mut letters = vec![0usize; level];
        let mut lifts = vec![0u64; level + 1];
        let mut at = index;
        for l in (0..=level).rev() {
            let node = &support.levels[l].nodes[at];
            lifts[l] = node.lift;
            if l > 0 {
                letters[l - 1] = node.letter;
                at = node.from;
            }
        }
        let mut lift = lifts[level];
        for j in level..length {
            let mut stepped = None;
            for &letter in &admitted[j] {
                let Some(next) = self.successor(lift, letter, fit)? else {
                    continue;
                };
                if support.levels[j + 1].supports(next) {
                    stepped = Some((letter, next));
                    break;
                }
            }
            let (letter, next) = stepped.ok_or(DuplexDefect::Unextendable { level: j })?;
            letters.push(letter);
            lifts.push(next);
            lift = next;
        }
        Ok(Member { letters, lifts })
    }
}

/// A refusal of the release law, as the repair owner reports it.
fn law(refusal: WidthRefusal) -> DuplexDefect {
    DuplexDefect::Compression(CompressionError::ReleaseLaw(refusal.to_string()))
}

fn refusal(reason: &str) -> DuplexDefect {
    DuplexDefect::Compression(CompressionError::ReleaseLaw(reason.to_owned()))
}

/// **The commit at tolerance zero**, as `compression::keys::repair`'s `decide` takes it: the
/// aggregate width of the family (the maximum over its coordinates, declared by the consumer) goes
/// through [`LawfulOptions::assemble`] and [`release`] with the holding rule. Released exactly when
/// the width is zero.
fn commit(width: &ReceiverWidth) -> Result<bool, DuplexDefect> {
    let rule = DecisionRule::new(
        "the duplex's commit at tolerance zero",
        WithinTolerance::Release,
        BeyondTolerance::Hold,
    );
    let options = LawfulOptions::assemble(width, Rat::zero(), None, true).map_err(law)?;
    let returned = release(&rule, &options).map_err(law)?;
    Ok(matches!(returned, ReleaseReturn::Released { .. }))
}

#[cfg(test)]
mod tests;
