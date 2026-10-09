//! **The paired carrier: the helical code's partner on the HNN carrier** (the
//! [record](../../../../research/records/2026-10-08_THE_HELICAL_CODE_IS_HOW_HOLONS_HOLARCHIES_EPOCHS_AND_AEONS_ENCODE.md),
//! §5, "Step 2: the partner face on the HNN carrier" and "The general partner law and its scope"; the
//! [guide](../../../../docs/ELEMENTARY_OBJECTS.md#the-helical-code-how-holons-encode); #63, #73, #62).
//!
//! [definition] The computational object is the helical pair interaction on the HNN's source ring:
//! strand position `k` meets partner position `n − 1 − k`. Of the winding guide's six general objects
//! this owner touches the **helix** (the ring's phase circle and its carry), the **pair** (a strand
//! against its complement) and **faces and placement** (the source port `E_g` reading a class at the
//! phase the ring reached). Cell holonomy, the tube and the tower thread stay attached and untouched.
//! It founds no recurrence of its own. Its first real caller is [`SourceMoment::encode`] and
//! [`SourceMoment::open_storage`], and the partner's face is read through them, from the strand's phase
//! counts, by [`SourceMoment::dyad`]. The one closed form kept here, `B Pᵏ` applied to a face, is what
//! that read is checked against, and it is the redundancy of the last section.
//!
//! **Three objects, named apart.**
//!
//! ```text
//! F_g   the ring's port permutation (Ring::reflector): an involution of ℤ/d, read today only as the
//!       Bombe's stage ρ⁻ᵐFρᵐ; Ring::declare checks F² = 1 and nothing else, and is not tightened
//! B_g   its realified carrier lift on ℚ^(2d):   (B v)[2F(i) + r] = v[2i + r],   r ∈ {0, 1}
//! σ     the class pairing: a fixed-point-free involution of an admitted class family
//! ```
//!
//! `Ring::rotate` moves the node pairs `(2i, 2i+1) → (2P^k(i), 2P^k(i)+1)` with `P(i) = i + 1`, so `B_g`
//! and the rotor `P_g` act on one carrier. (`B_g` is not the prior `B` of `hnn::executed::pair_deposit`,
//! which is the declared source port `E_0`.)
//!
//! **The admission** ([`PairedCarrier::admit`]), each refusal typed:
//!
//! ```text
//! F∘F = id                                                   the reflector is an involution
//! F(F(i) + 1) = i − 1   for every port i                     the dihedral relation, F P F = P⁻¹
//! σ∘σ = id,  σ(a) ≠ a   on the admitted family               an even family; or two roles, the free swap
//! B E = E Σ_σ   column by column:  E e_(σa) = B E e_a        the source port carries the pairing
//! ```
//!
//! [proved-derived] The dihedral relation holds exactly when `F(i) = F(0) − i` (mod `d`). From
//! `F P F = P⁻¹` and `F² = 1` follows `F P = P⁻¹ F`, so `F(i + 1) = F(i) − 1`; conversely `F(i) = c − i`
//! gives `F(F(i) + 1) = c − (c − i + 1) = i − 1`. So of the `d^d` maps of the ports exactly `d` pass, the
//! reflections of the `d`-gon, and `p ↦ −p`, campaign 1's reflector, is the one with `c = 0`; a ring of
//! period 4 with `F = [1, 0, 2, 3]` is an involution that `Ring::declare` accepts and that fails the
//! relation at port 0. Then `B² = 1` and `B P B = P⁻¹` on the carrier, `B Pᵏ = P⁻ᵏ B`, and every `B Pᵏ`
//! is an involution, the half-turn about a dyad (Lean `Transport/HelicalCode.{dihedral_swap,
//! dihedral_reflection_sq, dihedral_conj}`, with `U = B` and `S = P`).
//!
//! **The pairing is typed, and the alphabet is not changed to fit.** A [`PairingDeclaration`] is an
//! admitted class family with `σ` on it, or two role families with `σ` their free swap on the disjoint
//! union; anything else is refused ([`PairingDefect`]). A fixed-point-free involution pairs the classes
//! in twos, so a family is even. `FieldDeclaration::campaign_one` reads five classes, on which no
//! pairing exists (the owner's test enumerates all `5⁵` maps), and it is refused as it is. An even
//! sub-family of its five classes, or two roles, can be paired, and the classes outside it must carry
//! no count at the read. On four classes the pairings are the three translations of the Klein group
//! (Lean `free_involution_iff`, `card_free_involutions_fin4`), and on `2m` classes there are `(2m − 1)!!`
//! (1, 3 and 15 on 2, 4 and 6; the owner's test counts them). The native consumer's `Pairing::new`
//! (`compression::keys::duplex`) accepts exactly the total tables that resolve here (the owner's test
//! compares them), but it pairs a whole chart and so can declare neither an even sub-family of an odd
//! chart nor two roles.
//!
//! **The founded port is refused.** `declared_source_port` is the declared sign sequence times ½, the
//! opening `E_0` of every source ring, and it carries no pairing: on campaign 1 the first column of
//! either pairing of four of its classes fails at row 0 (`E_0[0][0] = −½` against `E_0[0][1] = E_0[0][2]
//! = +½`) and the admission names it. [`PairedCarrier::equivariant_port`] keeps such a port's leader
//! columns and sets each follower to `B` of its leader.
//!
//! **The source port is plastic, so the property is a state of the port and not of the carrier.** The
//! admission certifies `B E = E Σ_σ` of the port it is handed, at one moment. Deposition moves `E − E_0`
//! (`hnn::executed::pair_deposit`):
//!
//! ```text
//! Δ_y = P^δ E_0 e_y − (E − E_0) e_f(y)          E ← E + η D at the located classes' columns f(y),
//!                                                 D = Σ w g (X̂ f)ᵀ, X̂ the carried Gram's refined inverse
//! ```
//!
//! [proved-derived] That law does not preserve `E e_(σa) = B E e_a`. The pair it deposits, `y → f(y)` at
//! distance `δ` (the consequence is the current cell, the antecedent the earlier one), has the dyad
//! image `σ f(y) → σ y` at the same distance, because reversing a strand reverses the orientation of
//! each of its pairs: the image's consequence is `σ y`, not `σ f(y)`. The deposit moves the column of
//! `f(y)` by its slip. Equivariance asks the column of `σ f(y)` to move by `B` of that, and for
//! equivariant `E` and `E_0` one has `B Δ_y = P^(−δ) E_0 e_(σy) − (E − E_0) e_(σ f(y))`, the slip of a
//! pair at offset `−δ`, which the forward law does not read (measured: one forward deposit takes an
//! equivariant port off its subspace, the owner's test). Nor is its prior equivariant: the founded `E_0`
//! is the declared sign sequence, which this admission itself refuses (above). The equivariant deposit
//! reads that pair by the reversal law of the pair port ([`PairedCarrier::deposit`], "The paired
//! deposit" below). The carrier still keeps no port, and
//! **every read re-certifies the source port it reads** ([`PairedCarrier::partner_face`]): a port that
//! a deposit, or any declared change, has taken off the equivariant subspace is refused with the typed
//! [`PairedDefect::Equivariance`] naming the first failing column, and a different equivariant port is
//! read as lawfully as the admitted one.
//!
//! **The partner on the actual consumer** ([`SourceMoment`]). A cell is counted at the phase its ring
//! reaches **after** its step, and the open is
//!
//! ```text
//! m̃(u)   = ν̂(n) Σ_c P^(−c) E M[c]       M[c][a] = #{k : phase_k = c, u_k = a},  n = Σ M     (encode)
//! s(0)(u) = P^τ m̃(u)                      τ = the ring's lift after the passage                (open_storage)
//! ```
//!
//! with no pair ports and the transport at modulus one. On a unit-tick passage opened at phase `s`,
//! letter `k` sits at phase `s + k + 1`, so `m̃(u) = ν̂(n) Σ_k P^(−(s+k+1)) E e_(u_k)` and
//! `s(0)(u) = ν̂(n) Σ_k P^(n−1−k) E e_(u_k)`: the record's recurrence face `Σ_k Uⁿ⁻¹⁻ᵏ E(u_k)` with
//! `U = P`, the newest letter first. The partner `σ̄(u)_k = σ(u_(n−1−k))`, opened at `s′`, puts strand
//! letter `j` at phase `s′ + n − j`, so its counts are the strand's reflected in the phase and
//! complemented in the class:
//!
//! ```text
//! M′[t][c] = M[c₀ − t][σ(c)]        c₀ = s + s′ + n + 1 (mod d)         n′ = n,  ν̂(n′) = ν̂(n)
//! m̃(σ̄u)  = B P^(c₀) m̃(u)            s(0)(σ̄u) = B P^(−(n−1)) s(0)(u)     (B Pᵏ)² = id
//! ```
//!
//! [proved-derived] The first line needs no port: the counts of a unit-tick passage are relabelled by a
//! bijection. The second needs `E e_(σa) = B E e_a` and `B P B = P⁻¹`:
//! `s(0)(σ̄u) = ν̂ Σ_j Pʲ E e_(σu_j) = ν̂ Σ_j Pʲ B E e_(u_j) = B ν̂ Σ_j P⁻ʲ E e_(u_j) = B P^(−(n−1)) s(0)(u)`.
//! This is Lean `strandFace_complementReverse_nat` and `face_complementReverse` with `J = B`, `g = P`
//! and the conjugacy `B U B = U⁻¹` stated and checked, not implied by orthogonality. The bridge
//! `moment l = U^(n−1)·strandFace U⁻¹ (I∘E) l` that joins the Lean face to the moment is owed (#62).
//! [`PairedCarrier::partner_face`] reads the partner's open storage through the actual path and
//! returns it beside `B P^(−(n−1))` of the strand's own open storage, so the identity is checked at
//! every read and its exact residual is returned and never hidden.
//!
//! **The tick is certified from the field, not assumed** ([`PairedDefect::LockMisses`],
//! [`PairedDefect::CarriedClock`]). On the identity route a ring advances `[port ∈ N_g]` plus its
//! predecessor's carry, so the unit tick holds when every class of the family fits the source ring's
//! lock (a class is its own port there) and no earlier ring in the carry chain ever ticks (an empty
//! lock: it never wraps, so it never carries). A letter-selected clock, whose advances `A(c)` differ,
//! needs its own relation (`J S_a J = S_(σa)⁻¹`, and on a common fixed-generator rotor `A∘σ = A` with
//! its conjugacy declared); a located moment keeps no digits. Both are refused. The moment's
//! partition tag (periods, sources, alphabet, offsets) does not carry the locks, so the read takes
//! the field it is handed as the one the moment was ingested under, and `ticks = cells` is the
//! consistency it can check from the counts.
//!
//! **Descent through the quotient: what normalization or rounding would break, and where it is
//! refused.** The consumer's quotient is the counts weighted by `ν̂(n) = ⌊2^(L_ν)/n + ½⌋ 2^(−L_ν)`.
//! - At modulus one the weight is one scalar of the population `n`, the partner has the same `n`, and
//!   the chart rounds the same number on both sides, so it commutes with the lift exactly and the
//!   residual is zero.
//! - The leaky count rounds every decayed coordinate to the nearest lattice point at every tick, in the
//!   order of the ages, and again on the chart. A reversed passage reverses its ages, and for `U = ρP`
//!   the conjugate is `B U B = ρ P⁻¹`, not `U⁻¹ = ρ⁻¹ P⁻¹`: the redundant case's conjugacy fails
//!   ([`DyadRefusal::Leaky`]; a constitution whose transport is not one is refused at the read,
//!   [`PairedDefect::Transport`]).
//! - The pair ports read an oriented offset moment whose orientation reverses under the dyad and whose
//!   weight is `ν̂` of the pair population `n − δ`: refused ([`DyadRefusal::PairOffsets`]) until the
//!   moment's own pair-port reversal is built (the deposit's is [`PairedCarrier::deposit`]).
//! - A located clock, a continued section, a reframe, a ring that did not tick once a cell, and a count
//!   of a class outside the family have no unit-tick phase relation ([`DyadRefusal`]).
//!
//! **What the read joins and what it refuses.** It joins the phase counts `first[phase·|A| + class]`
//! (reflected and complemented), the population `n` and so `ν̂(n)`, the ring's `start`, `end`, `ticks`
//! and `cells`, the opening lift, `encode`'s carrying `P^(−c)` and `open_storage`'s lift `P^τ`. It
//! refuses everything listed above and any other moment than the field's own single-source,
//! ingest-only passage.
//!
//! **The paired deposit** ([`PairedCarrier::deposit`]; helical step 3, #386; Lean `HNN/PairedDeposit`).
//! [proved-derived; agent-inferred, October 9] With `B E_0 = E_0 Σ`, `B E = E Σ` and `B P B = P⁻¹`, the
//! lift of a located pair's slip is the slip of its dyad image read against the clock (Lean
//! `reversal_identity`, from `lift_pow`):
//!
//! ```text
//! B Δ_y = P^(−δ) E_0 e_(σy) − (E − E_0) e_(σ f(y))  =:  Δ^R          the pair-port reversal law
//! ```
//!
//! The dyad image's slip is read by its own law at `−δ` (`hnn::executed::oriented_slip`), never formed
//! as `B Δ`: the identity is the check at every pair ([`PairedDefect::Reversal`]). The slip reads the
//! ring's rotor alone, as the forward deposit does, so `P^(−δ)` is exact at every modulus; the partner
//! face, which reads the moment's weights, refuses a damped transport on its own.
//! - **One step for both orientations.** Each located pair and its dyad image enter one certified step
//!   with weight one each (`hnn::executed::deposit_reads`). The features' multiset is `Σ`-invariant, so
//!   `ΔH = Σ w f fᵀ` commutes with `Σ` and the aggregate `G = Σ w g fᵀ` satisfies `B G = G Σ`.
//! - **The chart commutes on pair features.** A pair's feature is a unit column, so from the founding
//!   `H_0 = 2^k I` the Gram stays diagonal, and each step of the chart (the warm start's rank-one steps,
//!   the refinements, the restart) acts on each diagonal entry alone with the same rounding: `X̂ Σ = Σ X̂`,
//!   so `D = G X̂` satisfies `B D = D Σ` (Lean `mul_commuting_stays`).
//! - **The lattice keeps the subspace.** The budgeted carry is entrywise, so equivariant remainders
//!   stay equivariant and the committed port stays equivariant (Lean `deposit_stays_equivariant`). The
//!   successor is re-admitted inside the deposit, and a port that left the subspace is refused
//!   ([`PairedDefect::Deposited`]).
//! - **Not built here: the symmetrized chart.** Where other deposits have made the Gram non-diagonal,
//!   `X̂` need not commute with `Σ`; `½(X̂ + Σ X̂ Σ)` does (Lean `symmetrized_commutes`), and it keeps
//!   the chart's certificate `‖1 − X̂H‖∞ ≤ δ` when `Σ H = H Σ` (Lean `symmetrized_rowNorm_le`). It is built with its first consumer, the comparison's general route
//!   (`compose_return`); until then the re-admission refuses such a deposit, typed.
//!
//! [proved-derived] On the equivariant subspace `|Δ^R| = |Δ_y|` (`B` permutes coordinates), so the
//! paired slip is twice the forward one there, and the paired deposit descends the forward slip within
//! the subspace: its fixed point is the forward slip's least point among equivariant ports. When the
//! located law asks a column for a content the pairing forbids (a column that is one pair's
//! consequence and another's dyad image with different carried priors), no equivariant port closes
//! every slip; the slip that remains is the law's incompatibility with the pairing, read and returned
//! (the owner's test reads a 4-cycle law beside a duplex whose strands move disjoint columns, where
//! every slip closes in one deposit).
//!
//! **Information at the retained quotient: redundancy.** At modulus one the partner's retained counts
//! are a fixed bijection of the strand's, and its face is `B P^(−(n−1))` of the strand's. So for this
//! undamped, conservative carrier the partner face is a function of the forward face and `n`: no two
//! admitted sources of one length share a forward face and differ in the partner's (the owner's test
//! groups every word of up to five letters over four classes by length and face). The partner is a pure
//! check, not new information. Damping alone would establish none, `B U B = Uᵀ` holds only in a declared
//! Euclidean carrier (in a material metric `G` the adjoint is `G⁻¹UᵀG`), and no metric claim is made.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | the reflector is a reflection of the rotor, `F(i) = F(0) − i`; the lift inverts the rotor | `Transport/HelicalCode.{dihedral_swap, dihedral_reflection_sq, dihedral_conj}` | [`reflector_defect`], [`PairedCarrier::admit`], [`PairedCarrier::lift`] |
//! | the pairing is a fixed-point-free involution of an even family, or the free swap of two roles | `Transport/HelicalCode.{complementReverse_involutive, free_involution_iff, card_free_involutions_fin4}` | [`PairingDeclaration::resolve`], [`PairingDeclaration::of_duplex`], [`Sigma`] |
//! | the port carries the pairing, `B E = E Σ_σ` | owed (#62) | [`PairedCarrier::certify`], [`PairedCarrier::equivariant_port`] |
//! | the partner's counts are the strand's reflected and complemented | owed (#62) | [`SourceMoment::dyad`], [`PairedCarrier::partner_moment`] |
//! | `s(0)(σ̄u) = B P^(−(n−1)) s(0)(u)`, `m̃(σ̄u) = B P^(c₀) m̃(u)` | `Transport/HelicalCode.{strandFace_complementReverse_nat, face_complementReverse, partner_map_involutive}` (the bridge to the moment is owed, #62) | [`PairedCarrier::partner_face`], [`PairedCarrier::half_turn`] |
//! | the pair-port reversal law `B Δ_y = Δ^R` and the equivariant deposit; the symmetrized chart commutes | `HNN/PairedDeposit.{lift_pow, reversal_identity, mul_commuting_stays, deposit_stays_equivariant, symmetrized_commutes, symmetrized_residual, symmetrized_rowNorm_le}` | [`PairedCarrier::deposit`], `hnn::executed::{oriented_slip, deposit_reads}` |
//!
//! **Recorded failures checked.** An authored routine standing in for learning: the port's follower
//! columns are the code's own relation `E(σa) = B E(a)` on a free leader, never a decoder or a table.
//! A parallel subsystem that nothing consumes: the reader of the partner is `SourceMoment::encode` and
//! `open_storage`. A common alphabet changed to fit: five classes stay five and are refused. A refusal
//! answered with a larger limit: every refusal is a typed return and no limit is raised. A design
//! thought in arrays and offsets: the law is stated in residues, phases and the dihedral group, and the
//! arrays are its realization.

use num_bigint::BigInt;
use num_traits::{One, Zero};
use thiserror::Error;

use crate::compression::keys::duplex::Pairing;
use crate::hnn::HnnError;
use crate::hnn::constitution::Constitution;
use crate::hnn::executed::{OrientedRead, PairDeposit, class_at, deposit_reads, oriented_slip};
use crate::hnn::field::{Current, Field, FieldMaterial, Ring};
use crate::hnn::keys::LocatedPair;
use crate::hnn::moment::{DyadRefusal, SourceMoment};
use crate::ratio::Rat;
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};

// -------------------------------------------------------------------------------------------
// the reflector

/// [definition] **What a reflector table fails** ([`reflector_defect`]): the first port at which
/// `F` is not a dihedral reflection of the rotor `P(i) = i + 1`.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum ReflectorDefect {
    /// An image lies outside the ports: the table is no map of them.
    #[error("port {port}'s image {image} lies outside the {ports} ports")]
    Outside {
        port: usize,
        image: usize,
        ports: usize,
    },
    /// `F(F(i)) ≠ i`: the table is no involution.
    #[error("F(F({port})) = {returns}, not {port}: the reflector is not an involution")]
    NotInvolution { port: usize, returns: usize },
    /// `F(F(i) + 1) ≠ i − 1`: the table is an involution that is not a reflection of the rotor.
    #[error(
        "F(F({port}) + 1) = {found}, but the dihedral relation needs {port} − 1 = {expected}: the reflector is not a reflection of the rotor"
    )]
    NotDihedral {
        port: usize,
        found: usize,
        expected: usize,
    },
}

/// [proved-derived] **The first port at which a reflector table is no dihedral reflection**, `None`
/// when it is one (module header, "The admission"): every image a port, `F(F(i)) = i`, and
/// `F(F(i) + 1) = i − 1` (mod `d`). It passes exactly when `F(i) = F(0) − i`. A pure read of the
/// table: `Ring::declare` checks `F² = 1` only, and the relation is checked here, at the paired
/// carrier's admission, never by tightening it.
pub fn reflector_defect(images: &[usize]) -> Option<ReflectorDefect> {
    let ports = images.len();
    for (port, &image) in images.iter().enumerate() {
        if image >= ports {
            return Some(ReflectorDefect::Outside { port, image, ports });
        }
    }
    for port in 0..ports {
        let returns = images[images[port]];
        if returns != port {
            return Some(ReflectorDefect::NotInvolution { port, returns });
        }
    }
    for port in 0..ports {
        let found = images[(images[port] + 1) % ports];
        let expected = (port + ports - 1) % ports;
        if found != expected {
            return Some(ReflectorDefect::NotDihedral {
                port,
                found,
                expected,
            });
        }
    }
    None
}

// -------------------------------------------------------------------------------------------
// the pairing

/// [definition] **How a pairing was declared**: which charts it pairs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum PairingKind {
    /// One admitted class family with `σ` on it.
    Family,
    /// Two role families, `σ` their free swap on the disjoint union.
    Roles,
}

/// [definition] **A class pairing as declared**: data, checked by [`PairingDeclaration::resolve`]. It
/// is typed: an even admitted family with `σ` on it, or two role families (two partner charts) with `σ`
/// the free swap on their disjoint union. Any other pairing is refused with a [`PairingDefect`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PairingDeclaration {
    /// The admitted family and `σ` on it: one row `(class, σ(class))` for each class of the family.
    Family { table: Vec<(usize, usize)> },
    /// Two role families of equal size, in matching order: `σ(first[i]) = second[i]` and
    /// `σ(second[i]) = first[i]`.
    Roles {
        first: Vec<usize>,
        second: Vec<usize>,
    },
}

/// [definition] **Every refusal of a declared pairing**, each naming the class it stands on.
#[derive(Clone, Copy, Debug, Error, PartialEq, Eq)]
pub enum PairingDefect {
    /// No class is declared.
    #[error("a pairing declares no class")]
    Empty,
    /// A class lies outside the field's class chart.
    #[error("class {class} lies outside the field's {alphabet} classes")]
    ClassOutside { class: usize, alphabet: usize },
    /// A class is declared twice: in a family, or in a role (or in both roles).
    #[error(
        "class {class} is declared twice: a family names each class once and two roles are disjoint"
    )]
    ClassRepeated { class: usize },
    /// A family of odd size: a fixed-point-free involution pairs the classes in twos.
    #[error(
        "a family of {classes} classes is odd: a fixed-point-free involution pairs the classes in twos, so no pairing exists on it"
    )]
    OddFamily { classes: usize },
    /// A class's image is no class of the family.
    #[error("class {class}'s image {image} is not a class of the family")]
    ImageOutside { class: usize, image: usize },
    /// A class is its own complement.
    #[error("class {class} is its own complement: a pairing has no fixed class")]
    FixedClass { class: usize },
    /// The complement of a class's complement is not the class.
    #[error(
        "the complement of class {class}'s complement is not the class: a pairing is an involution"
    )]
    NotInvolution { class: usize },
    /// The two roles differ in size, so the swap does not pair them one to one.
    #[error("the two roles name {first} and {second} classes: the free swap pairs them one to one")]
    RoleLengths { first: usize, second: usize },
}

/// [definition] **`σ` resolved**: a fixed-point-free involution of an even family of the chart's
/// classes, with the family's classes paired in twos. Built only by
/// [`PairingDeclaration::resolve`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Sigma {
    kind: PairingKind,
    image: Vec<Option<usize>>,
    pairs: Vec<(usize, usize)>,
}

impl Sigma {
    /// How the pairing was declared.
    pub fn kind(&self) -> PairingKind {
        self.kind
    }

    /// The chart's class count `|A|`.
    pub fn classes(&self) -> usize {
        self.image.len()
    }

    /// `σ(class)`, `None` outside the family.
    pub fn image(&self, class: usize) -> Option<usize> {
        self.image.get(class).copied().flatten()
    }

    /// `σ` on every class of the chart: `None` outside the family.
    pub fn table(&self) -> &[Option<usize>] {
        &self.image
    }

    /// The family's classes in twos, `(leader, follower)`: the lower class of each pair of a family
    /// declared as such, and the first role's class of a roles declaration. The leader's column of a
    /// port is free, and the follower's is forced by equivariance.
    pub fn pairs(&self) -> &[(usize, usize)] {
        &self.pairs
    }
}

impl PairingDeclaration {
    /// **The family declaration of the native duplex's pairing** (`compression::keys::duplex`): one
    /// `σ` declared once serves the duplex's located transport and this carrier, over the same
    /// chart. The duplex pairs a whole chart; this carrier can also declare a sub-family or two
    /// roles ([`PairingDeclaration::Roles`]).
    pub fn of_duplex(pairing: &Pairing) -> Self {
        Self::Family {
            table: (0..pairing.classes())
                .filter_map(|class| pairing.pair(class).map(|image| (class, image)))
                .collect(),
        }
    }

    /// **Resolve the declaration over a chart of `alphabet` classes**, or refuse it, typed. A family
    /// is checked in this order: non-empty, every class and image on the chart, each class once,
    /// an even size, every image a class of the family, then per row (in the table's order) no fixed
    /// class and an involution. Two roles are checked as: equal size, non-empty, then every class on
    /// the chart and named once across both roles.
    pub fn resolve(&self, alphabet: usize) -> Result<Sigma, PairingDefect> {
        match self {
            Self::Family { table } => resolve_family(table, alphabet),
            Self::Roles { first, second } => resolve_roles(first, second, alphabet),
        }
    }
}

fn resolve_family(table: &[(usize, usize)], alphabet: usize) -> Result<Sigma, PairingDefect> {
    if table.is_empty() {
        return Err(PairingDefect::Empty);
    }
    for &(class, partner) in table {
        for found in [class, partner] {
            if found >= alphabet {
                return Err(PairingDefect::ClassOutside {
                    class: found,
                    alphabet,
                });
            }
        }
    }
    let mut member = vec![false; alphabet];
    for &(class, _) in table {
        if member[class] {
            return Err(PairingDefect::ClassRepeated { class });
        }
        member[class] = true;
    }
    if table.len() % 2 == 1 {
        return Err(PairingDefect::OddFamily {
            classes: table.len(),
        });
    }
    let mut image: Vec<Option<usize>> = vec![None; alphabet];
    for &(class, partner) in table {
        image[class] = Some(partner);
        if !member[partner] {
            return Err(PairingDefect::ImageOutside {
                class,
                image: partner,
            });
        }
    }
    let mut pairs = Vec::with_capacity(table.len() / 2);
    for &(class, partner) in table {
        if partner == class {
            return Err(PairingDefect::FixedClass { class });
        }
        if image[partner] != Some(class) {
            return Err(PairingDefect::NotInvolution { class });
        }
        if class < partner {
            pairs.push((class, partner));
        }
    }
    Ok(Sigma {
        kind: PairingKind::Family,
        image,
        pairs,
    })
}

fn resolve_roles(
    first: &[usize],
    second: &[usize],
    alphabet: usize,
) -> Result<Sigma, PairingDefect> {
    if first.len() != second.len() {
        return Err(PairingDefect::RoleLengths {
            first: first.len(),
            second: second.len(),
        });
    }
    if first.is_empty() {
        return Err(PairingDefect::Empty);
    }
    let mut named = vec![false; alphabet];
    for &class in first.iter().chain(second) {
        if class >= alphabet {
            return Err(PairingDefect::ClassOutside { class, alphabet });
        }
        if named[class] {
            return Err(PairingDefect::ClassRepeated { class });
        }
        named[class] = true;
    }
    let mut image: Vec<Option<usize>> = vec![None; alphabet];
    let mut pairs = Vec::with_capacity(first.len());
    for (&leader, &follower) in first.iter().zip(second) {
        image[leader] = Some(follower);
        image[follower] = Some(leader);
        pairs.push((leader, follower));
    }
    Ok(Sigma {
        kind: PairingKind::Roles,
        image,
        pairs,
    })
}

// -------------------------------------------------------------------------------------------
// the defects

/// [definition] **Every refusal of the paired carrier**: a typed return naming the ring, class, column
/// or count it stands on, never a panic and never a string. The refusals of the moment's own carrier
/// ([`DyadRefusal`]) and of the HNN ([`HnnError`]) are carried, not restated.
#[derive(Debug, Error, PartialEq)]
pub enum PairedDefect {
    /// The ring is no ring of the field.
    #[error("ring {ring} lies outside a field of {rings} rings")]
    RingOutside { ring: usize, rings: usize },
    /// The ring has no source port to pair.
    #[error("ring {ring} is not a source ring: it has no source port E_g to pair")]
    NotSource { ring: usize },
    /// The reflector is not a reflection of the rotor.
    #[error("ring {ring}'s reflector is refused: {defect}")]
    Reflector {
        ring: usize,
        defect: ReflectorDefect,
    },
    /// The declared pairing is refused.
    #[error("the declared pairing is refused: {0}")]
    Pairing(#[from] PairingDefect),
    /// A port of another shape than `2d × |A|`.
    #[error(
        "a source port of {rows} × {columns} against the ring's {expected_rows} × {expected_columns}"
    )]
    PortShape {
        rows: usize,
        columns: usize,
        expected_rows: usize,
        expected_columns: usize,
    },
    /// The port is not equivariant: `B E e_column` differs from `E e_partner` at `row`, the first
    /// failing column of the family (in class order) and its first differing row.
    #[error(
        "ring {ring}'s source port is not equivariant: column {column} against its partner column {partner} first differs at row {row}, where B E e_{column} must equal E e_{partner}"
    )]
    Equivariance {
        ring: usize,
        column: usize,
        partner: usize,
        row: usize,
    },
    /// A vector of another width than the ring's carrier.
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    /// The field's ring is not the ring the carrier was admitted on.
    #[error("the field's ring {ring} is not the ring this carrier was admitted on")]
    ForeignField { ring: usize },
    /// The constitution's transport is not one: the weights read the ages, which a reversed passage
    /// reverses.
    #[error(
        "ring {ring}'s transport has modulus {modulus}, not one: a transport below one weighs a datum by its age, and a reversed passage reverses its ages"
    )]
    Transport { ring: usize, modulus: Box<Rat> },
    /// The constitution carries no source port for the ring.
    #[error("the constitution carries no source port for ring {ring}")]
    MissingSourcePort { ring: usize },
    /// An earlier ring of the carry chain ticks, so it may carry into the paired ring.
    #[error(
        "ring {earlier} precedes ring {ring} in the carry chain and has a nonempty lock: it may carry into the paired ring, whose tick is then not one a cell"
    )]
    CarriedClock { ring: usize, earlier: usize },
    /// A class of the family does not fit the ring's lock, so it does not tick the ring.
    #[error(
        "class {class} of the family does not fit ring {ring}'s lock: it does not tick the ring, so the tick is not one a cell"
    )]
    LockMisses { ring: usize, class: usize },
    /// The declared prior `E_0` a deposit reads is not equivariant, so the reversal identity's
    /// hypothesis fails: the first failing column, its partner and row, as [`PairedDefect::Equivariance`].
    #[error(
        "ring {ring}'s declared prior is not equivariant: column {column} against its partner column {partner} first differs at row {row}"
    )]
    PriorEquivariance {
        ring: usize,
        column: usize,
        partner: usize,
        row: usize,
    },
    /// A located class lies outside the pairing's family, so its dyad image is not defined.
    #[error("located class {class} lies outside ring {ring}'s paired family: it has no dyad image")]
    OutsideFamily { ring: usize, class: usize },
    /// The pair-port reversal law's check failed: the lift of a located pair's slip differs from the
    /// slip its dyad image reads against the clock, at `row`.
    #[error(
        "the lift of pair {antecedent} → {consequence}'s slip differs from its dyad image's at row {row}: the reversal law's check fails"
    )]
    Reversal {
        ring: usize,
        antecedent: usize,
        consequence: usize,
        row: usize,
    },
    /// The deposit's successor port is not equivariant (the re-admission after the deposit): the
    /// first failing column, its partner and row.
    #[error(
        "ring {ring}'s deposited source port is not equivariant: column {column} against its partner column {partner} first differs at row {row}"
    )]
    Deposited {
        ring: usize,
        column: usize,
        partner: usize,
        row: usize,
    },
    /// The moment is not a strand the dyad reads.
    #[error(transparent)]
    Dyad(#[from] DyadRefusal),
    /// A refusal of the HNN's own owners.
    #[error(transparent)]
    Hnn(Box<HnnError>),
}

impl From<HnnError> for PairedDefect {
    fn from(error: HnnError) -> Self {
        Self::Hnn(Box::new(error))
    }
}

impl From<ExactLinearError> for PairedDefect {
    fn from(error: ExactLinearError) -> Self {
        Self::Hnn(Box::new(HnnError::Linear(error)))
    }
}

// -------------------------------------------------------------------------------------------
// the carrier

/// [definition; agent-inferred, October 8] **A paired carrier**: a source ring whose reflector is a
/// dihedral reflection of its rotor (`F(i) = c − i`), whose realified lift `B` inverts the rotor on
/// the carrier, and whose declared class pairing `σ` its source port carried at the admission
/// (module header). It holds the dihedral structure and `σ`, and **no port**: the port is plastic,
/// so each reading takes the port it reads and certifies it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairedCarrier {
    ring: usize,
    axis: usize,
    reflector: Vec<usize>,
    sigma: Sigma,
}

impl PairedCarrier {
    /// The ring, the reflector and the pairing, with no port: everything the field and the
    /// declaration fix.
    fn frame(
        field: &Field,
        ring: usize,
        declared: &PairingDeclaration,
    ) -> Result<Self, PairedDefect> {
        let geometry = field.rings().get(ring).ok_or(PairedDefect::RingOutside {
            ring,
            rings: field.rings().len(),
        })?;
        if !field.is_source(ring) {
            return Err(PairedDefect::NotSource { ring });
        }
        let reflector = geometry.reflector().images().to_vec();
        if let Some(defect) = reflector_defect(&reflector) {
            return Err(PairedDefect::Reflector { ring, defect });
        }
        let sigma = declared.resolve(field.alphabet())?;
        Ok(Self {
            ring,
            axis: reflector[0],
            reflector,
            sigma,
        })
    }

    /// **Admit a paired carrier** (module header, "The admission"): source ring `ring` of `field`,
    /// the declared pairing and the source port `E_g` (`2d_g × |A|`). Certified in this order, each
    /// refusal typed: the ring and that it is a source, `F² = 1`, the dihedral relation at every
    /// port, the pairing (`σ² = id`, no fixed class, an even family or the free swap of two
    /// roles), the port's shape, and `B E = E Σ_σ` column by column, the first failing column
    /// named. The field's `Ring::declare` is not tightened. The admission certifies the carrier and
    /// the port it is handed, at one moment; the tick is certified at each read.
    pub fn admit(
        field: &Field,
        ring: usize,
        declared: &PairingDeclaration,
        port: &ExactRatMatrix,
    ) -> Result<Self, PairedDefect> {
        let carrier = Self::frame(field, ring, declared)?;
        carrier.certify(port)?;
        Ok(carrier)
    }

    /// **The equivariant port of a free one**: the carrier's frame admitted (everything but the port
    /// certificate), then [`PairedCarrier::equivariant_port`]. Construction of a port from the
    /// declared pairing, `E(σa) = B E(a)` on each pair, is a declared structure of the code's own
    /// kind, not a decoder.
    pub fn complete_port(
        field: &Field,
        ring: usize,
        declared: &PairingDeclaration,
        free: &ExactRatMatrix,
    ) -> Result<ExactRatMatrix, PairedDefect> {
        Self::frame(field, ring, declared)?.equivariant_port(free)
    }

    /// The source ring.
    pub fn ring(&self) -> usize {
        self.ring
    }

    /// `c = F(0)`: the reflector is `F(i) = c − i` (mod `d`), the half-turn about the dyad at `c/2`.
    pub fn axis(&self) -> usize {
        self.axis
    }

    /// `F`, as the images of the ports.
    pub fn reflector(&self) -> &[usize] {
        &self.reflector
    }

    /// The ring's period `d`.
    pub fn period(&self) -> usize {
        self.reflector.len()
    }

    /// The realified carrier's width `2d`.
    pub fn width(&self) -> usize {
        2 * self.reflector.len()
    }

    /// `σ`, resolved on the chart.
    pub fn sigma(&self) -> &Sigma {
        &self.sigma
    }

    /// **`B E = E Σ_σ`, column by column** (module header, "The admission"): for each class `a` of
    /// the family in ascending order, `(B E e_a)[row] = E[2F(j) + r][a]` must equal
    /// `E[row][σ(a)]` at every `row = 2j + r`. The first failing column (and its first differing
    /// row) is named; an equivariant port carries `σ` through the founded quotient, since
    /// `E e_a = E e_b` then forces `E e_(σa) = E e_(σb)`. Classes outside the family are not read.
    ///
    /// The carrier keeps no port, so every reading calls this on the port it reads.
    pub fn certify(&self, port: &ExactRatMatrix) -> Result<(), PairedDefect> {
        let width = self.width();
        let classes = self.sigma.classes();
        if port.rows() != width || port.columns() != classes {
            return Err(PairedDefect::PortShape {
                rows: port.rows(),
                columns: port.columns(),
                expected_rows: width,
                expected_columns: classes,
            });
        }
        for class in 0..classes {
            let Some(partner) = self.sigma.image(class) else {
                continue;
            };
            for row in 0..width {
                let source = 2 * self.reflector[row / 2] + row % 2;
                if port.get(source, class)? != port.get(row, partner)? {
                    return Err(PairedDefect::Equivariance {
                        ring: self.ring,
                        column: class,
                        partner,
                        row,
                    });
                }
            }
        }
        Ok(())
    }

    /// **A free port completed to an equivariant one**: the leader column of each pair is kept as
    /// given, the follower's is set to `B` of it, `E e_(σa) = B E e_a`, and the classes outside the
    /// family keep their columns. It is the port with the most freedom the pairing allows.
    pub fn equivariant_port(&self, free: &ExactRatMatrix) -> Result<ExactRatMatrix, PairedDefect> {
        let width = self.width();
        let classes = self.sigma.classes();
        if free.rows() != width || free.columns() != classes {
            return Err(PairedDefect::PortShape {
                rows: free.rows(),
                columns: free.columns(),
                expected_rows: width,
                expected_columns: classes,
            });
        }
        let mut rows = free.to_rows();
        for &(leader, follower) in self.sigma.pairs() {
            for (row, entries) in rows.iter_mut().enumerate() {
                let source = 2 * self.reflector[row / 2] + row % 2;
                entries[follower] = free.get(source, leader)?.clone();
            }
        }
        Ok(ExactRatMatrix::shaped(width, classes, rows)?)
    }

    /// **`B v`**, the realified lift of the reflector (module header): node `i`'s pair of
    /// coordinates moves to node `F(i)`. `B² = 1` and `B P B = P⁻¹`.
    pub fn lift(&self, vector: &[Rat]) -> Result<Vec<Rat>, PairedDefect> {
        let width = self.width();
        if vector.len() != width {
            return Err(PairedDefect::Shape {
                what: "a vector on the paired ring's carrier",
                expected: width,
                found: vector.len(),
            });
        }
        let mut lifted = vec![Rat::zero(); width];
        for (node, &image) in self.reflector.iter().enumerate() {
            lifted[2 * image] = vector[2 * node].clone();
            lifted[2 * image + 1] = vector[2 * node + 1].clone();
        }
        Ok(lifted)
    }

    /// **The ring this carrier was admitted on, read in `field`**: refused, `ForeignField`, unless
    /// the field's ring is a source ring with this reflector over this chart.
    fn ring_of<'f>(&self, field: &'f Field) -> Result<&'f Ring, PairedDefect> {
        let geometry = field
            .rings()
            .get(self.ring)
            .ok_or(PairedDefect::RingOutside {
                ring: self.ring,
                rings: field.rings().len(),
            })?;
        if geometry.reflector().images() != self.reflector.as_slice()
            || field.alphabet() != self.sigma.classes()
            || !field.is_source(self.ring)
        {
            return Err(PairedDefect::ForeignField { ring: self.ring });
        }
        Ok(geometry)
    }

    /// **`B Pᵏ v`**, the half-turn of the carrier about the dyad at `(c − k)/2`: the rotor's `k`-th
    /// power (`Ring::rotate`, signed) and then the lift. `(B Pᵏ)² = 1` (Lean
    /// `dihedral_reflection_sq`, `partner_map_involutive`), and `B Pᵏ = P⁻ᵏ B`.
    pub fn half_turn(
        &self,
        field: &Field,
        vector: &[Rat],
        turns: &BigInt,
    ) -> Result<Vec<Rat>, PairedDefect> {
        let geometry = self.ring_of(field)?;
        if vector.len() != geometry.width() {
            return Err(PairedDefect::Shape {
                what: "a vector on the paired ring's carrier",
                expected: geometry.width(),
                found: vector.len(),
            });
        }
        self.lift(&geometry.rotate(vector, turns))
    }

    /// **The unit tick, certified from the field** (module header): no earlier ring of the carry
    /// chain has a lock (an empty lock never ticks, so never wraps, so never carries), and every
    /// class of the family fits the source ring's lock (a class is its own port there). The ring then
    /// ticks once a cell on every cell of the family.
    fn uniform_tick(&self, field: &Field) -> Result<(), PairedDefect> {
        let geometry = self.ring_of(field)?;
        if let Some(earlier) = field.rings()[..self.ring]
            .iter()
            .position(|earlier| !earlier.notches().is_empty())
        {
            return Err(PairedDefect::CarriedClock {
                ring: self.ring,
                earlier,
            });
        }
        for class in 0..self.sigma.classes() {
            if self.sigma.image(class).is_some() && !geometry.fits(geometry.port(class)) {
                return Err(PairedDefect::LockMisses {
                    ring: self.ring,
                    class,
                });
            }
        }
        Ok(())
    }

    /// **The partner strand's moment** of a strand's `SourceMoment`, opened at phase
    /// `partner_opening` of the paired ring: [`SourceMoment::dyad`] with this carrier's `σ`, after
    /// the unit tick is certified from the field. `current` is the strand's reached lift point. On a
    /// unit-tick passage it equals, as a value, the moment ingest of `σ̄(u)` makes from a Current
    /// re-keyed to `partner_opening`. Refused, typed, as the module header lists.
    pub fn partner_moment(
        &self,
        field: &Field,
        current: &Current,
        strand: &SourceMoment,
        partner_opening: u64,
    ) -> Result<SourceMoment, PairedDefect> {
        self.uniform_tick(field)?;
        Ok(strand.dyad(
            field,
            current,
            self.ring,
            self.sigma.table(),
            partner_opening,
        )?)
    }

    /// **The partner's face, read through the actual moment** (module header). In order: the
    /// carrier's ring in `field`; the constitution's transport is one; the source port the
    /// constitution holds **now** is equivariant (re-certified here, so a deposit that took it off
    /// the subspace is refused, the first failing column named); the partner's moment
    /// ([`PairedCarrier::partner_moment`]); then the partner's open storage by
    /// `SourceMoment::open_storage` on that moment, beside the strand's own open storage carried by
    /// the half-turn `B P^(−(n−1))`. The two are returned with their exact residual
    /// ([`PartnerFace`]).
    pub fn partner_face(
        &self,
        field: &Field,
        constitution: &dyn FieldMaterial,
        current: &Current,
        strand: &SourceMoment,
        partner_opening: u64,
    ) -> Result<PartnerFace, PairedDefect> {
        self.ring_of(field)?;
        let modulus = constitution.transport(self.ring);
        if !modulus.is_one() {
            return Err(PairedDefect::Transport {
                ring: self.ring,
                modulus: Box::new(modulus),
            });
        }
        let port = constitution
            .source_port(self.ring)
            .ok_or(PairedDefect::MissingSourcePort { ring: self.ring })?;
        self.certify(port)?;
        let partner = self.partner_moment(field, current, strand, partner_opening)?;
        let mut lift = current.lift().to_vec();
        lift[self.ring] = partner.opening()[self.ring].clone() + BigInt::from(strand.cells());
        let partner_current = Current::at(field, lift)?;
        let read = partner.open_storage(field, constitution, &partner_current)?;
        let forward = strand.open_storage(field, constitution, current)?;
        let turns = BigInt::one() - BigInt::from(strand.cells());
        let transported = self.half_turn(field, &forward[self.ring], &turns)?;
        Ok(PartnerFace {
            read: read[self.ring].clone(),
            transported,
        })
    }

    /// **The equivariant deposit of a located pair** (module header, "The paired deposit"): the
    /// located pair `y → f(y)` at `+δ` and its dyad image `σy → σf(y)` read against the clock at `−δ`,
    /// every read one sample of one certified step (`hnn::executed::deposit_reads`). In order, each
    /// refusal typed: the carrier's ring in `field`; the source port the constitution holds now and the
    /// declared prior `E_0` are equivariant ([`PairedDefect::Equivariance`],
    /// [`PairedDefect::PriorEquivariance`]); every located class is in the family
    /// ([`PairedDefect::OutsideFamily`]); at every pair the lift of the forward slip is the slip of its
    /// dyad image, `B Δ_y = Δ^R` ([`PairedDefect::Reversal`]); the certified deposit
    /// (`hnn::executed::pair_deposit`'s conditions); and the successor port is re-admitted
    /// ([`PairedDefect::Deposited`]).
    pub fn deposit(
        &self,
        field: &Field,
        constitution: &Constitution,
        prior: &ExactRatMatrix,
        located: &LocatedPair,
    ) -> Result<(Constitution, PairDeposit), PairedDefect> {
        self.ring_of(field)?;
        let ring = self.ring;
        let port = constitution
            .source_port(ring)
            .ok_or(PairedDefect::MissingSourcePort { ring })?
            .clone();
        self.certify(&port)?;
        self.certify(prior).map_err(|defect| match defect {
            PairedDefect::Equivariance {
                ring,
                column,
                partner,
                row,
            } => PairedDefect::PriorEquivariance {
                ring,
                column,
                partner,
                row,
            },
            other => other,
        })?;
        let image = |class: usize| {
            self.sigma
                .image(class)
                .ok_or(PairedDefect::OutsideFamily { ring, class })
        };
        let classes = located
            .map
            .iter()
            .map(|&(from, to)| Ok((class_at(field, ring, from)?, class_at(field, ring, to)?)))
            .collect::<Result<Vec<(usize, usize)>, HnnError>>()?;
        let reversed = classes
            .iter()
            .map(|&(y, x)| Ok((image(y)?, image(x)?)))
            .collect::<Result<Vec<(usize, usize)>, PairedDefect>>()?;
        let forward = BigInt::from(located.offset);
        let backward = -&forward;
        for (&(y, x), &pair) in classes.iter().zip(&reversed) {
            let lifted = self.lift(&oriented_slip(field, ring, &port, prior, &forward, (y, x))?)?;
            let against = oriented_slip(field, ring, &port, prior, &backward, pair)?;
            if let Some(row) = lifted.iter().zip(&against).position(|(a, b)| a != b) {
                return Err(PairedDefect::Reversal {
                    ring,
                    antecedent: y,
                    consequence: x,
                    row,
                });
            }
        }
        let reads: Vec<OrientedRead> = classes
            .iter()
            .map(|&pair| (forward.clone(), pair))
            .chain(reversed.iter().map(|&pair| (backward.clone(), pair)))
            .collect();
        let (next, deposited) = deposit_reads(field, constitution, prior, ring, &reads)?;
        let successor = next
            .source_port(ring)
            .ok_or(PairedDefect::MissingSourcePort { ring })?;
        self.certify(successor).map_err(|defect| match defect {
            PairedDefect::Equivariance {
                ring,
                column,
                partner,
                row,
            } => PairedDefect::Deposited {
                ring,
                column,
                partner,
                row,
            },
            other => other,
        })?;
        Ok((
            next,
            PairDeposit {
                offset: located.offset,
                classes,
                reversed,
                slip_before: deposited.slip_before,
                slip_after: deposited.slip_after,
                certificate: deposited.certificate,
                consumer: deposited.consumer,
                source: deposited.source,
            },
        ))
    }
}

/// [definition] **A partner's face and what the strand's face carries it to**: `read` is the
/// partner's open storage on the paired ring by `SourceMoment::open_storage` on the partner's
/// moment, `transported` is `B P^(−(n−1))` of the strand's own open storage. They are equal where the
/// read is admitted (module header); the difference is returned exactly, never hidden.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartnerFace {
    /// `s(0)(σ̄u)`, read through the partner's moment.
    pub read: Vec<Rat>,
    /// `B P^(−(n−1)) s(0)(u)`.
    pub transported: Vec<Rat>,
}

impl PartnerFace {
    /// `read − transported`, entry by entry, exactly.
    pub fn residual(&self) -> Vec<Rat> {
        self.read
            .iter()
            .zip(&self.transported)
            .map(|(read, transported)| read - transported)
            .collect()
    }

    /// Whether the residual is zero in every entry.
    pub fn is_exact(&self) -> bool {
        self.read == self.transported
    }
}

#[cfg(test)]
mod tests;
