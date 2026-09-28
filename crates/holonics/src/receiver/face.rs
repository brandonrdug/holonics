//! **Receivers as Holons at ports: the passive coholon, the active receiver and the reading face.**
//!
//! [definition] A receiver is a role of a Holon joined at ports
//! ([object](../../../../docs/ELEMENTARY_OBJECTS.md#10-receipt)), and there are exactly three things
//! a receiver-named type can be.
//!
//! * **The passive coholon** ([`PassiveCoholon`]): the zero-storage, zero-flow limit that admits
//!   every effort and draws no power (`Holon/Law.passiveCoholon`,
//!   `Holon/Law.passiveCoholon_isDirac`). Its linear reading `C e` is
//!   `Holon/Law.passive_reading`; any reading of its bond, linear or not, draws zero power
//!   (`Holon/Law.coholon_reading_power`). [`LinearReading`] is this object with a declared name.
//! * **An active receiver** ([`ActiveReceiver`]): a receiver that returns something into the Holon
//!   it reads, entering with its actual power term ([`ReceiverPower`]). Joined through an interface
//!   conductance it satisfies `Holon/Law.active_receiver_law` ([`crate::holon::law::active_receiver`]);
//!   a learned linear relation carries `⟨f, L f⟩` ([`crate::holon::element::ActiveRelation`]); a nonlinear
//!   reading that injects a current `y` at drive ports carries the exterior power `⟨e_D, y⟩`, whose
//!   own balance closes exactly (`Holon/Law.exterior_drive_balance`); a covector pullback
//!   through the producing Jacobian's transpose is power preserving (`Holon/Law.pullback_law`,
//!   `Holon/Law.softmaxJacobian_transpose`).
//! * **A receiver face** (a codec projection): the exact value a reading returns ([`ExactFace`]),
//!   the declared norm ([`DiameterNorm`]), the diameter over a fibre ([`ReceiverWidth`],
//!   [`width_over_readings`]), the two-axis [`Horizon`] and the relation ladder's [`Rung`]. A face
//!   is what a coholon's value is charted as; it is not itself a port object. **A face read at a
//!   grain** keeps its carry, phase class and unresolved fibre ([`GrainCell`]), and the base-two
//!   logarithm of a ratio read at a grain is decided by integer comparison ([`grain_exponent`]);
//!   the HNN's receiving read (`hnn::receiving`) and the context tree's faces
//!   (`compression::landmark::context`) consume both.
//!
//! Release decisions are [`crate::receiver::release`], the one decision law.
//!
//! | Lean | Rust |
//! |---|---|
//! | `passiveCoholon`, `passiveCoholon_isDirac` | [`PassiveCoholon::dirac`] |
//! | `passive_reading` | [`PassiveCoholon::read`]; within reception, [`crate::holon::law::HolonLaw::receive`] |
//! | `coholon_reading_power` | [`coholon_bond`], [`PassiveCoholon::read_face`] |
//! | `exterior_drive_balance` | [`ActiveReceiver::drive_balance`] |
//! | `learned_receiver_balance` | [`ActiveReceiver::learned_balance`] |
//! | `softmaxJacobian`, `softmaxJacobian_transpose`, `pullback_law` | [`softmax_jacobian`], [`ActiveReceiver::pullback_balance`] |
//! | `active_receiver_law` | [`crate::holon::law::active_receiver`] |
//! | `Foundation/ReceiverRelease.width`, `width_nonneg`, `abs_sub_le_width` | [`width_over_readings`], [`ReceiverWidth`] |
//! | `Foundation/ReceiverRelease.Horizon`, `Horizon.Within`, `horizonWithin_is_not_total` | [`Horizon`], [`Horizon::contains`], [`Horizon::comparable`] |
//! | `Foundation/RelationLadder.Rung`, `Rung.entailed`, `Rung.entails`, `rungMeet` | [`Rung`], [`rung_meet`] |
//! | `HNN/Ratio.{grainRead, grainFibre, face_constant_on_fibre}` (the face reads only the grain cell) | [`GrainCell`] |
//! | `HNN/RegionCounts.{grainExponent_spec, grain_log_iff_pow_bounds}` (`log₂` of a ratio read at the grain by integer comparison) | [`grain_exponent`] |

use std::fmt::Debug;

use crate::ratio::Rat;
use num_bigint::{BigInt, BigUint};
use num_traits::{Signed, ToPrimitive, Zero};
use thiserror::Error;

use crate::holon::HolonError;
use crate::holon::dirac::DiracStructure;
use crate::holon::element::ActiveRelation;
use crate::holon::law::{EnergyBalance, PassiveReading};
use crate::holon::port::Bond;
use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::vector::{dot, matrix, zeros};
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};

// =============================================================================================
// The passive coholon
// =============================================================================================

/// [definition] **The coholon bond of a reading**: zero flow and the read effort, checked to lie in
/// the passive coholon's Dirac structure. Whatever function of the effort a receiver then computes —
/// linear or not — the bond it stands on draws zero power (`Holon/Law.coholon_reading_power`).
pub fn coholon_bond(effort: &[Rat]) -> Result<Bond, HolonError> {
    let bond = Bond::new(zeros(effort.len()), effort.to_vec())?;
    if !DiracStructure::passive_coholon(effort.len())?.contains(&bond)? {
        return Err(HolonError::NotAdmitted);
    }
    Ok(bond)
}

/// [definition] **The passive coholon with a declared linear reader** `C`: joined at a Holon's
/// ports it forces zero flow there, admits every effort, reads `C e` and draws zero power
/// (`Holon/Law.passive_reading`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassiveCoholon {
    receiver: String,
    reader: ExactRatMatrix,
}

impl PassiveCoholon {
    /// The coholon on `reader.columns()` ports with the declared name.
    pub fn new(receiver: impl Into<String>, reader: ExactRatMatrix) -> Self {
        Self {
            receiver: receiver.into(),
            reader,
        }
    }

    /// The receiver's declared name.
    pub fn receiver(&self) -> &str {
        &self.receiver
    }

    /// The linear reader `C`.
    pub fn reader(&self) -> &ExactRatMatrix {
        &self.reader
    }

    /// The ports it joins: the columns of `C`.
    pub fn ports(&self) -> usize {
        self.reader.columns()
    }

    /// Its interconnection: the passive coholon Dirac structure on its ports
    /// (`Holon/Law.passiveCoholon_isDirac`).
    pub fn dirac(&self) -> Result<DiracStructure, HolonError> {
        DiracStructure::passive_coholon(self.ports())
    }

    /// **Read one effort**: the bond `(0, e)` is checked admitted, the value is `C e` and the power
    /// drawn is the bond's, which is zero.
    pub fn read(&self, effort: &[Rat]) -> Result<PassiveReading, HolonError> {
        if effort.len() != self.ports() {
            return Err(HolonError::Shape {
                what: "passive coholon effort",
                expected: self.ports(),
                found: effort.len(),
            });
        }
        let bond = coholon_bond(effort)?;
        Ok(PassiveReading {
            value: self.reader.apply(bond.effort())?,
            power: bond.power(),
        })
    }

    /// The same reading charted as a receiver face.
    pub fn read_face(&self, effort: &[Rat]) -> Result<(ExactFace, Rat), HolonError> {
        let reading = self.read(effort)?;
        Ok((ExactFace::Vector(reading.value), reading.power))
    }
}

impl Reading for PassiveCoholon {
    fn name(&self) -> &str {
        &self.receiver
    }

    /// The state is read as the effort under the unit storage chart.
    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        Ok(ExactFace::Vector(self.reader.apply(state)?))
    }
}

impl LinearReading {
    /// **This reading as the passive coholon** with the same name and reader. The reading reads a
    /// state; the coholon reads that state as the effort under the unit storage chart, so the two
    /// values are equal entry for entry, and the coholon adds the zero-power statement.
    pub fn passive_coholon(&self) -> PassiveCoholon {
        PassiveCoholon::new(self.receiver.clone(), self.matrix.clone())
    }
}

impl From<&LinearReading> for PassiveCoholon {
    fn from(reading: &LinearReading) -> Self {
        reading.passive_coholon()
    }
}

// =============================================================================================
// The active receiver
// =============================================================================================

/// [definition] **The power term an active receiver enters with.** Passivity is never assumed:
/// each arm names the term the joined Holon's [`EnergyBalance`] carries for it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReceiverPower {
    /// A (possibly nonlinear) reading at zero flow that returns a face and no current: power zero
    /// (`Holon/Law.coholon_reading_power`).
    Reading,
    /// A learned linear relation `e_A = L f_A` with its declared power `⟨f_A, L f_A⟩`.
    Learned(ActiveRelation),
    /// A nonlinear reading of its read ports that injects the current `y` at `drive_ports` ports of
    /// the Holon. It stores nothing; the power it delivers, `⟨e_D, y⟩` at the Holon's drive effort
    /// `e_D`, is supplied from its exterior and evaluated by the consumer that owns `e_D`
    /// (`Holon/Law.exterior_drive_balance`).
    ExteriorDrive { drive_ports: usize },
    /// A covector returned through the transpose of the producing Jacobian `P` (an adjoint or
    /// pullback return): efforts move by `Pᵀ` and the pairing is preserved,
    /// `⟨g, P δ⟩ = ⟨Pᵀ g, δ⟩` (`Holon/Law.pullback_law`). It stores and delivers nothing.
    /// The normalized face's `J_p = diag p − p pᵀ` is self-adjoint
    /// (`Holon/Law.softmaxJacobian_transpose`), so its return is `J_p g` itself.
    Pullback,
}

/// [definition] **An active receiver element**: a named receiver on `read_ports` ports with its
/// declared power term.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActiveReceiver {
    receiver: String,
    read_ports: usize,
    power: ReceiverPower,
}

/// [definition] **One exchange of an active receiver**: its own balance (zero storage, so
/// `0 = port + active` exactly) and the power it delivers into the joined Holon, which is that
/// Holon's additional active term ([`EnergyBalance::joined_active`]).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverExchange {
    pub own: EnergyBalance,
    pub delivered: Rat,
}

impl ActiveReceiver {
    pub fn declared(receiver: impl Into<String>, read_ports: usize, power: ReceiverPower) -> Self {
        Self {
            receiver: receiver.into(),
            read_ports,
            power,
        }
    }

    pub fn receiver(&self) -> &str {
        &self.receiver
    }

    pub fn read_ports(&self) -> usize {
        self.read_ports
    }

    pub fn power(&self) -> &ReceiverPower {
        &self.power
    }

    /// Whether the receiver is passive by declaration: a reading or a pullback always is, a
    /// learned relation when `n₊(sym L) = 0`, an exterior drive never by declaration (its sign is
    /// the consumer's).
    pub fn is_passive(&self) -> bool {
        match &self.power {
            ReceiverPower::Reading | ReceiverPower::Pullback => true,
            ReceiverPower::Learned(relation) => relation.is_passive(),
            ReceiverPower::ExteriorDrive { .. } => false,
        }
    }

    fn read_bond(&self, read_effort: &[Rat]) -> Result<Bond, HolonError> {
        if read_effort.len() != self.read_ports {
            return Err(HolonError::Shape {
                what: "active receiver read effort",
                expected: self.read_ports,
                found: read_effort.len(),
            });
        }
        coholon_bond(read_effort)
    }

    /// **A reading's exchange**: the coholon bond's power, which is zero, and nothing delivered.
    pub fn reading_balance(&self, read_effort: &[Rat]) -> Result<ReceiverExchange, HolonError> {
        if self.power != ReceiverPower::Reading {
            return Err(HolonError::Unsupported {
                what: "a reading balance",
                reason: "the receiver is not declared a reading",
            });
        }
        let bond = self.read_bond(read_effort)?;
        let zero = Rat::zero();
        Ok(ReceiverExchange {
            own: EnergyBalance::closed(
                zero.clone(),
                zero.clone(),
                bond.power(),
                zero.clone(),
                zero.clone(),
                zero.clone(),
            ),
            delivered: zero,
        })
    }

    /// **An exterior drive's exchange** (`Holon/Law.exterior_drive_balance`): the receiver
    /// reads at zero flow, injects `y = output` against the Holon's drive effort `e_D`, and is
    /// supplied `⟨e_D, y⟩` from its exterior. Its own balance is `0 = −⟨e_D, y⟩ + ⟨e_D, y⟩`,
    /// exactly; the Holon receives `⟨e_D, y⟩`.
    pub fn drive_balance(
        &self,
        read_effort: &[Rat],
        output: &[Rat],
        drive_effort: &[Rat],
    ) -> Result<ReceiverExchange, HolonError> {
        let ReceiverPower::ExteriorDrive { drive_ports } = self.power else {
            return Err(HolonError::Unsupported {
                what: "an exterior drive balance",
                reason: "the receiver is not declared an exterior drive",
            });
        };
        if output.len() != drive_ports || drive_effort.len() != drive_ports {
            return Err(HolonError::Shape {
                what: "exterior drive ports",
                expected: drive_ports,
                found: output.len().max(drive_effort.len()),
            });
        }
        let read = self.read_bond(read_effort)?;
        let delivered = dot(drive_effort, output);
        let zero = Rat::zero();
        Ok(ReceiverExchange {
            own: EnergyBalance::closed(
                zero.clone(),
                zero.clone(),
                read.power() - &delivered,
                delivered.clone(),
                zero.clone(),
                zero,
            ),
            delivered,
        })
    }

    /// **A learned relation's exchange** (`Holon/Law.learned_receiver_balance`): at flow
    /// `f_A` the relation's effort is `L f_A`; its declared power `⟨f_A, L f_A⟩` is what it delivers.
    pub fn learned_balance(&self, flow: &[Rat]) -> Result<ReceiverExchange, HolonError> {
        let ReceiverPower::Learned(relation) = &self.power else {
            return Err(HolonError::Unsupported {
                what: "a learned balance",
                reason: "the receiver is not declared a learned relation",
            });
        };
        let delivered = relation.power(flow)?;
        let zero = Rat::zero();
        Ok(ReceiverExchange {
            own: EnergyBalance::closed(
                zero.clone(),
                zero.clone(),
                -delivered.clone(),
                delivered.clone(),
                zero.clone(),
                zero,
            ),
            delivered,
        })
    }

    /// **A pullback's exchange** (`Holon/Law.pullback_law`): the returned covector `Pᵀ g`
    /// paired with a displacement `δ` equals `g` paired with the forward variation `P δ`. Returns
    /// both pairings, refused unless equal; nothing is delivered.
    pub fn pullback_balance(
        &self,
        forward: &ExactRatMatrix,
        covector: &[Rat],
        displacement: &[Rat],
    ) -> Result<(Rat, Rat), HolonError> {
        if self.power != ReceiverPower::Pullback {
            return Err(HolonError::Unsupported {
                what: "a pullback balance",
                reason: "the receiver is not declared a pullback",
            });
        }
        if forward.columns() != self.read_ports {
            return Err(HolonError::Shape {
                what: "pullback forward map columns",
                expected: self.read_ports,
                found: forward.columns(),
            });
        }
        let returned = dot(&forward.transpose()?.apply(covector)?, displacement);
        let forward = dot(covector, &forward.apply(displacement)?);
        if returned != forward {
            return Err(HolonError::NotAdmitted);
        }
        Ok((returned, forward))
    }
}

/// [definition] **The normalized face's Jacobian** `J_p = diag p − p pᵀ`, exactly
/// (`Holon/Law.softmaxJacobian`); it is symmetric (`softmaxJacobian_transpose`), so the
/// normalized receiver's covector return `J_p g` is a power-preserving pullback.
pub fn softmax_jacobian(p: &[Rat]) -> Result<SymmetricForm, HolonError> {
    let m = matrix(p.len(), p.len(), |row, column| {
        let outer = &p[row] * &p[column];
        if row == column {
            &p[row] - outer
        } else {
            -outer
        }
    })?;
    Ok(crate::ratio::linear::vector::matrix_form(&m)?)
}

// =============================================================================================
// The receiver face
// =============================================================================================

/// The ceiling on a declared horizon.
///
/// [definition] A horizon's step count is work sized by a caller declaration (each longitudinal
/// step is one exact transport), so [`Horizon::declare`] bounds both coordinates before any step.
pub const HORIZON_CEILING: usize = 4096;

/// The ceiling on the number of members an enumerated compatible family may declare.
///
/// [definition] A width over an enumerated family reads every unordered pair, so the work is
/// `n(n−1)/2`. The ceiling bounds `n`, and the pair count is formed with checked arithmetic.
pub const FAMILY_CEILING: usize = 4096;

/// An exact face returned by a receiver reading. Three arms, each exact; no float appears.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExactFace {
    /// A yes/no reading, separated by `1` when the two disagree.
    Flag(bool),
    /// An exact integer reading — a step count, a Betti number, a multiplicity.
    Count(BigInt),
    /// An exact rational vector reading.
    Vector(Vec<Rat>),
}

impl ExactFace {
    /// The name of this arm, for the incomparability refusal.
    pub fn arm(&self) -> &'static str {
        match self {
            Self::Flag(_) => "flag",
            Self::Count(_) => "count",
            Self::Vector(_) => "vector",
        }
    }

    /// **The exact separation of two faces in a declared norm.** Two faces of different arms are
    /// refused by name rather than coerced; two vectors of different lengths likewise.
    pub fn separation(&self, other: &Self, norm: DiameterNorm) -> Result<Rat, WidthRefusal> {
        match (self, other) {
            (Self::Flag(left), Self::Flag(right)) => Ok(if left == right {
                Rat::zero()
            } else {
                Rat::from_integer(BigInt::from(1))
            }),
            (Self::Count(left), Self::Count(right)) => {
                let difference = Rat::from_integer((left - right).abs());
                Ok(match norm {
                    DiameterNorm::Supremum => difference,
                    DiameterNorm::SquaredEuclidean => &difference * &difference,
                })
            }
            (Self::Vector(left), Self::Vector(right)) => {
                if left.len() != right.len() {
                    return Err(WidthRefusal::VectorFacesDiffer {
                        left: left.len(),
                        right: right.len(),
                    });
                }
                Ok(match norm {
                    DiameterNorm::Supremum => {
                        left.iter().zip(right).map(|(a, b)| (a - b).abs()).fold(
                            Rat::zero(),
                            |best, value| if value > best { value } else { best },
                        )
                    }
                    DiameterNorm::SquaredEuclidean => {
                        left.iter().zip(right).fold(Rat::zero(), |sum, (a, b)| {
                            let difference = a - b;
                            sum + &difference * &difference
                        })
                    }
                })
            }
            _ => Err(WidthRefusal::FacesIncomparable {
                left: self.arm(),
                right: other.arm(),
            }),
        }
    }
}

/// The declared exact norm the diameter is taken in.
///
/// [established-bounded] `SquaredEuclidean` is exact over read faces ([`width_over_readings`]). Over
/// an enclosure it is not: the Euclidean diameter of a zonotope is attained at a vertex of the
/// generator cube, so an exact computation would enumerate `2^k` sign patterns
/// ([RECEIVER_HOLARCHY](../../../../docs/RECEIVER_HOLARCHY.md#width-and-release)); a width an owner
/// bounds by an enclosure is declared in the supremum norm.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DiameterNorm {
    /// The sup-norm. Exact on both an enumerated family and an enclosure.
    Supremum,
    /// The squared Euclidean norm. Exact on an enumerated family only.
    SquaredEuclidean,
}

impl DiameterNorm {
    /// The name, for a refusal message.
    pub fn name(self) -> &'static str {
        match self {
            Self::Supremum => "supremum",
            Self::SquaredEuclidean => "squared-euclidean",
        }
    }
}

/// A declared exact reading of one compatible state. Implementors are the declared receivers;
/// the reading is `R ∘ Φ_h` already composed, exactly as the Lean owner says.
///
/// [definition] **A reading is the passive coholon's**: it reads the state at zero
/// flow, so whatever the function — linear ([`LinearReading`], [`PassiveCoholon`]) or not — the bond
/// it stands on is [`coholon_bond`] and the power it draws is zero
/// (`Holon/Law.coholon_reading_power`). A reading that returns a current into the Holon is
/// not a `Reading`; it is an [`ActiveReceiver`] with its [`ReceiverPower`].
pub trait Reading {
    /// The receiver's declared name. It appears in every refusal and in every returned width.
    fn name(&self) -> &str;

    /// The exact face this receiver reads off one compatible state.
    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal>;
}

/// An exact **linear** reading `R x`, the one reading that is exact on an enclosure as well as on
/// an enumerated family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearReading {
    /// The receiver's declared name.
    pub receiver: String,
    /// The exact matrix `R`.
    pub matrix: ExactRatMatrix,
}

impl Reading for LinearReading {
    fn name(&self) -> &str {
        &self.receiver
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        Ok(ExactFace::Vector(self.matrix.apply(state)?))
    }
}

/// **The width of a receiver reading over a compatible family.**
///
/// Lean counterpart: `Foundation/ReceiverRelease.width`.
///
/// [implemented-exact] Every field is private. The constructors are [`width_over_readings`] and
/// [`Self::declared`], which refuses a negative diameter or an attaining witness incoherent with its
/// own `read` count, so a forged width cannot be handed to
/// [`crate::receiver::release::LawfulOptions::assemble`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverWidth {
    receiver: String,
    lineage: String,
    norm: DiameterNorm,
    diameter: Rat,
    attaining: WidthWitness,
    read: usize,
}

impl ReceiverWidth {
    /// **A width declared by an owner that computed it** (an enclosure width). It passes the same
    /// structural checks as every other route.
    pub fn declared(
        receiver: impl Into<String>,
        lineage: impl Into<String>,
        norm: DiameterNorm,
        diameter: Rat,
        attaining: WidthWitness,
        read: usize,
    ) -> Result<Self, WidthRefusal> {
        if diameter.is_negative() {
            return Err(WidthRefusal::NegativeWidth {
                declared: diameter.to_string(),
            });
        }
        match &attaining {
            WidthWitness::Pair { left, right } => {
                if left >= right || *right >= read {
                    return Err(WidthRefusal::WitnessOutsideReading {
                        read,
                        witness: format!("{attaining:?}"),
                    });
                }
            }
            WidthWitness::Coordinate { .. } => {}
            WidthWitness::Point => {
                if !diameter.is_zero() {
                    return Err(WidthRefusal::WitnessOutsideReading {
                        read,
                        witness: "point witness with a nonzero diameter".to_owned(),
                    });
                }
            }
        }
        Ok(Self {
            receiver: receiver.into(),
            lineage: lineage.into(),
            norm,
            diameter,
            attaining,
            read,
        })
    }
}

impl ReceiverWidth {
    /// The receiver whose reading this is.
    pub fn receiver(&self) -> &str {
        &self.receiver
    }

    /// What the fibre is the fibre of.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The declared norm.
    pub fn norm(&self) -> DiameterNorm {
        self.norm
    }

    /// The exact diameter.
    pub fn diameter(&self) -> &Rat {
        &self.diameter
    }

    /// How the diameter was reached: the pair that attains it, or the coordinate of the enclosure.
    pub fn attaining(&self) -> &WidthWitness {
        &self.attaining
    }

    /// How many members were read, or how many generators the enclosure carried.
    pub fn read(&self) -> usize {
        self.read
    }

    /// **Width zero is exactly constancy on the fibre**, and exactly releasability at every
    /// tolerance.
    ///
    /// Lean counterpart: `width_eq_zero_iff` and
    /// `releasable_at_every_tolerance_iff_width_zero`.
    pub fn is_zero(&self) -> bool {
        self.diameter.is_zero()
    }

    /// Whether this width falls inside a declared tolerance.
    ///
    /// Lean counterpart: `Releasable`.
    pub fn releasable_at(&self, tolerance: &Rat) -> bool {
        &self.diameter <= tolerance
    }
}

/// How a width was attained: the content of the diameter, not a summary of it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WidthWitness {
    /// The two enumerated members whose readings are furthest apart.
    Pair {
        /// Index of the first member.
        left: usize,
        /// Index of the second member.
        right: usize,
    },
    /// The coordinate of the image enclosure whose extent is widest.
    Coordinate {
        /// Which coordinate.
        coordinate: usize,
    },
    /// The family is a single member, or the enclosure carries no generator: the width is zero and
    /// nothing attains it but the point itself.
    Point,
}

/// The ceiling on the index coordinate of a declared two-axis [`Horizon`].
///
/// [definition] The index coordinate counts steps through a tower's charts. Every step toward a
/// finer chart replaces a face by its **fibre**, so the population a reach carries is multiplied
/// rather than kept, and the coordinate is therefore work a caller declares. It is checked by
/// [`Horizon::declare`] before any reach is walked; the tube-side reach adds its own work ceiling
/// over the product of this coordinate with the chart and face populations.
pub(crate) const INDEX_HORIZON_CEILING: usize = 1024;

/// **A horizon with two coordinates: `h` longitudinal steps and `k` steps in the tower's index.**
///
/// [definition] `w_R(h)` — the width this module already owned — measures distance into the
/// horizon along one axis only. The second coordinate is distance in the **index**, in either
/// direction: `k` steps toward the finer charts or `k` steps toward the coarser ones. Brandon's
/// statement, September 18: *zooming from orbit down to an organism is as far into the horizon as
/// looking out to the stars*, and that is the same notion of distance in both directions.
///
/// [proved-derived; formal-checked] Lean counterpart:
/// `Foundation/ReceiverRelease.Horizon`, with `Horizon.Within` the product order,
/// `horizonWithin_refl`/`horizonWithin_trans` its two laws and `horizonWithin_is_not_total` the
/// statement that **the two coordinates are not one scale**: `(2, 0)` and `(0, 2)` are
/// incomparable horizons, so "how far into the horizon" is a pair and not a number, and no
/// lexicographic order is imposed on it here. That is why this type derives no `Ord`.
///
/// [implemented-exact] Both fields are private and the only constructors are [`Self::declare`] and
/// [`Self::longitudinal_only`], which check both ceilings.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Horizon {
    longitudinal: usize,
    index: usize,
}

impl Horizon {
    /// Declare a two-axis horizon, checking both coordinates against their ceilings before
    /// anything is sized by them.
    pub fn declare(longitudinal: usize, index: usize) -> Result<Self, WidthRefusal> {
        if longitudinal > HORIZON_CEILING {
            return Err(WidthRefusal::HorizonCeiling {
                requested: longitudinal,
                ceiling: HORIZON_CEILING,
            });
        }
        if index > INDEX_HORIZON_CEILING {
            return Err(WidthRefusal::IndexHorizonCeiling {
                requested: index,
                ceiling: INDEX_HORIZON_CEILING,
            });
        }
        Ok(Self {
            longitudinal,
            index,
        })
    }

    /// The horizon this module's existing width reads at: `h` longitudinal steps and `k = 0`.
    ///
    /// Lean counterpart: `Horizon.longitudinalOnly` and
    /// `twoAxisWidth_at_index_zero_is_the_longitudinal_width`, which is why every theorem already
    /// proved of `width` is the `k = 0` case of the two-axis width and is not restated.
    pub fn longitudinal_only(longitudinal: usize) -> Result<Self, WidthRefusal> {
        Self::declare(longitudinal, 0)
    }

    /// The longitudinal coordinate: steps of `Φ` along the tube.
    pub const fn longitudinal(&self) -> usize {
        self.longitudinal
    }

    /// The index coordinate: steps through the tower's charts, in either direction.
    pub const fn index(&self) -> usize {
        self.index
    }

    /// Whether this is the longitudinal-only horizon the one-axis width reads at.
    pub const fn is_longitudinal_only(&self) -> bool {
        self.index == 0
    }

    /// Whether `inner` lies inside this horizon, in the **product** order: no further along either
    /// axis. This is the order the monotonicity law is stated in, and it is partial.
    ///
    /// Lean counterpart: `Horizon.Within`.
    pub const fn contains(&self, inner: &Self) -> bool {
        inner.longitudinal <= self.longitudinal && inner.index <= self.index
    }

    /// Whether two horizons are comparable at all. `(2, 0)` and `(0, 2)` are not.
    ///
    /// Lean counterpart: `horizonWithin_is_not_total`.
    pub const fn comparable(&self, other: &Self) -> bool {
        self.contains(other) || other.contains(self)
    }
}

/// **The width of an already-read family of exact faces.**
///
/// [definition] **The finite width**: the diameter of a set of exact faces read over a compatible
/// family, in a declared norm, with the pair that attains it. It is the one Rust statement of the
/// finite width law; retention's extinction (`receiver::standing`) reads it.
///
/// Lean counterpart: `Foundation/ReceiverRelease.width`, with `abs_sub_le_width` the pair
/// that attains it and `width_nonneg` the sign. The declared face count is checked against
/// [`FAMILY_CEILING`] and its pair count formed with checked arithmetic before any pair is read.
pub fn width_over_readings(
    receiver: &str,
    lineage: &str,
    faces: &[ExactFace],
    norm: DiameterNorm,
) -> Result<ReceiverWidth, WidthRefusal> {
    if faces.is_empty() {
        return Err(WidthRefusal::EmptyFamily);
    }
    if faces.len() > FAMILY_CEILING {
        return Err(WidthRefusal::FamilyCeiling {
            declared: faces.len(),
            ceiling: FAMILY_CEILING,
        });
    }
    let count = faces.len();
    count
        .checked_mul(count.saturating_sub(1))
        .ok_or(WidthRefusal::PairCountOverflows { members: count })?;
    let mut diameter = Rat::zero();
    let mut attaining = WidthWitness::Point;
    for left in 0..faces.len() {
        for right in (left + 1)..faces.len() {
            let separation = faces[left].separation(&faces[right], norm)?;
            if separation > diameter {
                diameter = separation;
                attaining = WidthWitness::Pair { left, right };
            }
        }
    }
    Ok(ReceiverWidth {
        receiver: receiver.to_owned(),
        lineage: lineage.to_owned(),
        norm,
        diameter,
        attaining,
        read: faces.len(),
    })
}

/// The release a declared law claimed, with the tolerance it declared it against. Carried behind a
/// box inside [`WidthRefusal::ReleasedOutsideTolerance`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleasedClaim {
    /// The law that claimed it.
    pub law: String,
    /// The exact width it released.
    pub width: Rat,
    /// The exact tolerance it declared.
    pub tolerance: Rat,
}

/// A declared widening whose proposed tolerance is smaller than the measured width.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WidenClaim {
    /// The law that proposed it.
    pub law: String,
    /// The measured exact width that prompted widening.
    pub width: Rat,
    /// The exact tolerance the law proposed.
    pub tolerance: Rat,
}

/// Why a width or a release was refused. Every failure is returned as content.
#[derive(Debug, Error)]
pub enum WidthRefusal {
    /// A declared width is negative. A diameter is a maximum of absolute
    /// separations and is never negative (`width_nonneg`).
    #[error(
        "a receiver width of {declared} is negative; a diameter is a maximum of absolute separations"
    )]
    NegativeWidth {
        /// The declared diameter, as prose.
        declared: String,
    },
    /// A declared width's attaining witness does not index the reading it claims.
    #[error("an attaining witness {witness} does not index a reading of {read} members")]
    WitnessOutsideReading {
        /// How many members the width claims to have read.
        read: usize,
        /// The witness, as prose.
        witness: String,
    },
    /// A compatible family with no member has no diameter.
    #[error("a compatible family with no member has no width")]
    EmptyFamily,
    /// Two declared extents do not agree.
    #[error("a carrier of dimension {declared} does not pair with one of dimension {found}")]
    DimensionMismatch {
        /// What was declared.
        declared: usize,
        /// What was found.
        found: usize,
    },
    /// A declared horizon is longer than the ceiling admits.
    #[error(
        "a horizon of {requested} steps exceeds the declared ceiling {ceiling}; nothing was \
         allocated and no step was taken"
    )]
    HorizonCeiling {
        /// How many steps were asked for.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// A declared two-axis horizon reaches further through the index than the ceiling admits.
    #[error(
        "an index horizon of {requested} chart steps exceeds the declared ceiling {ceiling}; \
         no chart was walked and no fibre was opened"
    )]
    IndexHorizonCeiling {
        /// How many index steps were asked for.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// A declared enumerated family is wider than the ceiling admits.
    #[error(
        "an enumerated family of {declared} members exceeds the declared ceiling {ceiling}; \
         nothing was allocated"
    )]
    FamilyCeiling {
        /// How many were declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The pair count of a declared family does not fit a machine integer.
    #[error("the unordered pairs of {members} members overflow the machine integer counting them")]
    PairCountOverflows {
        /// How many members were declared.
        members: usize,
    },
    /// Two faces of different arms have no separation.
    #[error("a {left} face and a {right} face are incomparable and no separation is invented")]
    FacesIncomparable {
        /// The first arm.
        left: &'static str,
        /// The second arm.
        right: &'static str,
    },
    /// Two vector faces of different lengths have no separation.
    #[error("a vector face of length {left} and one of length {right} are incomparable")]
    VectorFacesDiffer {
        /// The first length.
        left: usize,
        /// The second length.
        right: usize,
    },
    /// A declared law released outside its own declared tolerance. The claim is boxed because two
    /// exact rationals and a name are the largest payload this refusal carries, and an unboxed
    /// variant would widen every `Result` in the module.
    #[error(
        "the decision law {:?} released a width of {} outside its own declared tolerance of {}",
        .0.law, .0.width, .0.tolerance
    )]
    ReleasedOutsideTolerance(Box<ReleasedClaim>),
    /// A declared law proposed a widening tolerance smaller than the measured width.
    #[error(
        "the decision law {law:?} proposed tolerance {tolerance} below measured width {width}",
        law = .0.law, width = .0.width, tolerance = .0.tolerance
    )]
    WidenTooNarrow(Box<WidenClaim>),
    /// A declared law asked for a probe the library did not compute.
    #[error(
        "the decision law {law:?} asked for the probe {probe:?}, which was not among the computed options"
    )]
    ProbeNotOffered {
        /// The law.
        law: String,
        /// The probe it named.
        probe: String,
    },
    /// A probe's partition and the partition it is compared against are not partitions of one
    /// nonempty fibre into nonempty classes (`receiver::release::ProbePartition`).
    #[error(
        "a probe's partition of {classes} members into nonempty classes does not compare with one \
         of {against} members: both must partition one nonempty fibre"
    )]
    ProbeClasses {
        /// The members the probe's classes hold.
        classes: usize,
        /// The members the compared classes hold.
        against: usize,
    },
    /// A probe whose partition carries no more information than the one it is compared against:
    /// `∏_c |c|^|c|` is not strictly below the comparison's (`receiver::release::ProbePartition`).
    #[error(
        "a probe's partition product {product} is not strictly below its comparison's {against}: \
         it separates the fibre no more than the move it would replace"
    )]
    ProbeNotInformative {
        /// `∏_c |c|^|c|` over the probe's classes, as prose.
        product: String,
        /// The same product over the compared classes, as prose.
        against: String,
    },
    /// A declared width law returned a draw: a width decision carries no key, and a draw is
    /// decided only by `receiver::release::draw` (the separating term between the two acts).
    #[error(
        "the decision law {law:?} returned a draw; a width decision carries no key, so a draw is \
         decided only by the certified draw"
    )]
    DrawNotOffered {
        /// The law.
        law: String,
    },
    /// The exact linear algebra refused.
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
}

impl PartialEq for WidthRefusal {
    fn eq(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }
}

// =============================================================================================
// The relation ladder's scale
// =============================================================================================

/// The rungs as data, so that "which relation was established" is a value and not a word.
///
/// Lean counterpart: `Foundation/RelationLadder.Rung`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Rung {
    /// Rung 1: `x = y`, strict occurrence identity inside one situated type.
    Identity,
    /// Rung 3: a symmetry of the situation carrying one occurrence to the other.
    Isomorphism,
    /// Rung 5: equal potential over the declared `(G, R)`.
    EqualPotential,
    /// Rung 4: equal under every declared receiver, now.
    ReceiverEqual,
    /// Rung 6: a declared reading inside a declared tolerance.
    WithinTolerance,
    /// Rung 2: an addressed passage carries one occurrence to the other.
    Continuation,
    /// Nothing on this ladder was established. The honest bottom, not a claim.
    NoRelation,
}

impl Rung {
    /// Every rung, in the order the Lean `inductive` declares them.
    pub const ALL: [Rung; 7] = [
        Rung::Identity,
        Rung::Isomorphism,
        Rung::EqualPotential,
        Rung::ReceiverEqual,
        Rung::WithinTolerance,
        Rung::Continuation,
        Rung::NoRelation,
    ];

    /// Everything this rung entails, itself included.
    ///
    /// Lean counterpart: `Foundation/RelationLadder.Rung.entailed`.
    pub fn entailed(self) -> &'static [Rung] {
        match self {
            Rung::Identity => &[
                Rung::Identity,
                Rung::Isomorphism,
                Rung::EqualPotential,
                Rung::ReceiverEqual,
                Rung::WithinTolerance,
                Rung::Continuation,
                Rung::NoRelation,
            ],
            Rung::Isomorphism => &[
                Rung::Isomorphism,
                Rung::EqualPotential,
                Rung::ReceiverEqual,
                Rung::WithinTolerance,
                Rung::Continuation,
                Rung::NoRelation,
            ],
            Rung::EqualPotential => &[
                Rung::EqualPotential,
                Rung::ReceiverEqual,
                Rung::WithinTolerance,
                Rung::NoRelation,
            ],
            Rung::ReceiverEqual => &[Rung::ReceiverEqual, Rung::WithinTolerance, Rung::NoRelation],
            Rung::WithinTolerance => &[Rung::WithinTolerance, Rung::NoRelation],
            Rung::Continuation => &[Rung::Continuation, Rung::NoRelation],
            Rung::NoRelation => &[Rung::NoRelation],
        }
    }

    /// Whether every pair standing in this relation also stands in `other`.
    ///
    /// Lean counterpart: `Foundation/RelationLadder.Rung.entails`.
    pub fn entails(self, other: Rung) -> bool {
        self.entailed().contains(&other)
    }
}

/// The greatest common lower bound of two rungs. Total: incomparable rungs meet at
/// [`Rung::NoRelation`].
///
/// Lean counterpart: `Foundation/RelationLadder.rungMeet`.
pub fn rung_meet(left: Rung, right: Rung) -> Rung {
    if left.entails(right) {
        right
    } else if right.entails(left) {
        left
    } else {
        Rung::NoRelation
    }
}

// =============================================================================================
// The face read at a grain
// =============================================================================================

/// [definition] **One exponent read at a grain**: `value = carry + phase/grain + fibre`, with
/// `phase ∈ ℤ/grain` and `fibre ∈ [0, 1/grain)` (Lean `HNN/Ratio.{grainRead, grainFibre,
/// face_constant_on_fibre}`): the reading at a declared grain, the carry, the phase class and the
/// unresolved fibre, which is returned and never rounded. A receiver's face depends only on the
/// cells of its exponents.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GrainCell {
    pub carry: BigInt,
    pub phase: u64,
    pub fibre: Rat,
}

impl GrainCell {
    /// Read `value` at `grain ≥ 1`, exactly: nothing is rounded, the remainder is the fibre.
    ///
    /// [definition; agent-inferred] Two integer divisions with remainder of `value = p/q`
    /// (`q > 0`): `p = n q + r` with `0 ≤ r < q`, then `L r = k q + s` with `0 ≤ s < q`, so the
    /// carry is `n`, the phase class `k` and the fibre `s/(L q)`, normalized once. These are the
    /// floor readings `n = ⌊value⌋`, `k = ⌊L(value − n)⌋`, `ε = (L(value − n) − k)/L` exactly.
    pub fn of(value: &Rat, grain: u64) -> Self {
        let (numerator, denominator) = (value.numer(), value.denom());
        // A reduced ratio carries a positive denominator, so the truncated remainder is
        // corrected once for a negative numerator.
        let (mut carry, mut remainder) = (numerator / denominator, numerator % denominator);
        if remainder.is_negative() {
            carry -= 1;
            remainder += denominator;
        }
        let scaled = remainder * BigInt::from(grain);
        let (phase, residue) = (&scaled / denominator, &scaled % denominator);
        let fibre = Rat::new(residue, denominator * BigInt::from(grain));
        Self {
            carry,
            phase: phase.to_u64().expect("a phase class lies in ℤ/grain"),
            fibre,
        }
    }

    /// The cell's representative `carry + phase/grain`: the point every value of the cell reads as.
    pub fn representative(&self, grain: u64) -> Rat {
        Rat::from_integer(self.carry.clone())
            + Rat::new(BigInt::from(self.phase), BigInt::from(grain))
    }
}

/// A ratio the grain read refuses.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum GrainRefusal {
    #[error("a ratio read at the grain must be positive: a zero part has no finite exponent")]
    NotPositive,
    #[error("the grain {grain} passes 32 bits")]
    WideGrain { grain: u64 },
}

/// [definition] **The grain exponent of a positive ratio `a/b` at grain `L`** (Lean
/// `HNN/RegionCounts.{grainExponent_spec, grain_log_iff_pow_bounds}`): the unique integer `k` with
/// `2^k ≤ (a/b)^L < 2^(k+1)`, decided by the natural-number comparisons
/// `2^(k⁺) b^L ≤ 2^(k⁻) a^L` and `2^((k+1)⁻) a^L < 2^((k+1)⁺) b^L` (`k⁺ = max(k, 0)`,
/// `k⁻ = max(−k, 0)`). The bit lengths of `a^L` and `b^L` place `k` within one of its value, and one
/// comparison decides it. It is the face `log₂(a/b)` read at the grain: `k/L ≤ log₂(a/b) < (k+1)/L`.
/// Refused at a zero numerator or denominator (no finite exponent).
pub fn grain_exponent(
    numerator: &BigUint,
    denominator: &BigUint,
    grain: u64,
) -> Result<BigInt, GrainRefusal> {
    if numerator.is_zero() || denominator.is_zero() {
        return Err(GrainRefusal::NotPositive);
    }
    let power = u32::try_from(grain).map_err(|_| GrainRefusal::WideGrain { grain })?;
    let (a, b) = (numerator.pow(power), denominator.pow(power));
    // `2^(bits(a) − 1) ≤ a < 2^bits(a)`, likewise `b`: `a/b ∈ (2^(d−1), 2^(d+1))`, `d = bits(a) − bits(b)`.
    let d = BigInt::from(a.bits()) - BigInt::from(b.bits());
    let k = if at_least(&a, &b, &d) { d } else { d - 1 };
    debug_assert!(at_least(&a, &b, &k) && !at_least(&a, &b, &(&k + 1)));
    Ok(k)
}

/// `2^k ≤ a/b`, as `2^(k⁺) b ≤ 2^(k⁻) a`.
fn at_least(a: &BigUint, b: &BigUint, k: &BigInt) -> bool {
    let shift = k
        .magnitude()
        .to_usize()
        .expect("a grain exponent within the machine word");
    if k.is_negative() {
        b <= &(a << shift)
    } else {
        &(b << shift) <= a
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::holon::law::EnergyBalance;
    use crate::ratio::algebraic::log2_enclosure;
    use crate::ratio::integer;
    use crate::ratio::linear::vector::{form_matrix, integer_matrix, ints};
    use crate::ratio::rat;
    use num_traits::One;

    /// `Holon/Law.passive_reading`: the linear reading and the coholon read the same value,
    /// and the coholon draws zero power.
    #[test]
    fn a_linear_reading_is_the_passive_coholon() {
        let reading = LinearReading {
            receiver: "sum and first".to_owned(),
            matrix: integer_matrix(&[&[1, 1, 1], &[1, 0, 0]]).unwrap(),
        };
        let coholon = reading.passive_coholon();
        let effort = vec![rat(1, 2), integer(-3), rat(7, 5)];
        let passive = coholon.read(&effort).unwrap();
        assert_eq!(
            Reading::read(&reading, &effort).unwrap(),
            ExactFace::Vector(passive.value.clone())
        );
        assert_eq!(
            Reading::read(&coholon, &effort).unwrap(),
            ExactFace::Vector(passive.value)
        );
        assert!(passive.power.is_zero());
        assert_eq!(coholon.dirac().unwrap().ports(), 3);
        assert!(coholon.read(&ints(&[1, 2])).is_err());
    }

    /// `Holon/Law.coholon_reading_power`: a nonlinear reading of the coholon bond draws no
    /// power either.
    #[test]
    fn a_nonlinear_reading_stands_on_a_zero_power_bond() {
        let effort = ints(&[3, -1, 4]);
        let bond = coholon_bond(&effort).unwrap();
        let largest = bond.effort().iter().max().unwrap().clone();
        assert_eq!(largest, integer(4));
        assert!(bond.power().is_zero());
        let reading = ActiveReceiver::declared("argmax", 3, ReceiverPower::Reading);
        let exchange = reading.reading_balance(&effort).unwrap();
        assert!(exchange.own.is_exact() && exchange.delivered.is_zero());
    }

    /// `Holon/Law.exterior_drive_balance`: the drive's own balance closes, and joining the
    /// delivered power closes the Holon's balance that did not count it.
    #[test]
    fn an_exterior_drive_closes_its_balance_and_the_joined_one() {
        let drive = ActiveReceiver::declared(
            "participation",
            2,
            ReceiverPower::ExteriorDrive { drive_ports: 2 },
        );
        assert!(!drive.is_passive());
        let exchange = drive
            .drive_balance(&ints(&[1, 2]), &[rat(1, 3), rat(2, 3)], &ints(&[3, -6]))
            .unwrap();
        assert_eq!(exchange.delivered, integer(-3));
        assert!(exchange.own.is_exact());
        // A Holon whose stored change is the delivered power, before counting the receiver.
        let open = EnergyBalance::closed(
            integer(-3),
            integer(0),
            integer(0),
            integer(0),
            integer(0),
            integer(0),
        );
        assert!(!open.is_exact());
        assert!(open.joined_active(&exchange.delivered).is_exact());
        assert!(drive.reading_balance(&ints(&[1, 2])).is_err());
    }

    /// `Holon/Law.learned_receiver_balance`.
    #[test]
    fn a_learned_receiver_delivers_its_declared_power() {
        let relation =
            ActiveRelation::new(integer_matrix(&[&[-1, 2], &[-2, -1]]).unwrap()).unwrap();
        let learned = ActiveReceiver::declared("learned", 2, ReceiverPower::Learned(relation));
        assert!(learned.is_passive());
        let exchange = learned.learned_balance(&ints(&[1, 1])).unwrap();
        assert_eq!(exchange.delivered, integer(-2));
        assert!(exchange.own.is_exact());
    }

    /// `Holon/Law.softmaxJacobian_transpose` and `pullback_law`: `J_p` is symmetric, rows
    /// sum to zero on the simplex, and the pullback preserves the pairing.
    #[test]
    fn the_normalized_pullback_preserves_power() {
        let p = vec![rat(1, 2), rat(1, 3), rat(1, 6)];
        let j = softmax_jacobian(&p).unwrap();
        let jm = form_matrix(&j);
        assert!(
            jm.apply(&ints(&[1, 1, 1]))
                .unwrap()
                .iter()
                .all(Zero::is_zero)
        );
        assert_eq!(jm.transpose().unwrap(), jm);
        let pullback = ActiveReceiver::declared("normalized", 3, ReceiverPower::Pullback);
        let (returned, forward) = pullback
            .pullback_balance(
                &jm,
                &[rat(1, 2), integer(-1), integer(2)],
                &ints(&[3, 1, -2]),
            )
            .unwrap();
        assert_eq!(returned, forward);
        // A non-symmetric producing Jacobian returns through its transpose with the same law.
        let p = integer_matrix(&[&[1, 2, 0], &[0, -1, 3]]).unwrap();
        let (returned, forward) = pullback
            .pullback_balance(&p, &ints(&[2, -1]), &ints(&[1, 1, 1]))
            .unwrap();
        assert_eq!(returned, forward);
    }

    /// Guard 15, and Lean `HNN/Ratio.face_constant_on_fibre`: an exponent read at a grain is its carry,
    /// its phase class and its fibre, exactly, with `0 ≤ ε < 1/L`; reading it down to its cell's
    /// representative moves it by less than `1/L`, and every value of a cell has one representative.
    #[test]
    fn the_grain_reading_is_a_carry_a_phase_class_and_a_fibre() {
        let values = [
            rat(-37, 7),
            rat(5, 3),
            integer(-2),
            rat(1, 16),
            rat(-1, 1000),
            Rat::zero(),
        ];
        for value in &values {
            for grain in [1u64, 2, 16, 7] {
                let cell = GrainCell::of(value, grain);
                let grain_rat = Rat::from_integer(BigInt::from(grain));
                assert!(cell.phase < grain);
                assert!(cell.fibre >= Rat::zero() && cell.fibre < grain_rat.recip());
                assert_eq!(cell.representative(grain) + &cell.fibre, *value);
                assert!(value - cell.representative(grain) < grain_rat.recip());
                let inside = cell.representative(grain) + &cell.fibre / integer(2);
                assert_eq!(
                    GrainCell::of(&inside, grain).representative(grain),
                    cell.representative(grain)
                );
            }
        }
        let cell = GrainCell::of(&rat(-37, 7), 16);
        assert_eq!(cell.carry, BigInt::from(-6));
        assert_eq!(cell.phase, 11);
    }

    /// `2^k ≤ p^L < 2^(k+1)`, checked over ℚ.
    fn brackets(p: &Rat, grain: u64, k: &BigInt) -> bool {
        let mut read = Rat::one();
        for _ in 0..grain {
            read *= p;
        }
        let two = |k: &BigInt| {
            let magnitude = usize::try_from(k.magnitude().clone()).unwrap();
            let value = Rat::from_integer(BigInt::one() << magnitude);
            if k.sign() == num_bigint::Sign::Minus {
                value.recip()
            } else {
                value
            }
        };
        two(k) <= read && read < two(&(k + 1))
    }

    fn grain_of(p: &Rat, grain: u64) -> BigInt {
        grain_exponent(
            &p.numer().to_biguint().unwrap(),
            &p.denom().to_biguint().unwrap(),
            grain,
        )
        .unwrap()
    }

    /// Lean `HNN/RegionCounts.{grainExponent_spec, grain_log_iff_pow_bounds, grain_face_residual,
    /// grain_fixture}`: the grain exponent is the unique `k` with `2^k ≤ (a/b)^L < 2^(k+1)`, from integer
    /// comparisons, and `k/L ≤ log₂(a/b) < (k+1)/L`; at `L = 1` it is `⌊log₂(a/b)⌋`; an exact power of
    /// two reads its own exponent; `5/8 → −11`, `3/8 → −23` at `L = 16`; a zero is refused.
    #[test]
    fn the_grain_exponent_is_the_integer_comparison() {
        for p in [
            rat(5, 8),
            rat(3, 8),
            rat(1, 1),
            rat(1, 256),
            rat(3, 7),
            rat(255, 256),
            rat(1, 3),
            rat(9, 2),
            rat(1023, 1025),
        ] {
            for grain in [1u64, 2, 7, 16] {
                let k = grain_of(&p, grain);
                assert!(brackets(&p, grain, &k), "{p} at {grain}");
                let log = log2_enclosure(&p).unwrap();
                let grain_rat = Rat::from_integer(BigInt::from(grain));
                assert!(Rat::from_integer(k.clone()) / &grain_rat <= log.upper);
                assert!(log.lower < Rat::from_integer(&k + 1) / &grain_rat);
            }
        }
        assert_eq!(grain_of(&rat(1, 256), 16), BigInt::from(-128));
        assert_eq!(grain_of(&rat(9, 2), 1), BigInt::from(2));
        assert_eq!(grain_of(&rat(5, 8), 16), BigInt::from(-11));
        assert_eq!(grain_of(&rat(3, 8), 16), BigInt::from(-23));
        assert!(grain_exponent(&BigUint::zero(), &BigUint::one(), 16).is_err());
    }
}
