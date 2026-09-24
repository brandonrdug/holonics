//! **Receivers as Holons at ports: the passive coholon, the active receiver and the reading face.**
//!
//! [definition] Plan phase 7 ([plan](../../../../docs/plans/THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md),
//! [object](../../../../docs/ELEMENTARY_OBJECTS.md#the-holon-as-one-object)): a receiver is a Holon
//! joined at ports, and there are exactly three things a receiver-named type can be.
//!
//! * **The passive coholon** ([`PassiveCoholon`]): the zero-storage, zero-flow limit that admits
//!   every effort and draws no power (`Holon/Law.lean::passiveCoholon`,
//!   `Holon/Law.lean::passiveCoholon_isDirac`). Its linear reading `C e` is
//!   `Holon/Law.lean::passive_reading`; any reading of its bond, linear or not, draws zero power
//!   (`Holon/Law.lean::coholon_reading_power`). [`LinearReading`] and the engine's
//!   `standing::ReceiverReading` are this object with a declared name.
//! * **An active receiver** ([`ActiveReceiver`]): a receiver that returns something into the Holon
//!   it reads, entering with its actual power term ([`ReceiverPower`]). Joined through an interface
//!   conductance it satisfies `Holon/Law.lean::active_receiver_law` ([`crate::law::active_receiver`]);
//!   a learned linear relation carries `⟨f, L f⟩` ([`crate::element::ActiveRelation`]); a nonlinear
//!   reading that injects a current `y` at drive ports carries the exterior power `⟨e_D, y⟩`, whose
//!   own balance closes exactly (`Holon/Law.lean::exterior_drive_balance`); a covector pullback
//!   through the producing Jacobian's transpose is power preserving (`Holon/Law.lean::pullback_law`,
//!   `Holon/Law.lean::softmaxJacobian_transpose`).
//! * **A receiver face** (a codec projection): the exact value a reading returns ([`ExactFace`]),
//!   the declared norm ([`DiameterNorm`]), the diameter over a fibre ([`ReceiverWidth`],
//!   [`width_over_readings`]), the two-axis [`Horizon`] and the relation ladder's [`Rung`]. A face
//!   is what a coholon's value is charted as; it is not itself a port object.
//!
//! [definition] The face machinery moved here from `crates/holonic-engine/src/receiver_release.rs`
//! (and [`Rung`] from `relation_ladder.rs`), which re-export every item at their existing paths;
//! the wire forms (`holonics.receiver-width.v1`, the kebab-case face and witness tags, the
//! validating `try_from` routes) are unchanged. They moved so that the tube's horizon, defect
//! profile and route plan could join the core restriction facet
//! ([`crate::restriction::tube::horizon`]).
//!
//! | Lean | Rust |
//! |---|---|
//! | `passiveCoholon`, `passiveCoholon_isDirac` | [`PassiveCoholon::dirac`] |
//! | `passive_reading` | [`PassiveCoholon::read`], [`crate::law::HolonLaw::receive`] |
//! | `coholon_reading_power` | [`coholon_bond`], [`PassiveCoholon::read_face`] |
//! | `exterior_drive_balance` | [`ActiveReceiver::drive_balance`] |
//! | `learned_receiver_balance` | [`ActiveReceiver::learned_balance`] |
//! | `softmaxJacobian`, `softmaxJacobian_transpose`, `pullback_law` | [`softmax_jacobian`], [`ActiveReceiver::pullback_balance`] |
//! | `active_receiver_law` | [`crate::law::active_receiver`] |
//! | `Foundation/ReceiverRelease.lean::width`, `width_nonneg`, `abs_sub_le_width` | [`width_over_readings`], [`ReceiverWidth`] |
//! | `Foundation/ReceiverRelease.lean::Horizon`, `Horizon.Within`, `horizonWithin_is_not_total` | [`Horizon`], [`Horizon::contains`], [`Horizon::comparable`] |
//! | `Foundation/RelationLadder.lean::Rung`, `Rung.entailed`, `Rung.entails`, `rungMeet` | [`Rung`], [`rung_meet`] |

use std::fmt::Debug;

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::dirac::DiracStructure;
use crate::element::ActiveRelation;
use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::holon::HolonError;
use crate::inertia::SymmetricForm;
use crate::law::{EnergyBalance, PassiveReading};
use crate::port::Bond;
use crate::scalar::{dot, matrix, zeros};

// =============================================================================================
// The passive coholon
// =============================================================================================

/// [definition] **The coholon bond of a reading**: zero flow and the read effort, checked to lie in
/// the passive coholon's Dirac structure. Whatever function of the effort a receiver then computes —
/// linear or not — the bond it stands on draws zero power (`Holon/Law.lean::coholon_reading_power`).
pub fn coholon_bond(effort: &[Rat]) -> Result<Bond, HolonError> {
    let bond = Bond::new(zeros(effort.len()), effort.to_vec())?;
    if !DiracStructure::passive_coholon(effort.len())?.contains(&bond)? {
        return Err(HolonError::NotAdmitted);
    }
    Ok(bond)
}

/// [definition] **The passive coholon with a declared linear reader** `C`: joined at a Holon's
/// ports it forces zero flow there, admits every effort, reads `C e` and draws zero power
/// (`Holon/Law.lean::passive_reading`).
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
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
    /// (`Holon/Law.lean::passiveCoholon_isDirac`).
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
    /// (`Holon/Law.lean::coholon_reading_power`).
    Reading,
    /// A learned linear relation `e_A = L f_A` with its declared power `⟨f_A, L f_A⟩`.
    Learned(ActiveRelation),
    /// A nonlinear reading of its read ports that injects the current `y` at `drive_ports` ports of
    /// the Holon. It stores nothing; the power it delivers, `⟨e_D, y⟩` at the Holon's drive effort
    /// `e_D`, is supplied from its exterior and evaluated by the consumer that owns `e_D`
    /// (`Holon/Law.lean::exterior_drive_balance`).
    ExteriorDrive { drive_ports: usize },
    /// A covector returned through the transpose of the producing Jacobian `P` (an adjoint or
    /// pullback return): efforts move by `Pᵀ` and the pairing is preserved,
    /// `⟨g, P δ⟩ = ⟨Pᵀ g, δ⟩` (`Holon/Law.lean::pullback_law`). It stores and delivers nothing.
    /// The normalized face's `J_p = diag p − p pᵀ` is self-adjoint
    /// (`Holon/Law.lean::softmaxJacobian_transpose`), so its return is `J_p g` itself.
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

    /// **An exterior drive's exchange** (`Holon/Law.lean::exterior_drive_balance`): the receiver
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

    /// **A learned relation's exchange** (`Holon/Law.lean::learned_receiver_balance`): at flow
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

    /// **A pullback's exchange** (`Holon/Law.lean::pullback_law`): the returned covector `Pᵀ g`
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
/// (`Holon/Law.lean::softmaxJacobian`); it is symmetric (`softmaxJacobian_transpose`), so the
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
    Ok(crate::scalar::matrix_form(&m)?)
}

// =============================================================================================
// The receiver face (moved from `holonic-engine::receiver_release`)
// =============================================================================================

/// Serialized schema name for a returned width.
pub const RECEIVER_WIDTH_SCHEMA: &str = "holonics.receiver-width.v1";

/// The ceiling on a declared horizon.
///
/// [definition] `horizon_image` runs one exact matrix multiplication per step, so the *step count*
/// is itself work sized by a caller declaration. Bounding the generator product is not enough: an
/// admitted-input box with no width contributes no generator at all, so a hostile horizon would
/// pass the generator ceiling and still loop. This ceiling is checked first.
pub const HORIZON_CEILING: usize = 4096;

/// The ceiling on the number of members an enumerated compatible family may declare.
///
/// [definition] A width over an enumerated family reads every unordered pair, so the work is
/// `n(n−1)/2`. The ceiling bounds `n`, and the pair count is formed with checked arithmetic.
pub const FAMILY_CEILING: usize = 4096;

/// An exact face returned by a receiver reading. Three arms, each exact; no float appears.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "face", rename_all = "kebab-case")]
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
/// [established-bounded] `SquaredEuclidean` is exact on an **enumerated** family and is refused on
/// an enclosure: the Euclidean diameter of a zonotope is attained at a vertex of the generator
/// cube, so an exact computation would enumerate `2^k` sign patterns. The refusal is
/// [`WidthRefusal::NormNotExactOnEnclosure`] and names the norm.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
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

/// A declared exact reading of one compatible state. Implementors are the receivers of the plan;
/// the reading is `R ∘ Φ_h` already composed, exactly as the Lean owner says.
///
/// [definition] **A reading is the passive coholon's** (plan phase 7): it reads the state at zero
/// flow, so whatever the function — linear ([`LinearReading`], [`PassiveCoholon`]) or not — the bond
/// it stands on is [`coholon_bond`] and the power it draws is zero
/// (`Holon/Law.lean::coholon_reading_power`). A reading that returns a current into the Holon is
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
/// Lean counterpart: `Foundation/ReceiverRelease.lean::width`.
///
/// [implemented-exact] Every field is private. The only constructors are `receiver_release::width_enumerated` and
/// `receiver_release::width_enclosed`, and the only wire route is the validating [`TryFrom`] below, reached
/// through `#[serde(try_from = ...)]`: a remounted reading whose schema, diameter sign or
/// attaining witness is incoherent with its own `read` count is refused rather than carried, so
/// a forged width cannot be handed to `receiver_release::LawfulOptions::assemble`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ReceiverWidthWire")]
pub struct ReceiverWidth {
    schema: String,
    receiver: String,
    lineage: String,
    norm: DiameterNorm,
    diameter: Rat,
    attaining: WidthWitness,
    read: usize,
}

/// The wire form of a [`ReceiverWidth`]. Deserializing a `ReceiverWidth` goes through this and
/// the structural re-check in `TryFrom`; there is no unchecked route.
#[derive(Clone, Debug, Deserialize)]
struct ReceiverWidthWire {
    schema: String,
    receiver: String,
    lineage: String,
    norm: DiameterNorm,
    diameter: Rat,
    attaining: WidthWitness,
    read: usize,
}

impl TryFrom<ReceiverWidthWire> for ReceiverWidth {
    type Error = WidthRefusal;

    fn try_from(wire: ReceiverWidthWire) -> Result<Self, Self::Error> {
        if wire.schema != RECEIVER_WIDTH_SCHEMA {
            return Err(WidthRefusal::WidthSchemaMismatch {
                declared: wire.schema,
                expected: RECEIVER_WIDTH_SCHEMA,
            });
        }
        if wire.diameter.is_negative() {
            return Err(WidthRefusal::NegativeWidth {
                declared: wire.diameter.to_string(),
            });
        }
        match &wire.attaining {
            WidthWitness::Pair { left, right } => {
                if left >= right || *right >= wire.read {
                    return Err(WidthRefusal::WitnessOutsideReading {
                        read: wire.read,
                        witness: format!("{:?}", wire.attaining),
                    });
                }
            }
            WidthWitness::Coordinate { .. } => {}
            WidthWitness::Point => {
                if !wire.diameter.is_zero() {
                    return Err(WidthRefusal::WitnessOutsideReading {
                        read: wire.read,
                        witness: "point witness with a nonzero diameter".to_owned(),
                    });
                }
            }
        }
        Ok(Self {
            schema: wire.schema,
            receiver: wire.receiver,
            lineage: wire.lineage,
            norm: wire.norm,
            diameter: wire.diameter,
            attaining: wire.attaining,
            read: wire.read,
        })
    }
}

impl ReceiverWidth {
    /// **A width declared by an owner that computed it** (the engine's enclosure width, whose
    /// zonotope stays in the engine). It passes the same structural checks as the wire route, so
    /// this constructor admits nothing a remount would refuse.
    pub fn declared(
        receiver: impl Into<String>,
        lineage: impl Into<String>,
        norm: DiameterNorm,
        diameter: Rat,
        attaining: WidthWitness,
        read: usize,
    ) -> Result<Self, WidthRefusal> {
        Self::try_from(ReceiverWidthWire {
            schema: RECEIVER_WIDTH_SCHEMA.to_owned(),
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
    /// The serialized schema.
    pub fn schema(&self) -> &str {
        &self.schema
    }

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
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "witness", rename_all = "kebab-case")]
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
pub const INDEX_HORIZON_CEILING: usize = 1024;

/// **A horizon with two coordinates: `h` longitudinal steps and `k` steps in the tower's index.**
///
/// [definition] `w_R(h)` — the width this module already owned — measures distance into the
/// horizon along one axis only. The second coordinate is distance in the **index**, in either
/// direction: `k` steps toward the finer charts or `k` steps toward the coarser ones. Brandon's
/// statement, September 18: *zooming from orbit down to an organism is as far into the horizon as
/// looking out to the stars*, and that is the same notion of distance in both directions.
///
/// [proved-derived; formal-checked] Lean counterpart:
/// `Foundation/ReceiverRelease.lean::Horizon`, with `Horizon.Within` the product order,
/// `horizonWithin_refl`/`horizonWithin_trans` its two laws and `horizonWithin_is_not_total` the
/// statement that **the two coordinates are not one scale**: `(2, 0)` and `(0, 2)` are
/// incomparable horizons, so "how far into the horizon" is a pair and not a number, and no
/// lexicographic order is imposed on it here. That is why this type derives no `Ord`.
///
/// [implemented-exact] Both fields are private and the only constructors are [`Self::declare`] and
/// [`Self::longitudinal_only`], which check both ceilings. The `Deserialize` route goes through
/// `#[serde(try_from = ...)]` and re-runs those checks, so a remounted horizon cannot carry a
/// declaration the library would have refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(try_from = "HorizonWire")]
pub struct Horizon {
    longitudinal: usize,
    index: usize,
}

/// The wire form of a [`Horizon`]. Deserializing one goes through this and the ceiling checks in
/// `TryFrom`; there is no unchecked route.
#[derive(Clone, Copy, Debug, Deserialize)]
struct HorizonWire {
    longitudinal: usize,
    index: usize,
}

impl TryFrom<HorizonWire> for Horizon {
    type Error = WidthRefusal;

    fn try_from(wire: HorizonWire) -> Result<Self, Self::Error> {
        Self::declare(wire.longitudinal, wire.index)
    }
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
/// [definition] This is `receiver_release::width_enumerated`'s second half on its own: the diameter of a set of
/// exact faces in a declared norm, with the pair that attains it. It exists because a width is
/// taken over readings that did not come from a `Vec<Rat>` compatible family — the faces of a
/// tube's two-axis horizon are the first consumer — and the diameter law must not be written a
/// second time for them.
///
/// Lean counterpart: `Foundation/ReceiverRelease.lean::width`, with `abs_sub_le_width` the pair
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
        schema: RECEIVER_WIDTH_SCHEMA.to_owned(),
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

/// A coarser release offered against a tolerance other than the one it was searched under.
/// Carried behind a box inside [`WidthRefusal::CoarserSearchedAtAnotherTolerance`], so the
/// refusal stays small.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoarserToleranceClaim {
    /// The coarser receiver named by the release.
    pub receiver: String,
    /// The tolerance `receiver_release::release_coarser` searched under.
    pub searched: Rat,
    /// The tolerance the options declare.
    pub declared: Rat,
}

/// The coarser release a declared law claimed, with the tolerance the options were assembled
/// against. Carried behind a box inside [`WidthRefusal::CoarserReleasedOutsideTolerance`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoarserClaim {
    /// The law that claimed it.
    pub law: String,
    /// The coarser receiver it claimed to release.
    pub receiver: String,
    /// The exact width it released.
    pub width: Rat,
    /// The exact tolerance the options declared.
    pub tolerance: Rat,
}

/// Why a width or a release was refused. Every failure is returned as content.
#[derive(Debug, Error)]
pub enum WidthRefusal {
    /// A coarser release searched under one tolerance was assembled against another.
    #[error(
        "the coarser receiver {} was searched inside tolerance {} and cannot be offered against \
         the declared tolerance {}",
        .0.receiver, .0.searched, .0.declared
    )]
    CoarserSearchedAtAnotherTolerance(Box<CoarserToleranceClaim>),
    /// A remounted width declares a schema this module does not own.
    #[error("a receiver width declaring schema {declared} is not a {expected}")]
    WidthSchemaMismatch {
        /// What the wire declared.
        declared: String,
        /// What this module owns.
        expected: &'static str,
    },
    /// A remounted width declares a negative diameter. A diameter is a maximum of absolute
    /// separations and is never negative (`width_nonneg`).
    #[error(
        "a receiver width of {declared} is negative; a diameter is a maximum of absolute separations"
    )]
    NegativeWidth {
        /// The declared diameter, as prose.
        declared: String,
    },
    /// A remounted width's attaining witness does not index the reading it claims.
    #[error("an attaining witness {witness} does not index a reading of {read} members")]
    WitnessOutsideReading {
        /// How many members the width claims to have read.
        read: usize,
        /// The witness, as prose.
        witness: String,
    },
    /// A declared law released a coarser receiver outside the declared tolerance.
    #[error(
        "the law {} released the coarser receiver {} at width {} outside the declared tolerance {}",
        .0.law, .0.receiver, .0.width, .0.tolerance
    )]
    CoarserReleasedOutsideTolerance(Box<CoarserClaim>),
    /// A compatible family with no member has no diameter.
    #[error("a compatible family with no member has no width")]
    EmptyFamily,
    /// A zero-dimensional carrier has no reading.
    #[error("a zero-dimensional carrier carries no receiver reading")]
    EmptyDimension,
    /// Two declared extents do not agree.
    #[error("a carrier of dimension {declared} does not pair with one of dimension {found}")]
    DimensionMismatch {
        /// What was declared.
        declared: usize,
        /// What was found.
        found: usize,
    },
    /// A declared enclosure asks for more generators than the ceiling admits.
    #[error(
        "an enclosure of {requested} uncertainty generators exceeds the declared ceiling {ceiling}; \
         nothing was allocated"
    )]
    GeneratorCeiling {
        /// How many were asked for.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The generator count of an `h`-step image does not fit a machine integer.
    #[error(
        "{states} state generators and {inputs} input generators over horizon {horizon} overflow \
         the machine integer counting them; nothing was allocated"
    )]
    GeneratorCountOverflows {
        /// State generators.
        states: usize,
        /// Input generators.
        inputs: usize,
        /// The declared horizon.
        horizon: usize,
    },
    /// A declared carrier extent is wider than the ceiling admits.
    #[error(
        "a carrier of extent {requested} exceeds the declared ceiling {ceiling}; nothing was \
         allocated and no product was formed"
    )]
    ExtentCeiling {
        /// The declared extent.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The exact multiplications a declared horizon and extent ask for exceed the work ceiling.
    #[error(
        "a horizon of {horizon} steps at extent {extent} asks for more than the declared ceiling \
         of {ceiling} exact products; no step was taken"
    )]
    MultiplyWorkCeiling {
        /// The declared extent.
        extent: usize,
        /// The declared horizon.
        horizon: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// A declared coarsening tower carries more steps than the ceiling admits.
    #[error(
        "a coarsening tower of {requested} steps exceeds the declared ceiling {ceiling}; no step \
         was checked"
    )]
    TowerStepCeiling {
        /// The declared step count.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// More candidate observations were declared than the ceiling admits.
    #[error(
        "a probe over {requested} candidate observations exceeds the declared ceiling {ceiling}; \
         no candidate was read"
    )]
    CandidateCeiling {
        /// The declared candidate count.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
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
    /// A generator index outside the enclosure.
    #[error("generator {index} lies outside an enclosure carrying {carried}")]
    GeneratorAbsent {
        /// The index asked for.
        index: usize,
        /// How many the enclosure carries.
        carried: usize,
    },
    /// A declared half-width was negative.
    #[error("coordinate {coordinate} was declared a negative half-width, which is not an extent")]
    NegativeHalfWidth {
        /// Which coordinate.
        coordinate: usize,
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
    /// A declared reading was asked for a width over an enclosure it cannot read.
    #[error(
        "the declared reading {receiver:?} is not linear, so its width needs an enumerated \
         compatible family; an enclosure is refused rather than sampled"
    )]
    DeclaredReadingNeedsEnumeratedFamily {
        /// The receiver that refused.
        receiver: String,
    },
    /// An enclosure reading was asked for a width over an enumerated family.
    #[error("the enclosure reading {receiver:?} was given an enumerated family instead of a hull")]
    EnclosedReadingNeedsEnclosure {
        /// The receiver that refused.
        receiver: String,
    },
    /// A norm that is not exact on an enclosure.
    #[error(
        "the {norm} diameter of a zonotope is attained at a vertex of its generator cube, so it is \
         not computed exactly on an enclosure; declare the supremum norm or enumerate the family"
    )]
    NormNotExactOnEnclosure {
        /// The norm that was declared.
        norm: &'static str,
    },
    /// A declared law released outside its own declared tolerance. The claim is boxed because two
    /// exact rationals and a name are the largest payload this refusal carries, and an unboxed
    /// variant would widen every `Result` in the module.
    #[error(
        "the decision law {:?} released a width of {} outside its own declared tolerance of {}",
        .0.law, .0.width, .0.tolerance
    )]
    ReleasedOutsideTolerance(Box<ReleasedClaim>),
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
    /// A declared law released a coarser receiver the tower did not return.
    #[error(
        "the decision law {law:?} released the coarser receiver {receiver:?}, which the declared \
         tower did not return inside tolerance"
    )]
    CoarserNotOffered {
        /// The law.
        law: String,
        /// The receiver it named.
        receiver: String,
    },
    /// A declared coarsening step does not factor through the step before it.
    #[error(
        "the receiver {coarse:?} does not factor through {fine:?}: members {left} and {right} of \
         the fibre are identified by the finer reading and separated by the coarser one, so the \
         declared tower is not a coarsening"
    )]
    CoarserDoesNotFactor {
        /// The coarser receiver.
        coarse: String,
        /// The finer one.
        fine: String,
        /// The first member.
        left: usize,
        /// The second.
        right: usize,
    },
    /// A factor map was composed with a reading whose face it cannot act on.
    #[error("the factor map {factor:?} acts on a vector face and was given a {arm} face")]
    FactorNeedsVectorFace {
        /// The factor map.
        factor: String,
        /// The arm it was given.
        arm: &'static str,
    },
    /// A declared factor map increases a separation on the fibre actually read.
    #[error(
        "the factor map {factor:?} is expansive on this fibre: at coordinate {coordinate} it \
         separates members {left} and {right} further than the finer reading does, so the coarser \
         receiver is not narrower"
    )]
    FactorIsExpansive {
        /// The factor map.
        factor: String,
        /// The first member.
        left: usize,
        /// The second.
        right: usize,
        /// The coordinate that refutes it.
        coordinate: usize,
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
// The relation ladder's scale (moved from `holonic-engine::relation_ladder`)
// =============================================================================================

/// The rungs as data, so that "which relation was established" is a value and not a word.
///
/// Lean counterpart: `Foundation/RelationLadder.lean::Rung`.
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
    /// Lean counterpart: `Foundation/RelationLadder.lean::Rung.entailed`.
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
    /// Lean counterpart: `Foundation/RelationLadder.lean::Rung.entails`.
    pub fn entails(self, other: Rung) -> bool {
        self.entailed().contains(&other)
    }
}

/// The greatest common lower bound of two rungs. Total: incomparable rungs meet at
/// [`Rung::NoRelation`].
///
/// Lean counterpart: `Foundation/RelationLadder.lean::rungMeet`.
pub fn rung_meet(left: Rung, right: Rung) -> Rung {
    if left.entails(right) {
        right
    } else if right.entails(left) {
        left
    } else {
        Rung::NoRelation
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::law::EnergyBalance;
    use crate::scalar::{form_matrix, int, integer_matrix, ints, rat};

    /// `Holon/Law.lean::passive_reading`: the linear reading and the coholon read the same value,
    /// and the coholon draws zero power.
    #[test]
    fn a_linear_reading_is_the_passive_coholon() {
        let reading = LinearReading {
            receiver: "sum and first".to_owned(),
            matrix: integer_matrix(&[&[1, 1, 1], &[1, 0, 0]]).unwrap(),
        };
        let coholon = reading.passive_coholon();
        let effort = vec![rat(1, 2), int(-3), rat(7, 5)];
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

    /// `Holon/Law.lean::coholon_reading_power`: a nonlinear reading of the coholon bond draws no
    /// power either.
    #[test]
    fn a_nonlinear_reading_stands_on_a_zero_power_bond() {
        let effort = ints(&[3, -1, 4]);
        let bond = coholon_bond(&effort).unwrap();
        let largest = bond.effort().iter().max().unwrap().clone();
        assert_eq!(largest, int(4));
        assert!(bond.power().is_zero());
        let reading = ActiveReceiver::declared("argmax", 3, ReceiverPower::Reading);
        let exchange = reading.reading_balance(&effort).unwrap();
        assert!(exchange.own.is_exact() && exchange.delivered.is_zero());
    }

    /// `Holon/Law.lean::exterior_drive_balance`: the drive's own balance closes, and joining the
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
        assert_eq!(exchange.delivered, int(-3));
        assert!(exchange.own.is_exact());
        // A Holon whose stored change is the delivered power, before counting the receiver.
        let open = EnergyBalance::closed(int(-3), int(0), int(0), int(0), int(0), int(0));
        assert!(!open.is_exact());
        assert!(open.joined_active(&exchange.delivered).is_exact());
        assert!(drive.reading_balance(&ints(&[1, 2])).is_err());
    }

    /// `Holon/Law.lean::learned_receiver_balance`.
    #[test]
    fn a_learned_receiver_delivers_its_declared_power() {
        let relation =
            ActiveRelation::new(integer_matrix(&[&[-1, 2], &[-2, -1]]).unwrap()).unwrap();
        let learned = ActiveReceiver::declared("learned", 2, ReceiverPower::Learned(relation));
        assert!(learned.is_passive());
        let exchange = learned.learned_balance(&ints(&[1, 1])).unwrap();
        assert_eq!(exchange.delivered, int(-2));
        assert!(exchange.own.is_exact());
    }

    /// `Holon/Law.lean::softmaxJacobian_transpose` and `pullback_law`: `J_p` is symmetric, rows
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
            .pullback_balance(&jm, &[rat(1, 2), int(-1), int(2)], &ints(&[3, 1, -2]))
            .unwrap();
        assert_eq!(returned, forward);
        // A non-symmetric producing Jacobian returns through its transpose with the same law.
        let p = integer_matrix(&[&[1, 2, 0], &[0, -1, 3]]).unwrap();
        let (returned, forward) = pullback
            .pullback_balance(&p, &ints(&[2, -1]), &ints(&[1, 1, 1]))
            .unwrap();
        assert_eq!(returned, forward);
    }

    /// The declared width passes the wire's checks.
    #[test]
    fn a_declared_width_is_checked_like_the_wire() {
        assert!(
            ReceiverWidth::declared(
                "r",
                "l",
                DiameterNorm::Supremum,
                int(2),
                WidthWitness::Pair { left: 0, right: 1 },
                2
            )
            .is_ok()
        );
        assert!(
            ReceiverWidth::declared(
                "r",
                "l",
                DiameterNorm::Supremum,
                int(2),
                WidthWitness::Point,
                1
            )
            .is_err()
        );
        let width = width_over_readings(
            "r",
            "l",
            &[
                ExactFace::Vector(ints(&[0, 1])),
                ExactFace::Vector(ints(&[3, 1])),
            ],
            DiameterNorm::Supremum,
        )
        .unwrap();
        assert_eq!(width.diameter(), &int(3));
    }
}
