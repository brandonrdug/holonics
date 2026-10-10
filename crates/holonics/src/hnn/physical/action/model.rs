//! **The World's learned model: a native port Holon read through its own charts** (the receiving-phase
//! [record](../../../../../../research/records/2026-10-08_THE_RECEIVING_PHASE_COMPARISON_RETAINS_AN_EXACT_FAMILY_AND_ITS_PROBE_IS_A_DECLARED_LEVERAGE.md)
//! §7, C1b; #73).
//!
//! [definition; agent-inferred, October 9; Epime's review] The model is a declared family of native
//! port Holon laws of the HNN's own kind ([`ModelKey`]): midpoint Dirac laws with their wave
//! admittances. It never reads the actual World's coefficients: `world.rs` keeps them private, and
//! the family is a declaration whose truth membership is never claimed. Each key's charts,
//!
//! ```text
//! ξ⁺ = F ξ + G a,   b = P ξ + Q a        at the actual World's indexing: the source/storage cut of one step
//! ```
//!
//! are read on unit columns of the same Dirac commit and Robin termination the actual World solves
//! (`ReferenceHolon::prepare_commit`, then the coupled `(z, e)` system of `world.rs`'s
//! `interact_wave` with its flow constant, through `ExactRatMatrix::preimage_fibre`); no second
//! stepping or elimination rule enters. Unit columns are the charts by the owner's identity:
//! `prepare_commit`'s operator (`system`, `flow_coefficient`, `external_target`) does not depend on the
//! state, and its target and flow constant are linear in the state at zero input. The equal operator at
//! every unit state and the zero return of the zero state are guards on that identity, not its proof.
//!
//! **Admission.** A key is compared with raw `(a, b)` only on the source's own wave frame and clock:
//! at binding (`Resident::bind_world_model`) every key's external ports are the bound source ring's
//! realified width (the wave the World admits), each at that ring's admittance, at the field's step,
//! all read from the source's declarations and none from the World's material. A key off that frame
//! is refused there, as a declaration; it is never an observation's incompatibility, and no
//! transport between frames is claimed. Only the Resident absorbs, in the executed order of the
//! actual encounter.
//!
//! **The exact fixed-key filter.** For every key the memory keeps the affine fibre `c + N k` of model
//! states at the current crossing that reproduce every actual `(a, b)` absorbed so far. One actual
//! step restricts and then advances it:
//!
//! ```text
//! (P N) h = b − P c − Q a          its complete preimage h₀ + K j, or none
//! c ← F (c + N h₀) + G a,   N ← F N K   (reduced by the rank factorization; a singular F may erase directions)
//! ```
//!
//! A key whose observation has no preimage is **incompatible**, eliminated only by the exact
//! annihilator (`ExactRatMatrix::preimage_obstruction`), which is kept as its receipt. A key whose
//! charts cannot be read (a non-unique or inconsistent model commit) or whose arithmetic leaves its
//! carrier is **held**: its last certified fibre and its certified cut stay, beside the memory's actual
//! reached tick, and it is not a current-crossing alternative. The memory's tick advances with every
//! actual World step, whatever any key or any later comparison or deposit does; no step list is kept.
//!
//! **The return image** ([`WorldModel::predict`]). From a live fibre at the current crossing `T` and a
//! declared future incident word, with `Φ_j = F_(T+j−1)⋯F_T` and `Φ_0 = 1`, the return at the `j`-th
//! future step is
//!
//! ```text
//! b_(T+j) = P_(T+j) Φ_j (c + N k)  +  Σ_(i<j) P_(T+j) F_(T+j−1)⋯F_(T+i+1) G_(T+i) a_(T+i)  +  Q_(T+j) a_(T+j)
//!           free response            forced response
//! ```
//!
//! so at a constant material the free response at the `t`-th future step is `P F^(t−1) ξ_T`. One `k`
//! moves every step together: the image is one correlated fibre over the whole word, never a product of
//! per-step sets. A held key's span belongs to its certified cut, not to the current crossing, and an
//! incompatible key has none; both are refused. The image answers a declared word: in an actual
//! encounter each later incident wave depends on the returned ones through the continuing native
//! source, so the image is a model response, not a certificate of that closed loop, which the coupled
//! prospect below answers.
//!
//! **The coupled prospect** (C1b-2a, [`WorldModel::coupled_prospect`]). In an actual encounter each
//! later incident wave depends on the returned ones through the native source, so a declared word
//! does not give the actual future. The prepared native Word's own prospective passage
//! (`Word::prospective_coupled_passage`, opened on its actual unrun opening exactly as
//! `Word::prospective_feature` opens its baseline) is run with each emitted `a_t` answered by a live
//! key's charts, `b_t = P ξ_t + Q a_t` and `ξ_(t+1) = F ξ_t + G a_t`, from `ξ_T` at the World's crossing
//! `T`, step `t` read at commit `T + t − 1`. It predicts the port waves and the native station
//! features with their receiving logits: the native readout, not the World's observed face, whose
//! key-owned face relation is a separate join. The prepared Word, the actual World and this memory
//! stay unchanged. One `k` moves the whole passage together: the prospect is the passage from the
//! fibre's point and, per fibre direction, the exact change it makes to every predicted value, read as
//! the difference of two exact passages. The passage is affine in `ξ_T` because the admitted Word is
//! the exact unsplit quadratic one (`ActionProducer::of`) and the key's charts are linear; the sum of
//! the directions is checked against one more passage as a guard. The prepared action reads it before
//! its encounter ([`super::PreparedPhysicalAction::world_prospect`]).
//!
//! **The key's face** (C1b-2b, [`ModelKey::with_face`]). The World's observed target at a compared
//! epoch is its own face, `C_S x_S⁺ + C_R x_R⁺ + o` on the step's after-state, never the native
//! readout. A key may declare the face it hypothesizes, split at its own source extent; the prospect
//! then predicts that raw face at every compared epoch from the model state after the step, with the
//! same `k` as the waves and the native readout. The World's face coefficients are never read. A true
//! port law with a wrong face is a different key: a family may pair one law with several faces, and a
//! key that declares no face predicts none, so an undeclared or unobserved face constrains nothing.
//! Two boundaries hold. The raw affine face is not the grain-level reading the encounter compares
//! (`Face::of_read` at its grain), whose relation to it is not joined here. And predicting a declared
//! face eliminates no face hypothesis: the memory is filtered by the port observations `(a, b)` alone,
//! so no face key is thereby consistent with the observed faces, and none of this is learning.
//!
//! **The state-only matched control** (C2, [`WorldModel::carried`]). The consequence of retained actual
//! World history is read at one common crossing, between the bound memory and a matched control: the
//! memory from before an absorbed passage, carried through that passage's actual incident waves with
//! no restriction, `c ← F c + G a` and `N ← F N`. Everything actual is shared: the receiver with its
//! carry, material and opening, the one World and its clock, and the keys with their charts. The
//! control removes exactly the restriction by the passage's reflected waves and the eliminations it
//! made. The absorbed fibre lies in the carried one, so the bound memory's prospect of a later prepared
//! action lies in the control's ([`super::PreparedPhysicalAction::world_prospect_of`]), and a control
//! direction that changes a compared station's reading where no retained direction does is a reading
//! the retained history fixed. Where no retained direction moves a declared face, its grain reading is
//! the encounter's own reader applied to the predicted raw face, since that reader is a function of
//! the raw face; the relation for a plural image stays owed. The faces stay port-filtered: a false
//! face is never ruled out by this comparison.
//!
//! **Bits.** The memory's current bits ([`WorldModel::current_bits`]) are every key state's values and
//! cut and the reached tick; the Resident's state bits charge them at every step, whatever size the
//! fibres reach. The keys are immutable declarations, held separately as the World's own are.
//!
//! The owner's test is `tests/world_model.rs`; the receiving-phase record's §7 states this owner, its
//! acceptance and its receipts, and its atlas rows are the `hnn.world-model-*` rows. The bits read the
//! mutable model state only: not the immutable key laws, the solves' workspace or process memory. A
//! coupled passage also keeps the transient post-step states of that one passage (ticks by storage
//! values), never retained history; a CPU or CUDA memory budget counts that workspace and the rational
//! carrier sizes beyond the bits. Owed: the forward cover of a plural fibre at the receiver's grain
//! (its readings over the fibre, which needs a declared energy bound on it); the grain-level
//! observation relation of a declared face over a plural image (`Face::of_read` at the encounter's
//! grain) and the conditioning of retained fibres on actual face observations
//! (`NativeEncounter::observed` at the compared epochs); the Ask over keys, which would read the
//! coupled future of the key family per admitted wave where `PreparedPhysicalProbe::ask` reads the
//! receiving phase family at the native feature; learning through the model; and the World/Robin and
//! all-material first and second variation.

use crate::hnn::HnnError;
use crate::hnn::physical::action::WaveJointStep;
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::Word;
use crate::hnn::word::action::CoupledPassage;
use crate::holon::HolonState;
use crate::holon::law::{CommitCoefficients, HolonLaw, ReferenceHolon, Scheme};
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, sub};
use crate::receiver::reception::ReceiverFace;
use num_traits::{One, Signed, Zero};

/// [definition] **One key's charts at one step** (the module header): `ξ⁺ = F ξ + G a`,
/// `b = P ξ + Q a`, at the actual World's indexing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelCharts {
    pub f: ExactRatMatrix,
    pub g: ExactRatMatrix,
    pub p: ExactRatMatrix,
    pub q: ExactRatMatrix,
}

/// [definition] **A declared key of the native kind**: a midpoint port Holon law with no loaded
/// parametron, and the positive wave admittance of each of its external ports.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModelKey {
    law: ReferenceHolon,
    admittance: Vec<Rat>,
    face: Option<KeyFace>,
}

/// [definition] **A key's declared face** (the module header): the observer it hypothesizes for the
/// World's target face, a [`ReceiverFace`] with zero chart rate read on the model state split at
/// `source` (the source's coordinates, then the receiver's).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyFace {
    face: ReceiverFace,
    source: usize,
}

impl KeyFace {
    /// The declared face.
    pub fn face(&self) -> &ReceiverFace {
        &self.face
    }

    /// The source extent at which the model state splits.
    pub fn source(&self) -> usize {
        self.source
    }

    /// The raw face read on one model state.
    pub fn read(&self, state: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        let source = state.get(..self.source).ok_or(HnnError::Unadmitted {
            reason: "a face reads a model state that holds its declared source extent",
        })?;
        Ok(self.face.read(source, &state[self.source..])?)
    }
}

impl ModelKey {
    /// Declare a key, refused off the kind the actual World admits (`BoundJointWorld::new`).
    pub fn declare(law: ReferenceHolon, admittance: Vec<Rat>) -> Result<Self, HnnError> {
        let counts = law.holon().counts();
        if law.scheme() != Scheme::Midpoint
            || law.holon().loaded_parametron().is_some()
            || counts.external == 0
            || admittance.len() != counts.external
            || admittance.iter().any(|y| !y.is_positive())
        {
            return Err(HnnError::Unadmitted {
                reason: "a World model key is a midpoint port Holon with a positive wave admittance on every external port",
            });
        }
        Ok(Self {
            law,
            admittance,
            face: None,
        })
    }

    /// **Declare the face this key hypothesizes** (the module header): admitted only with a zero
    /// chart rate (the actual World admits no other, `BoundJointWorld::new`), a source extent inside
    /// the key's storage, and a read that succeeds on the zero state.
    pub fn with_face(mut self, face: ReceiverFace, source: usize) -> Result<Self, HnnError> {
        let declared = KeyFace { face, source };
        if declared
            .face
            .chart_rate()
            .iter()
            .any(|rate| !rate.is_zero())
            || source > self.extent()
            || declared.read(&vec![Rat::zero(); self.extent()]).is_err()
        {
            return Err(HnnError::Unadmitted {
                reason: "a key's face has zero chart rate and reads the key's own state split inside its storage",
            });
        }
        self.face = Some(declared);
        Ok(self)
    }

    /// The face this key declares, if any.
    pub fn face(&self) -> Option<&KeyFace> {
        self.face.as_ref()
    }

    /// The model state's extent `σ` (the law's storage).
    pub fn extent(&self) -> usize {
        self.law.holon().counts().storage
    }

    /// The external ports `π`.
    pub fn ports(&self) -> usize {
        self.law.holon().counts().external
    }

    /// The wave admittance of each external port: the key's declared wave frame.
    pub fn admittance(&self) -> &[Rat] {
        &self.admittance
    }

    /// The law's step: the key's declared clock.
    pub fn step(&self) -> &Rat {
        self.law.step()
    }

    /// **The charts at model clock `commit`** (the module header), read on unit columns.
    pub fn charts(&self, commit: u64) -> Result<ModelCharts, HnnError> {
        let holon = self.law.holon();
        let counts = holon.counts();
        let (sigma, n, pi) = (counts.storage, counts.total(), counts.external);
        let po = counts.storage + counts.resistive;
        let next = commit.checked_add(1).ok_or(HnnError::CountOverflow)?;
        let zero_input = vec![Rat::zero(); pi];
        let coefficients = |x: Vec<Rat>| {
            self.law.prepare_commit(
                &HolonState::at(x, commit),
                &zero_input,
                holon.storage_at(commit),
                holon.active().relation(),
                holon.storage_at(next),
            )
        };
        let base = coefficients(vec![Rat::zero(); sigma])?;
        if base.system.rows() != n || base.system.columns() != n {
            return Err(HnnError::Unadmitted {
                reason: "a square model midpoint Dirac commit before Robin coupling",
            });
        }
        // The coupled (z, e) system of the actual World's interact_wave, at this key's material.
        let mut rows = vec![vec![Rat::zero(); n + pi]; n + pi];
        for (i, row) in rows.iter_mut().enumerate().take(n) {
            for (j, entry) in row.iter_mut().enumerate().take(n) {
                *entry = base.system.get(i, j)?.clone();
            }
            for j in 0..pi {
                row[n + j] = -base.external_target.get(i, j)?.clone();
            }
        }
        for (i, y) in self.admittance.iter().enumerate() {
            let row = &mut rows[n + i];
            for (j, entry) in row.iter_mut().enumerate().take(n) {
                *entry = base.flow_coefficient.get(po + i, j)? / y;
            }
            row[n + i] = Rat::one();
        }
        let system = ExactRatMatrix::new(rows)?;
        // The actual World's Robin target and return: e + Y⁻¹(F_P z + c_P) = a, b = e − Y⁻¹(F_P z + c_P).
        let response =
            |at: &CommitCoefficients, incident: &[Rat]| -> Result<(Vec<Rat>, Vec<Rat>), HnnError> {
                let mut target = at.target.clone();
                target.extend(
                    (0..pi).map(|i| &incident[i] - &at.flow_constant[po + i] / &self.admittance[i]),
                );
                let solved = match system.preimage_fibre(&target)? {
                    Some((point, kernel)) if kernel.is_empty() => point,
                    _ => {
                        return Err(HnnError::Unadmitted {
                            reason: "a unique model midpoint commit under the Robin termination",
                        });
                    }
                };
                let flow = add(
                    &base.flow_coefficient.apply(&solved[..n])?,
                    &at.flow_constant,
                );
                let reflected = (0..pi)
                    .map(|i| &solved[n + i] - &flow[po + i] / &self.admittance[i])
                    .collect();
                Ok((solved[..sigma].to_vec(), reflected))
            };
        // Unit columns are the charts by `prepare_commit`'s identity (the module header); the zero
        // return here and the equal operator per unit state below are its guards.
        let (offset, offset_return) = response(&base, &zero_input)?;
        if offset
            .iter()
            .chain(&offset_return)
            .any(|value| !value.is_zero())
        {
            return Err(HnnError::Unadmitted {
                reason: "a linear model commit: the zero state under no incident wave returns nothing",
            });
        }
        let (mut f, mut p) = (Vec::with_capacity(sigma), Vec::with_capacity(sigma));
        for j in 0..sigma {
            let mut unit = vec![Rat::zero(); sigma];
            unit[j] = Rat::one();
            let at = coefficients(unit)?;
            if at.system != base.system
                || at.flow_coefficient != base.flow_coefficient
                || at.external_target != base.external_target
            {
                return Err(HnnError::Unadmitted {
                    reason: "a model commit whose operator does not depend on the state",
                });
            }
            let (state, reflected) = response(&at, &zero_input)?;
            f.push(state);
            p.push(reflected);
        }
        let (mut g, mut q) = (Vec::with_capacity(pi), Vec::with_capacity(pi));
        for k in 0..pi {
            let mut incident = zero_input.clone();
            incident[k] = Rat::one();
            let (state, reflected) = response(&base, &incident)?;
            g.push(state);
            q.push(reflected);
        }
        Ok(ModelCharts {
            f: columns(sigma, &f)?,
            g: columns(sigma, &g)?,
            p: columns(pi, &p)?,
            q: columns(pi, &q)?,
        })
    }
}

/// A matrix of `rows` rows from its columns.
fn columns(rows: usize, columns: &[Vec<Rat>]) -> Result<ExactRatMatrix, HnnError> {
    Ok(ExactRatMatrix::shaped(
        rows,
        columns.len(),
        (0..rows)
            .map(|i| columns.iter().map(|column| column[i].clone()).collect())
            .collect(),
    )?)
}

/// [definition] **An affine fibre of model states at the current crossing**: `point + span(directions)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StateFibre {
    pub point: Vec<Rat>,
    pub directions: Vec<Vec<Rat>>,
}

impl StateFibre {
    /// The whole state space of extent `sigma`: no state is known before an observation.
    pub fn whole(sigma: usize) -> Self {
        Self {
            point: vec![Rat::zero(); sigma],
            directions: (0..sigma)
                .map(|j| {
                    let mut unit = vec![Rat::zero(); sigma];
                    unit[j] = Rat::one();
                    unit
                })
                .collect(),
        }
    }

    /// Its exact bits: every coordinate of its point and directions, by numerator and denominator.
    pub fn bits(&self) -> u64 {
        self.point
            .iter()
            .chain(self.directions.iter().flatten())
            .map(value_bits)
            .sum()
    }
}

/// The exact bits of one value: its numerator's and its denominator's.
fn value_bits(value: &Rat) -> u64 {
    value.numer().bits() + value.denom().bits()
}

/// The exact bits of a clock reading.
fn clock_bits(tick: u64) -> u64 {
    u64::from(u64::BITS - tick.leading_zeros())
}

/// [definition] **Why a key is held** (the module header): its charts could not be read, or its
/// arithmetic left its carrier. Never an observation's incompatibility.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HeldReason {
    /// The key's model commit is not uniquely solvable under the Robin termination.
    Charts,
    /// An exact operation refused (an extent or shape the carrier cannot hold).
    Arithmetic,
}

/// [definition] **One key's state in the memory** (the module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KeyState {
    /// The fibre at the current crossing.
    Live(StateFibre),
    /// The last certified fibre and its certified cut; not a current-crossing alternative.
    Held {
        fibre: StateFibre,
        certified_tick: u64,
        reason: HeldReason,
    },
    /// Eliminated at `tick` by the exact annihilator of its observation's preimage.
    Incompatible { tick: u64, annihilator: Vec<Rat> },
}

impl KeyState {
    /// Its exact bits: two for its variant among three, then its values and its cut (and one for a
    /// held key's reason among two).
    pub fn bits(&self) -> u64 {
        2 + match self {
            Self::Live(fibre) => fibre.bits(),
            Self::Held {
                fibre,
                certified_tick,
                ..
            } => fibre.bits() + clock_bits(*certified_tick) + 1,
            Self::Incompatible { tick, annihilator } => {
                clock_bits(*tick) + annihilator.iter().map(value_bits).sum::<u64>()
            }
        }
    }
}

/// [definition] **A live key's return image over a declared future incident word** (the module
/// header): per future step, the free response of the fibre's point and the forced response of the
/// word, and, per fibre direction, its free response over the whole word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReturnImage {
    /// The current crossing `T` the image starts from.
    pub tick: u64,
    /// `free[j] = P_(T+j) Φ_j c`.
    pub free: Vec<Vec<Rat>>,
    /// `forced[j]`: the word's return from the zero state, its own step's `Q_(T+j) a_(T+j)` included.
    pub forced: Vec<Vec<Rat>>,
    /// `directions[r][j] = P_(T+j) Φ_j N e_r`: one direction moves every step together.
    pub directions: Vec<Vec<Vec<Rat>>>,
}

/// [definition] **One fibre direction's change to a coupled passage** (the module header): per
/// junction step the change of `(a_t, b_t)`, and per compared station the change of its native
/// feature and logits.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoupledChange {
    pub waves: Vec<(Vec<Rat>, Vec<Rat>)>,
    pub features: Vec<(usize, Vec<Rat>, Vec<Rat>)>,
    /// Per compared station the change of the key's declared raw face; empty without a face.
    pub faces: Vec<(usize, Vec<Rat>)>,
}

impl CoupledChange {
    /// The sum of two changes of one passage's shape.
    fn plus(&self, other: &Self) -> Result<Self, HnnError> {
        if self.waves.len() != other.waves.len()
            || self.features.len() != other.features.len()
            || self.faces.len() != other.faces.len()
            || self
                .features
                .iter()
                .zip(&other.features)
                .any(|(left, right)| left.0 != right.0)
            || self
                .faces
                .iter()
                .zip(&other.faces)
                .any(|(left, right)| left.0 != right.0)
        {
            return Err(HnnError::Unadmitted {
                reason: "changes of one coupled passage's shape",
            });
        }
        Ok(Self {
            waves: self
                .waves
                .iter()
                .zip(&other.waves)
                .map(|((a, b), (c, d))| (add(a, c), add(b, d)))
                .collect(),
            features: self
                .features
                .iter()
                .zip(&other.features)
                .map(|((station, f, l), (_, g, m))| (*station, add(f, g), add(l, m)))
                .collect(),
            faces: self
                .faces
                .iter()
                .zip(&other.faces)
                .map(|((station, f), (_, g))| (*station, add(f, g)))
                .collect(),
        })
    }
}

/// One key's passage: the native coupled passage and the key's declared raw faces at the compared
/// stations (empty without a face).
#[derive(Clone, Debug, PartialEq, Eq)]
struct KeyPassage {
    passage: CoupledPassage,
    faces: Vec<(usize, Vec<Rat>)>,
    /// The model state after the passage's last step.
    end: Vec<Rat>,
}

/// The exact change from one key passage to another of the same shape.
fn change(moved: &KeyPassage, point: &KeyPassage) -> Result<CoupledChange, HnnError> {
    let (m, p) = (&moved.passage, &point.passage);
    if m.waves.len() != p.waves.len()
        || m.features.len() != p.features.len()
        || moved.faces.len() != point.faces.len()
        || m.features
            .iter()
            .zip(&p.features)
            .any(|(left, right)| left.0 != right.0)
        || moved
            .faces
            .iter()
            .zip(&point.faces)
            .any(|(left, right)| left.0 != right.0)
    {
        return Err(HnnError::Unadmitted {
            reason: "two coupled passages of one shape",
        });
    }
    Ok(CoupledChange {
        waves: m
            .waves
            .iter()
            .zip(&p.waves)
            .map(|((a, b), (c, d))| (sub(a, c), sub(b, d)))
            .collect(),
        features: m
            .features
            .iter()
            .zip(&p.features)
            .map(|((station, f, l), (_, g, n))| (*station, sub(f, g), sub(l, n)))
            .collect(),
        faces: moved
            .faces
            .iter()
            .zip(&point.faces)
            .map(|((station, f), (_, g))| (*station, sub(f, g)))
            .collect(),
    })
}

/// [definition] **A live key's coupled prospect** (the module header): the passage from the fibre's
/// point at the current crossing `tick`, and one change per fibre direction; the predicted values are
/// `point + Σ_r k_r directions[r]` with one `k` for the whole passage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoupledProspect {
    pub tick: u64,
    pub point: CoupledPassage,
    /// The key's declared raw face at each compared station from the fibre's point; empty without a
    /// face.
    pub faces: Vec<(usize, Vec<Rat>)>,
    pub directions: Vec<CoupledChange>,
}

/// [definition] **The World model's memory** (the module header): the declared keys, each key's
/// state, and the actual tick the memory has reached. No step list is kept.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WorldModel {
    keys: Vec<ModelKey>,
    states: Vec<KeyState>,
    tick: u64,
}

/// One step's outcome for a live key.
enum Stepped {
    Live(StateFibre),
    Incompatible(Vec<Rat>),
}

impl WorldModel {
    /// **Found the memory** at the actual World's tick `tick`, every key's fibre the whole state space.
    pub fn found(keys: Vec<ModelKey>, tick: u64) -> Result<Self, HnnError> {
        if keys.is_empty() {
            return Err(HnnError::Unadmitted {
                reason: "a World model declares at least one key",
            });
        }
        let states = keys
            .iter()
            .map(|key| KeyState::Live(StateFibre::whole(key.extent())))
            .collect();
        Ok(Self { keys, states, tick })
    }

    /// [definition; agent-inferred, October 9; the held-carry record §5e] **The memory's learned part
    /// as exact text**: the tick, and each key's state. A Live state writes its fibre's point and
    /// directions; a Held state its fibre, certified tick and reason; an Incompatible state its
    /// elimination tick and annihilator. Rationals are written `p/q`. The keys are declarations, not
    /// learned, so they are not written: [`Self::restored`] re-declares them.
    pub fn to_text(&self) -> String {
        let row = |values: &[Rat]| {
            values
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(" ")
        };
        let fibre = |out: &mut String, fibre: &StateFibre| {
            *out += &format!("point {}\n", row(&fibre.point));
            for direction in &fibre.directions {
                *out += &format!("direction {}\n", row(direction));
            }
        };
        let mut out = format!("world-model v1\ntick {}\nkeys {}\n", self.tick, self.states.len());
        for state in &self.states {
            match state {
                KeyState::Live(f) => {
                    out += "live\n";
                    fibre(&mut out, f);
                }
                KeyState::Held {
                    fibre: f,
                    certified_tick,
                    reason,
                } => {
                    out += &format!(
                        "held {certified_tick} {}\n",
                        match reason {
                            HeldReason::Charts => "charts",
                            HeldReason::Arithmetic => "arithmetic",
                        }
                    );
                    fibre(&mut out, f);
                }
                KeyState::Incompatible { tick, annihilator } => {
                    out += &format!("incompatible {tick}\nannihilator {}\n", row(annihilator));
                }
            }
            out += "end\n";
        }
        out
    }

    /// **Restore the memory from its text** ([`Self::to_text`]) on its declared `keys`. It is refused
    /// for another version, another key count, a malformed value, or a fibre whose extents are not
    /// its key's.
    pub fn restored(keys: Vec<ModelKey>, text: &str) -> Result<Self, HnnError> {
        let refuse = || HnnError::Unadmitted {
            reason: "a World model's text restores on its own declared keys",
        };
        let values = |rest: &str| -> Result<Vec<Rat>, HnnError> {
            rest.split_whitespace()
                .map(|v| v.parse::<Rat>().map_err(|_| refuse()))
                .collect()
        };
        let mut lines = text.lines();
        if lines.next() != Some("world-model v1") {
            return Err(refuse());
        }
        let tick: u64 = lines
            .next()
            .and_then(|l| l.strip_prefix("tick "))
            .and_then(|t| t.parse().ok())
            .ok_or_else(refuse)?;
        let count: usize = lines
            .next()
            .and_then(|l| l.strip_prefix("keys "))
            .and_then(|t| t.parse().ok())
            .ok_or_else(refuse)?;
        if count != keys.len() {
            return Err(refuse());
        }
        let mut states = Vec::with_capacity(count);
        for key in &keys {
            let head = lines.next().ok_or_else(refuse)?;
            let read_fibre = |lines: &mut std::str::Lines<'_>| -> Result<StateFibre, HnnError> {
                let point = values(
                    lines
                        .next()
                        .and_then(|l| l.strip_prefix("point"))
                        .ok_or_else(refuse)?,
                )?;
                let mut directions = Vec::new();
                loop {
                    let line = lines.next().ok_or_else(refuse)?;
                    if line == "end" {
                        break;
                    }
                    directions.push(values(line.strip_prefix("direction").ok_or_else(refuse)?)?);
                }
                if point.len() != key.extent() || directions.iter().any(|d| d.len() != key.extent()) {
                    return Err(refuse());
                }
                Ok(StateFibre { point, directions })
            };
            let state = if head == "live" {
                KeyState::Live(read_fibre(&mut lines)?)
            } else if let Some(rest) = head.strip_prefix("held ") {
                let mut parts = rest.split_whitespace();
                let certified_tick: u64 =
                    parts.next().and_then(|t| t.parse().ok()).ok_or_else(refuse)?;
                let reason = match parts.next() {
                    Some("charts") => HeldReason::Charts,
                    Some("arithmetic") => HeldReason::Arithmetic,
                    _ => return Err(refuse()),
                };
                KeyState::Held {
                    fibre: read_fibre(&mut lines)?,
                    certified_tick,
                    reason,
                }
            } else if let Some(rest) = head.strip_prefix("incompatible ") {
                let eliminated: u64 = rest.trim().parse().map_err(|_| refuse())?;
                let annihilator = values(
                    lines
                        .next()
                        .and_then(|l| l.strip_prefix("annihilator"))
                        .ok_or_else(refuse)?,
                )?;
                if lines.next() != Some("end") {
                    return Err(refuse());
                }
                KeyState::Incompatible {
                    tick: eliminated,
                    annihilator,
                }
            } else {
                return Err(refuse());
            };
            states.push(state);
        }
        if lines.next().is_some() {
            return Err(refuse());
        }
        Ok(Self { keys, states, tick })
    }

    /// The declared keys.
    pub fn keys(&self) -> &[ModelKey] {
        &self.keys
    }

    /// Each key's state, in declared order.
    pub fn states(&self) -> &[KeyState] {
        &self.states
    }

    /// The actual World tick the memory has reached.
    pub fn tick(&self) -> u64 {
        self.tick
    }

    /// **The memory's current bits** (the module header): every key state's and the reached tick's.
    pub fn current_bits(&self) -> u64 {
        self.states.iter().map(KeyState::bits).sum::<u64>() + clock_bits(self.tick)
    }

    /// **Predict a live key's returns** over a declared future incident word, one incident wave per
    /// step, from the current crossing (the module header). A held or incompatible key is refused.
    pub fn predict(&self, key: usize, word: &[Vec<Rat>]) -> Result<ReturnImage, HnnError> {
        let (Some(model), Some(state)) = (self.keys.get(key), self.states.get(key)) else {
            return Err(HnnError::Unadmitted {
                reason: "a prediction names a declared key",
            });
        };
        let KeyState::Live(fibre) = state else {
            return Err(HnnError::Unadmitted {
                reason: "a prediction starts from a live key at the current crossing; a held or incompatible key's span is refused",
            });
        };
        if word.iter().any(|incident| incident.len() != model.ports()) {
            return Err(HnnError::Unadmitted {
                reason: "a predicted word declares an incident wave on every external port",
            });
        }
        let mut point = fibre.point.clone();
        let mut forced_state = vec![Rat::zero(); fibre.point.len()];
        let mut spans = fibre.directions.clone();
        let mut free = Vec::with_capacity(word.len());
        let mut forced = Vec::with_capacity(word.len());
        let mut directions: Vec<Vec<Vec<Rat>>> = vec![Vec::with_capacity(word.len()); spans.len()];
        for (j, incident) in word.iter().enumerate() {
            let offset = u64::try_from(j).map_err(|_| HnnError::CountOverflow)?;
            let commit = self
                .tick
                .checked_add(offset)
                .ok_or(HnnError::CountOverflow)?;
            let charts = model.charts(commit)?;
            free.push(charts.p.apply(&point)?);
            forced.push(add(
                &charts.p.apply(&forced_state)?,
                &charts.q.apply(incident)?,
            ));
            for (span, image) in spans.iter().zip(directions.iter_mut()) {
                image.push(charts.p.apply(span)?);
            }
            point = charts.f.apply(&point)?;
            forced_state = add(&charts.f.apply(&forced_state)?, &charts.g.apply(incident)?);
            for span in &mut spans {
                *span = charts.f.apply(span)?;
            }
        }
        Ok(ReturnImage {
            tick: self.tick,
            free,
            forced,
            directions,
        })
    }

    /// **The coupled prospect of a live key** (the module header): the prepared native Word's coupled
    /// prospective passage from the fibre's point, and each fibre direction's exact change to every
    /// predicted wave and feature. A held or incompatible key is refused.
    pub fn coupled_prospect(
        &self,
        key: usize,
        word: &Word<'_>,
        source_ring: usize,
        phases: &ReceivingPhases,
        compared: &[bool],
    ) -> Result<CoupledProspect, HnnError> {
        let (model, fibre) = self.live(key)?;
        let passage = |start: &[Rat]| {
            self.coupled_from(
                model,
                start,
                word,
                source_ring,
                phases,
                compared,
                &mut |_: &Word<'_>, _: usize| -> Result<(), HnnError> { Ok(()) },
            )
        };
        let point = passage(&fibre.point)?;
        let mut directions = Vec::with_capacity(fibre.directions.len());
        for direction in &fibre.directions {
            directions.push(change(&passage(&add(&fibre.point, direction))?, &point)?);
        }
        if let Some((first, rest)) = directions.split_first() {
            let mut summed_state = fibre.point.clone();
            for direction in &fibre.directions {
                summed_state = add(&summed_state, direction);
            }
            let summed = rest
                .iter()
                .try_fold(first.clone(), |total, next| total.plus(next))?;
            if change(&passage(&summed_state)?, &point)? != summed {
                return Err(HnnError::Unadmitted {
                    reason: "a coupled passage affine in the model state",
                });
            }
        }
        Ok(CoupledProspect {
            tick: self.tick,
            point: point.passage,
            faces: point.faces,
            directions,
        })
    }

    /// The declared key `key` and its fibre at the current crossing, refused unless it is live.
    fn live(&self, key: usize) -> Result<(&ModelKey, &StateFibre), HnnError> {
        let (Some(model), Some(state)) = (self.keys.get(key), self.states.get(key)) else {
            return Err(HnnError::Unadmitted {
                reason: "a prospect names a declared key",
            });
        };
        let KeyState::Live(fibre) = state else {
            return Err(HnnError::Unadmitted {
                reason: "a prospect starts from a live key at the current crossing; a held or incompatible key's span is refused",
            });
        };
        Ok((model, fibre))
    }

    /// [definition; agent-inferred, October 10; the held-carry record §7b] **The located prospect
    /// with its material tangents**: the coupled passage from the key's located point, with each
    /// tangent riding it tick by tick through the key's charts at the same commits the passage's
    /// returns read (`MaterialTangent::step_through_port`), and held at every compared station with
    /// the observed face's tangent read through the key's declared face, each station numbered by
    /// its rank among the compared ones as the prospect's comparison numbers it. It is the actual encounter's
    /// tangent law (`PhysicalReceiver::execute_prepared`) on the prospective Word: the key stands for
    /// the World in both. Refused unless the key is live, its fibre is a point, and it declares a face.
    pub fn located_prospect_with_tangents(
        &self,
        key: usize,
        word: &Word<'_>,
        source_ring: usize,
        phases: &ReceivingPhases,
        compared: &[bool],
        tangents: &mut [crate::hnn::word::continuation::MaterialTangent],
    ) -> Result<CoupledProspect, HnnError> {
        let (_, fibre) = self.live(key)?;
        if !fibre.directions.is_empty() {
            return Err(HnnError::Unadmitted {
                reason: "a prospect's tangents ride a located World state: the key's fibre is a point",
            });
        }
        let start = fibre.point.clone();
        Ok(self
            .located_passage_with_tangents(
                key,
                &start,
                self.tick,
                word,
                source_ring,
                phases,
                compared,
                tangents,
            )?
            .0)
    }

    /// [definition; agent-inferred, October 10; the held-carry record §7f] **A located passage from
    /// any key state and clock**: the coupled passage of a live point-fibre key from `start` at model
    /// clock `tick`, with tangents riding it as in [`Self::located_prospect_with_tangents`]. Returns
    /// the prospect and the key state at the passage's end, which the next encounter of a schedule
    /// starts from (at `tick` plus the passage's junction steps).
    #[allow(clippy::too_many_arguments)]
    pub fn located_passage_with_tangents(
        &self,
        key: usize,
        start: &[Rat],
        tick: u64,
        word: &Word<'_>,
        source_ring: usize,
        phases: &ReceivingPhases,
        compared: &[bool],
        tangents: &mut [crate::hnn::word::continuation::MaterialTangent],
    ) -> Result<(CoupledProspect, Vec<Rat>), HnnError> {
        let (model, fibre) = self.live(key)?;
        if !fibre.directions.is_empty() {
            return Err(HnnError::Unadmitted {
                reason: "a prospect's tangents ride a located World state: the key's fibre is a point",
            });
        }
        let face = model.face().ok_or(HnnError::Unadmitted {
            reason: "a prospect's tangents read the key's declared face",
        })?;
        let epochs: Vec<usize> = phases.epochs().collect();
        let mut observer = |word: &Word<'_>, t: usize| -> Result<(), HnnError> {
            let offset = t
                .checked_sub(1)
                .and_then(|offset| u64::try_from(offset).ok())
                .ok_or(HnnError::CountOverflow)?;
            let charts = model.charts(tick.checked_add(offset).ok_or(HnnError::CountOverflow)?)?;
            for tangent in tangents.iter_mut() {
                tangent.step_through_port(word, &charts.f, &charts.g, &charts.p, &charts.q)?;
                for (station, (&epoch, &yes)) in epochs.iter().zip(compared).enumerate() {
                    if !yes || epoch != t {
                        continue;
                    }
                    let observed = match tangent.world() {
                        Some(psi) => Some(sub(
                            &face.read(psi)?,
                            &face.read(&vec![Rat::zero(); psi.len()])?,
                        )),
                        None => None,
                    };
                    // Numbered as the prospect's comparison numbers its stations: by rank among
                    // the compared ones (`PhysicalReceiver::world_prospect_ratio`).
                    let rank = compared[..station].iter().filter(|&&c| c).count();
                    tangent.observe_station(word, phases.ring(), rank, observed)?;
                }
            }
            Ok(())
        };
        let point = self.coupled_at(
            model,
            start,
            tick,
            word,
            source_ring,
            phases,
            compared,
            &mut observer,
        )?;
        Ok((
            CoupledProspect {
                tick,
                point: point.passage,
                faces: point.faces,
                directions: Vec::new(),
            },
            point.end,
        ))
    }

    /// The coupled passage from one model state `ξ_T`, step `t` answered at commit `T + t − 1`,
    /// with the key's declared raw face read on the state after the step at every compared epoch,
    /// and `observer` beside the Word after each step's return.
    #[allow(clippy::too_many_arguments)]
    fn coupled_from(
        &self,
        model: &ModelKey,
        start: &[Rat],
        word: &Word<'_>,
        source_ring: usize,
        phases: &ReceivingPhases,
        compared: &[bool],
        observer: &mut crate::hnn::word::action::PassageObserver<'_>,
    ) -> Result<KeyPassage, HnnError> {
        self.coupled_at(model, start, self.tick, word, source_ring, phases, compared, observer)
    }

    /// The coupled passage from model state `start` at model clock `tick` (as
    /// [`Self::coupled_from`], whose clock is the memory's own).
    #[allow(clippy::too_many_arguments)]
    fn coupled_at(
        &self,
        model: &ModelKey,
        start: &[Rat],
        tick: u64,
        word: &Word<'_>,
        source_ring: usize,
        phases: &ReceivingPhases,
        compared: &[bool],
        observer: &mut crate::hnn::word::action::PassageObserver<'_>,
    ) -> Result<KeyPassage, HnnError> {
        let mut state = start.to_vec();
        let mut states = vec![start.to_vec()];
        let mut returns = |t: usize, incident: &[Rat]| -> Result<Vec<Rat>, HnnError> {
            let offset = t
                .checked_sub(1)
                .and_then(|offset| u64::try_from(offset).ok())
                .ok_or(HnnError::CountOverflow)?;
            let commit = tick.checked_add(offset).ok_or(HnnError::CountOverflow)?;
            let charts = model.charts(commit)?;
            let reflected = add(&charts.p.apply(&state)?, &charts.q.apply(incident)?);
            state = add(&charts.f.apply(&state)?, &charts.g.apply(incident)?);
            states.push(state.clone());
            Ok(reflected)
        };
        let passage = word.prospective_coupled_passage(
            source_ring,
            phases,
            compared,
            &mut returns,
            observer,
        )?;
        let mut faces = Vec::new();
        if let Some(face) = model.face() {
            for (station, epoch) in phases.epochs().enumerate() {
                if !compared.get(station).copied().unwrap_or(false) {
                    continue;
                }
                let after = states.get(epoch).ok_or(HnnError::WordEnded {
                    ticks: states.len() - 1,
                })?;
                faces.push((station, face.read(after)?));
            }
        }
        let end = states.last().cloned().unwrap_or_else(|| start.to_vec());
        Ok(KeyPassage {
            passage,
            faces,
            end,
        })
    }

    /// **Absorb one actually executed World step** (the module header): every live key is restricted
    /// by the step's actual `(a, b)` and advanced; a held or incompatible key is unchanged; the
    /// memory's tick advances in every case. It cannot fail: a key's own failure holds that key.
    /// Only the Resident calls it, with the encounter's executed steps in their order, so a replayed
    /// or misclocked receipt has no path in.
    pub(crate) fn absorb(&mut self, step: &WaveJointStep) {
        let commit = self.tick;
        for (key, state) in self.keys.iter().zip(self.states.iter_mut()) {
            let KeyState::Live(fibre) = state else {
                continue;
            };
            let outcome = key
                .charts(commit)
                .map_err(|_| HeldReason::Charts)
                .and_then(|charts| {
                    stepped(&charts, fibre, &step.incident, &step.reflected)
                        .map_err(|_| HeldReason::Arithmetic)
                });
            *state = match outcome {
                Ok(Stepped::Live(next)) => KeyState::Live(next),
                Ok(Stepped::Incompatible(annihilator)) => KeyState::Incompatible {
                    tick: commit,
                    annihilator,
                },
                Err(reason) => KeyState::Held {
                    fibre: fibre.clone(),
                    certified_tick: commit,
                    reason,
                },
            };
        }
        self.tick = commit.saturating_add(1);
    }

    /// **The state-only matched control of a declared incident word** (C2; the module header): the
    /// memory as it would stand after the word had no reflected wave restricted it. Every live key's
    /// fibre is carried by its own charts at the memory's commits, `c ← F c + G a` and `N ← F N`,
    /// reduced to a basis as an absorbed step's is; a key whose charts cannot be read, or whose
    /// arithmetic leaves its carrier, is held at its last fibre as an absorbed step holds it; a held or
    /// incompatible key is unchanged; and the tick advances by the word's length. It returns a new
    /// memory and reads and writes nothing actual: only the Resident's memory absorbs, and this one is
    /// never bound.
    ///
    /// Carried through the incident waves of an absorbed passage, from the memory that absorbed it,
    /// the control removes exactly the restriction by that passage's reflected waves and the
    /// eliminations it made, and nothing else: an absorbed step's `c + N h₀` and `N K` advance into
    /// `F c + G a + F N h₀` and `F N K`, both in the carried `F c + G a + span(F N)`, so the absorbed
    /// fibre lies in the carried one at every step.
    pub fn carried(&self, word: &[Vec<Rat>]) -> Result<Self, HnnError> {
        let mut carried = self.clone();
        for incident in word {
            let commit = carried.tick;
            for (key, state) in carried.keys.iter().zip(carried.states.iter_mut()) {
                let KeyState::Live(fibre) = state else {
                    continue;
                };
                if incident.len() != key.ports() {
                    return Err(HnnError::Unadmitted {
                        reason: "a carried word declares an incident wave on every external port",
                    });
                }
                let outcome =
                    key.charts(commit)
                        .map_err(|_| HeldReason::Charts)
                        .and_then(|charts| {
                            advanced(&charts, fibre, incident).map_err(|_| HeldReason::Arithmetic)
                        });
                *state = match outcome {
                    Ok(next) => KeyState::Live(next),
                    Err(reason) => KeyState::Held {
                        fibre: fibre.clone(),
                        certified_tick: commit,
                        reason,
                    },
                };
            }
            carried.tick = commit.checked_add(1).ok_or(HnnError::CountOverflow)?;
        }
        Ok(carried)
    }
}

/// One live key's fibre carried through one incident wave with no restriction (the state-only
/// matched control, [`WorldModel::carried`]): `c ← F c + G a` and `N ← F N`.
fn advanced(
    charts: &ModelCharts,
    fibre: &StateFibre,
    incident: &[Rat],
) -> Result<StateFibre, HnnError> {
    let sigma = fibre.point.len();
    let point = add(&charts.f.apply(&fibre.point)?, &charts.g.apply(incident)?);
    let carried: Vec<Vec<Rat>> = fibre
        .directions
        .iter()
        .map(|direction| charts.f.apply(direction))
        .collect::<Result<_, _>>()?;
    Ok(StateFibre {
        point,
        directions: basis(sigma, &carried)?,
    })
}

/// A carried span reduced to a basis by the rank factorization: a singular `F` may erase
/// directions, and an empty span stays empty.
fn basis(sigma: usize, carried: &[Vec<Rat>]) -> Result<Vec<Vec<Rat>>, HnnError> {
    if carried.is_empty() {
        return Ok(Vec::new());
    }
    let factor = columns(sigma, carried)?.rank_factorization()?;
    let left = &factor.left;
    let directions = (0..left.columns())
        .map(|j| {
            (0..left.rows())
                .map(|i| left.get(i, j).cloned())
                .collect::<Result<Vec<Rat>, _>>()
        })
        .collect::<Result<Vec<Vec<Rat>>, _>>()?;
    Ok(directions)
}

/// One live key's restriction by `(a, b)` and its advance (the module header).
fn stepped(
    charts: &ModelCharts,
    fibre: &StateFibre,
    incident: &[Rat],
    reflected: &[Rat],
) -> Result<Stepped, HnnError> {
    let sigma = fibre.point.len();
    let directions = columns(sigma, &fibre.directions)?;
    // (P N) h = b − P c − Q a.
    let pn = charts.p.multiply(&directions)?;
    let rhs = sub(
        &sub(reflected, &charts.p.apply(&fibre.point)?),
        &charts.q.apply(incident)?,
    );
    let Some((h0, kernel)) = pn.preimage_fibre(&rhs)? else {
        let annihilator = pn.preimage_obstruction(&rhs)?.ok_or(HnnError::Unadmitted {
            reason: "an observation outside the image carries its annihilator",
        })?;
        return Ok(Stepped::Incompatible(annihilator));
    };
    // c + N h₀ and N K, then c ← F(c + N h₀) + G a and N ← F N K.
    let restricted = add(&fibre.point, &directions.apply(&h0)?);
    let point = add(&charts.f.apply(&restricted)?, &charts.g.apply(incident)?);
    let carried: Vec<Vec<Rat>> = kernel
        .iter()
        .map(|k| charts.f.apply(&directions.apply(k)?))
        .collect::<Result<_, _>>()?;
    Ok(Stepped::Live(StateFibre {
        point,
        directions: basis(sigma, &carried)?,
    }))
}
