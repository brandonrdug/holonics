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
//! stepping or elimination rule enters. The reading certifies its own linearity: the commit's operator
//! is the same at every unit state, and the zero state under no incident wave returns nothing.
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
//! [incomplete, the first partial pin] Not yet joined here: the free response and the affine return
//! image over a fibre (`predict`), the bits charged by the Resident, the owner's test, the record's §7
//! update and the atlas row handoff. Owed beyond C1b-1: C2's finite forward cover, the Ask over keys,
//! learning through the model, and the World/Robin and all-material first and second variation.

use crate::hnn::HnnError;
use crate::hnn::physical::action::WaveJointStep;
use crate::holon::HolonState;
use crate::holon::law::{CommitCoefficients, HolonLaw, ReferenceHolon, Scheme};
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, sub};
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
        Ok(Self { law, admittance })
    }

    /// The model state's extent `σ` (the law's storage).
    pub fn extent(&self) -> usize {
        self.law.holon().counts().storage
    }

    /// The external ports `π`.
    pub fn ports(&self) -> usize {
        self.law.holon().counts().external
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
        for i in 0..pi {
            for j in 0..n {
                rows[n + i][j] = base.flow_coefficient.get(po + i, j)? / &self.admittance[i];
            }
            rows[n + i][n + i] = Rat::one();
        }
        let system = ExactRatMatrix::new(rows)?;
        // The actual World's Robin target and return: e + Y⁻¹(F_P z + c_P) = a, b = e − Y⁻¹(F_P z + c_P).
        let response = |at: &CommitCoefficients,
                        incident: &[Rat]|
         -> Result<(Vec<Rat>, Vec<Rat>), HnnError> {
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
        // Unit columns are the charts exactly: the commit's operator does not depend on the state
        // (checked per column), its target and flow constant are linear in it (`prepare_commit`),
        // and the zero state under no incident wave returns nothing (checked here).
        let (offset, offset_return) = response(&base, &zero_input)?;
        if offset.iter().chain(&offset_return).any(|value| !value.is_zero()) {
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

    /// **Absorb one actually executed World step** (the module header): every live key is restricted
    /// by the step's actual `(a, b)` and advanced; a held or incompatible key is unchanged; the
    /// memory's tick advances in every case. It cannot fail: a key's own failure holds that key.
    pub fn absorb(&mut self, step: &WaveJointStep) {
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
        let annihilator = pn
            .preimage_obstruction(&rhs)?
            .ok_or(HnnError::Unadmitted {
                reason: "an observation outside the image carries its annihilator",
            })?;
        return Ok(Stepped::Incompatible(annihilator));
    };
    // c + N h₀ and N K, then c ← F(c + N h₀) + G a and N ← F N K.
    let restricted = add(&fibre.point, &directions.apply(&h0)?);
    let point = add(
        &charts.f.apply(&restricted)?,
        &charts.g.apply(incident)?,
    );
    let carried: Vec<Vec<Rat>> = kernel
        .iter()
        .map(|k| charts.f.apply(&directions.apply(k)?))
        .collect::<Result<_, _>>()?;
    let directions = if carried.is_empty() {
        Vec::new()
    } else {
        let factor = columns(sigma, &carried)?.rank_factorization()?;
        let left = &factor.left;
        (0..left.columns())
            .map(|j| (0..left.rows()).map(|i| left.get(i, j).cloned()).collect())
            .collect::<Result<_, _>>()?
    };
    Ok(Stepped::Live(StateFibre { point, directions }))
}
