//! **The Holon law: advance, receive, interconnect, restrict, pull back — with its energy balance.**
//!
//! [definition] The five statements (`Holon/Law`): **advance** — one implicit-midpoint step
//! has zero balance residual (`Holon/Law.advance_law`, from
//! `Holon/Element.midpoint_balance`), and backward Euler carries the defect
//! `−½⟨Δq, QΔq⟩` (`Holon/Element.backwardEuler_balance`); **receive** — the zero-storage
//! specialization of joint reception ([`crate::receiver::reception`],
//! `Holarchy/Reception.zero_storage_receiver_is_passive_reading`): the receiver reads the
//! source's effort at zero power (`Holon/Law.passive_reading`) while the source advances by its
//! own law, and an active receiver through an interface conductance `G` satisfies
//! `P_H + P_R = −D_Σ`, `D_Σ = ⟨Δ, GΔ⟩ ≥ 0` for passive `G` (`Holon/Law.active_receiver_law`);
//! **interconnect** — a Holon of Holons is a Holon: the law on the whole of the Holarchy
//! [`Holon::interconnect`] returns (`Holon/Law.PortHolon.interconnect`,
//! `Holarchy/Join.joinHolon`); **restrict** — the
//! pushforward (`Holon/Restriction.pushforwardD_isDirac`), scale square and Kron reduction;
//! **pullback** — efforts move by the transpose and power is preserved
//! (`Holon/Law.pullback_law`). The continuous balance is
//! `Holon/Element.PortHolon.energy_balance`; with learning and deposition it is
//! `Holon/Deposition.learned_energy_balance` and, per commit,
//! `Holon/Deposition.commit_balance`.
//!
//! [definition; agent-inferred] **The reference motion is the Dirac form itself.** One step solves,
//! exactly over ℚ, for `(x⁺, f_R, f_P, f_A)` such that the step bond
//! `(−Δx/h, ē; f_R, −R f_R; f_P, u; f_A, L f_A)` lies in `D`, with `ē = Q(x + x⁺)/2` (implicit
//! midpoint) or `Q x⁺` (backward Euler) and the external efforts `u` the declared input. For the
//! medium this is `q⁺ − q = h((J − R + L) Q q̄ + B u)`, the Lean step; for an interconnected Holon it
//! is the same law on the joined structure, so interaction needs no second stepping rule. Power
//! neutrality of `D` gives `⟨ē, Δx⟩ = h(−⟨f_R,Rf_R⟩ + ⟨u,f_P⟩ + ⟨f_A,Lf_A⟩)` exactly, and the
//! balance's residual is computed, not assumed.
//!
//! | Lean | Rust |
//! |---|---|
//! | `advance_law`, `midpoint_balance` | [`ReferenceHolon`] with [`Scheme::Midpoint`] |
//! | `backwardEuler_balance`, `backwardEuler_defect_witness` | [`Scheme::BackwardEuler`] |
//! | `commit_balance`, `deposition_work` | [`ReferenceHolon::commit`] |
//! | `passive_reading`, `Holarchy/Reception.zero_storage_receiver_is_passive_reading` | [`HolonLaw::receive`] |
//! | `PortHolon.interconnect`, `Holarchy/Join.joinHolon` | [`HolonLaw::interconnect`] |
//! | `active_receiver_law` | [`active_receiver`] |
//! | `pullback_law` | [`HolonLaw::pullback`] |
//!
//! [definition] **Receivers** are Holons at ports: the passive coholon, the active receiver with its
//! declared power, and the faces they are charted by, in [`crate::receiver::face`].

use crate::ratio::Rat;
use num_traits::{One, Zero};

use crate::holarchy::Gluing;
use crate::holon::dirac::DiracStructure;
use crate::holon::element::{ResistiveRelation, storage_energy};
use crate::holon::port::Bond;
use crate::holon::restriction::PortMap;
use crate::holon::{Holon, HolonError, HolonState, KindBonds};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::inertia::SymmetricForm;
use crate::ratio::linear::vector::{at, dot, form_matrix, matrix, neg, quad, sub};
use crate::ratio::rat;
use crate::receiver::receipt::ReceiptLaw;
use crate::receiver::reception::{InteractionReturn, JointLaw, ReceiverFace};

/// [definition] **One energy balance**, every term exact:
/// `stored_change = −dissipated + port + active + deposition_work + discretization_defect + residual`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EnergyBalance {
    /// `E(x⁺; Q⁺) − E(x; Q)`.
    pub stored_change: Rat,
    /// `h⟨f_R, R f_R⟩ ≥ 0` for a certified resistance.
    pub dissipated: Rat,
    /// `h⟨e_P, f_P⟩`: power supplied through the external ports.
    pub port: Rat,
    /// `h⟨f_A, L f_A⟩`: the declared active power.
    pub active: Rat,
    /// `½⟨x⁺, (Q⁺ − Q) x⁺⟩`: work done by changing the constitution.
    pub deposition_work: Rat,
    /// The scheme's own term: `0` for the implicit midpoint, `−½⟨Δq, QΔq⟩` for backward Euler.
    pub discretization_defect: Rat,
    /// What the other terms do not account for. Zero for a conforming law.
    pub residual: Rat,
}

impl EnergyBalance {
    /// The balance of the declared terms, with the residual computed rather than supplied:
    /// `residual = stored_change − (−dissipated + port + active + deposition_work +
    /// discretization_defect)`. Engine readings that already carry these terms convert through it.
    pub fn closed(
        stored_change: Rat,
        dissipated: Rat,
        port: Rat,
        active: Rat,
        deposition_work: Rat,
        discretization_defect: Rat,
    ) -> Self {
        let residual = &stored_change
            - (-&dissipated + &port + &active + &deposition_work + &discretization_defect);
        Self {
            stored_change,
            dissipated,
            port,
            active,
            deposition_work,
            discretization_defect,
            residual,
        }
    }

    pub fn is_exact(&self) -> bool {
        self.residual.is_zero()
    }

    /// The word part: the balance before any deposit, `−dissipated + port + active + defect`.
    pub fn word_change(&self) -> Rat {
        -&self.dissipated + &self.port + &self.active + &self.discretization_defect
    }

    /// **Join an active receiver's delivered power** ([`crate::receiver::face::ReceiverExchange::delivered`]):
    /// the power becomes part of the active term and the residual is recomputed, so a balance that
    /// did not yet count a joined receiver closes exactly when it does.
    pub fn joined_active(&self, delivered: &Rat) -> Self {
        Self::closed(
            self.stored_change.clone(),
            self.dissipated.clone(),
            self.port.clone(),
            &self.active + delivered,
            self.deposition_work.clone(),
            self.discretization_defect.clone(),
        )
    }
}

/// [definition] The discrete stepping scheme.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Scheme {
    /// `ē = Q(x + x⁺)/2`: exact discrete balance.
    Midpoint,
    /// `ē = Q x⁺`: carries `−½⟨Δq, QΔq⟩`.
    BackwardEuler,
}

/// One word of motion: the reached state, the step bond it was admitted with, and its balance.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Advance {
    pub state: HolonState,
    /// The step bond `(−Δx/h, ē; f_R, −R f_R; f_P, u; f_A, L f_A)`, admitted by `D`.
    pub bond: Bond,
    pub balance: EnergyBalance,
}

/// [definition] **A passive coholon's reading** (`Holon/Law.passive_reading`): the linear
/// reading of the storage effort, and the power drawn, which is zero.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PassiveReading {
    pub value: Vec<Rat>,
    pub power: Rat,
}

/// [definition] **The Holon law.**
pub trait HolonLaw {
    /// The law this motion realizes.
    fn holon(&self) -> &Holon;

    /// One word of motion from `state` under the external efforts `input`, with its balance.
    fn advance(&self, state: &HolonState, input: &[Rat]) -> Result<Advance, HolonError>;

    /// **interconnect**: the law on the whole of the Holarchy that [`Holon::interconnect`] returns
    /// for this law's Holon and another's under a declared gluing; a gluing defect is returned
    /// inside [`HolonError::Gluing`]. Reception between two participants is
    /// [`JointLaw::interact`], which solves a step of such a whole.
    fn interconnect(&self, other: &Self, gluing: &Gluing) -> Result<Self, HolonError>
    where
        Self: Sized;

    /// **receive**: the zero-storage specialization of joint reception
    /// (`Holarchy/Reception.zero_storage_receiver_is_passive_reading`). A receiver at rest that
    /// stores nothing, coupled at the storage efforts by `reader = C`, is joined to this law
    /// ([`JointLaw::reading`]) and one joint step is solved: the source advances by its own law,
    /// the receiver reaches `h C ē_S` at zero power, and the joint balance is the source's own.
    fn receive(
        &self,
        state: &HolonState,
        input: &[Rat],
        reader: &ExactRatMatrix,
        receipt: &ReceiptLaw,
    ) -> Result<InteractionReturn, HolonError>;

    /// **restrict**: the pushforward of the interconnection along a port map
    /// (`Holon/Restriction.pushforwardD_isDirac`).
    fn restrict(&self, map: &PortMap) -> Result<DiracStructure, HolonError> {
        map.pushforward(self.holon().port_holon().dirac())
    }

    /// **pullback**: a coarse effort (covector) returns to the fine ports by `Pᵀ`
    /// (`Holon/Law.pullback_law`).
    fn pullback(&self, map: &PortMap, effort: &[Rat]) -> Result<Vec<Rat>, HolonError> {
        if map.source_ports() != self.holon().port_holon().counts().total() {
            return Err(HolonError::Shape {
                what: "pullback map source ports",
                expected: self.holon().port_holon().counts().total(),
                found: map.source_ports(),
            });
        }
        map.pull_effort(effort)
    }
}

/// [definition] **The exact reference law** over ℚ: the Dirac-form step of [`Holon`] at step `h`
/// under a declared scheme.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReferenceHolon {
    holon: Holon,
    step: Rat,
    scheme: Scheme,
}

impl ReferenceHolon {
    pub fn new(holon: Holon, step: Rat, scheme: Scheme) -> Result<Self, HolonError> {
        if step <= Rat::zero() {
            return Err(HolonError::NonpositiveStep);
        }
        Ok(Self {
            holon,
            step,
            scheme,
        })
    }

    pub fn step(&self) -> &Rat {
        &self.step
    }

    pub fn scheme(&self) -> Scheme {
        self.scheme
    }

    /// **One word at a declared material** `(Q, L)`, then a deposit `Q → Q'`
    /// (`Holon/Deposition.commit_balance`): the returned balance is the word's plus the
    /// deposition work `½⟨x⁺, (Q' − Q) x⁺⟩`, and `stored_change = E(x⁺; Q') − E(x; Q)`.
    pub fn commit(
        &self,
        state: &HolonState,
        input: &[Rat],
        storage: &SymmetricForm,
        active: &ExactRatMatrix,
        deposit: &SymmetricForm,
    ) -> Result<Advance, HolonError> {
        let port_holon = self.holon.port_holon();
        let c = port_holon.counts();
        if storage.extent() != c.storage || deposit.extent() != c.storage {
            return Err(HolonError::Shape {
                what: "committed storage extent",
                expected: c.storage,
                found: storage.extent().max(deposit.extent()),
            });
        }
        if active.rows() != c.active || active.columns() != c.active {
            return Err(HolonError::Shape {
                what: "committed active extent",
                expected: c.active,
                found: active.rows(),
            });
        }
        let x = &state.configuration;
        if x.len() != c.storage {
            return Err(HolonError::Shape {
                what: "state configuration",
                expected: c.storage,
                found: x.len(),
            });
        }
        if input.len() != c.external {
            return Err(HolonError::Shape {
                what: "external input efforts",
                expected: c.external,
                found: input.len(),
            });
        }
        let (sigma, rho, pi, alpha) = (c.storage, c.resistive, c.external, c.active);
        let n = c.total();
        let q = form_matrix(storage);
        let r = port_holon.resistance().resistance();
        let h = &self.step;
        let inverse_step = Rat::one() / h;
        let weight = match self.scheme {
            Scheme::Midpoint => rat(1, 2),
            Scheme::BackwardEuler => Rat::one(),
        };
        // Unknowns z = (x⁺, f_R, f_P, f_A). Step bond: f = A_f z + c_f, e = A_e z + c_e.
        let (xo, ro, po, ao) = (0, sigma, sigma + rho, sigma + rho + pi);
        let flow_coefficient = matrix(n, n, |row, column| {
            if row < sigma {
                if column == xo + row {
                    -inverse_step.clone()
                } else {
                    Rat::zero()
                }
            } else if row == column {
                Rat::one()
            } else {
                Rat::zero()
            }
        })?;
        let effort_coefficient = matrix(n, n, |row, column| {
            if row < sigma && column < sigma {
                &weight * at(&q, row, column)
            } else if (ro..ro + rho).contains(&row) && (ro..ro + rho).contains(&column) {
                -at(r, row - ro, column - ro)
            } else if (ao..ao + alpha).contains(&row) && (ao..ao + alpha).contains(&column) {
                at(active, row - ao, column - ao)
            } else {
                Rat::zero()
            }
        })?;
        let mut flow_constant = crate::ratio::linear::vector::zeros(n);
        let mut effort_constant = crate::ratio::linear::vector::zeros(n);
        let qx = q.apply(x)?;
        for i in 0..sigma {
            flow_constant[i] = &inverse_step * &x[i];
            if self.scheme == Scheme::Midpoint {
                effort_constant[i] = rat(1, 2) * &qx[i];
            }
        }
        effort_constant[po..po + pi].clone_from_slice(input);
        let form = port_holon.dirac().form();
        let f = form.flow_matrix()?;
        let e = form.effort_matrix()?;
        let system = f
            .multiply(&flow_coefficient)?
            .add(&e.multiply(&effort_coefficient)?)?;
        let target = neg(&crate::ratio::linear::vector::add(
            &f.apply(&flow_constant)?,
            &e.apply(&effort_constant)?,
        ));
        let z = match system.preimage_fibre(&target)? {
            None => return Err(HolonError::Inconsistent),
            Some((z, kernel)) if kernel.is_empty() => z,
            Some((_, kernel)) => {
                return Err(HolonError::NotUniquelySolvable {
                    nullity: kernel.len(),
                });
            }
        };
        let flow = crate::ratio::linear::vector::add(&flow_coefficient.apply(&z)?, &flow_constant);
        let effort =
            crate::ratio::linear::vector::add(&effort_coefficient.apply(&z)?, &effort_constant);
        let bond = Bond::new(flow, effort)?;
        if !port_holon.dirac().contains(&bond)? {
            return Err(HolonError::NotAdmitted);
        }
        let x_next: Vec<Rat> = z[xo..xo + sigma].to_vec();
        let resistive_flow = &z[ro..ro + rho];
        let external_flow = &z[po..po + pi];
        let active_flow = &z[ao..ao + alpha];
        let delta = sub(&x_next, x);
        let discretization_defect = match self.scheme {
            Scheme::Midpoint => Rat::zero(),
            Scheme::BackwardEuler => -(rat(1, 2) * quad(&q, &delta)?),
        };
        let deposition_work = storage_energy(deposit, &x_next)? - storage_energy(storage, &x_next)?;
        let balance = EnergyBalance::closed(
            storage_energy(deposit, &x_next)? - storage_energy(storage, x)?,
            h * quad(r, resistive_flow)?,
            h * dot(input, external_flow),
            h * quad(active, active_flow)?,
            deposition_work,
            discretization_defect,
        );
        Ok(Advance {
            state: HolonState {
                configuration: x_next,
                commit: state.commit + 1,
            },
            bond,
            balance,
        })
    }

    /// The step bond split by kind.
    pub fn kinds(&self, advance: &Advance) -> Result<KindBonds, HolonError> {
        self.holon.port_holon().split(&advance.bond)
    }
}

impl HolonLaw for ReferenceHolon {
    fn holon(&self) -> &Holon {
        &self.holon
    }

    /// The word at the material in force; a pumped Holon deposits its next scheduled storage.
    fn advance(&self, state: &HolonState, input: &[Rat]) -> Result<Advance, HolonError> {
        let storage = self.holon.storage_at(state.commit);
        let deposit = self.holon.storage_at(state.commit + 1);
        self.commit(
            state,
            input,
            storage,
            self.holon.active().relation(),
            deposit,
        )
    }

    fn interconnect(&self, other: &Self, gluing: &Gluing) -> Result<Self, HolonError> {
        if self.step != other.step || self.scheme != other.scheme {
            return Err(HolonError::Unsupported {
                what: "joining reference laws",
                reason: "the two laws step at different steps or schemes",
            });
        }
        Self::new(
            self.holon
                .interconnect(&other.holon, gluing)?
                .whole()
                .clone(),
            self.step.clone(),
            self.scheme,
        )
    }

    fn receive(
        &self,
        state: &HolonState,
        input: &[Rat],
        reader: &ExactRatMatrix,
        receipt: &ReceiptLaw,
    ) -> Result<InteractionReturn, HolonError> {
        let sigma = self.holon.port_holon().counts().storage;
        if state.configuration.len() != sigma {
            return Err(HolonError::Shape {
                what: "source configuration",
                expected: sigma,
                found: state.configuration.len(),
            });
        }
        let joint = JointLaw::reading(self, reader)?;
        let mut configuration = state.configuration.clone();
        configuration.extend(crate::ratio::linear::vector::zeros(reader.rows()));
        joint.interact(
            &HolonState::at(configuration, state.commit),
            input,
            &ReceiverFace::receiver_state(sigma, reader.rows())?,
            receipt,
        )
    }
}

/// [definition] **The active receiver interface** (`Holon/Law.active_receiver_law`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActiveReceiverReading {
    /// Power delivered into the Holon side, `⟨e_H, −G Δ⟩`.
    pub holon_power: Rat,
    /// Power delivered into the receiver side, `⟨e_R, G Δ⟩`.
    pub receiver_power: Rat,
    /// `D_Σ = ⟨Δ, G Δ⟩`, `Δ = e_H − e_R`.
    pub dissipation: Rat,
}

/// Join a Holon effort `e_H` and a receiver effort `e_R` through a certified passive interface
/// conductance `G`: `P_H + P_R = −D_Σ` and `D_Σ ≥ 0` (checked, and refused if violated).
pub fn active_receiver(
    conductance: &ResistiveRelation,
    holon_effort: &[Rat],
    receiver_effort: &[Rat],
) -> Result<ActiveReceiverReading, HolonError> {
    let g = conductance.resistance();
    let delta = sub(holon_effort, receiver_effort);
    let current = g.apply(&delta)?;
    let holon_power = dot(&neg(&current), holon_effort);
    let receiver_power = dot(&current, receiver_effort);
    let dissipation = quad(g, &delta)?;
    if &holon_power + &receiver_power != -dissipation.clone() || dissipation < Rat::zero() {
        return Err(HolonError::NotAdmitted);
    }
    Ok(ActiveReceiverReading {
        holon_power,
        receiver_power,
        dissipation,
    })
}
