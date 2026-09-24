//! **The complex parametron: the ring that stores, oscillates and locks.**
//!
//! [definition] The ring is an oriented incidence `B` (branches × nodes) with two diagonal
//! constitutive weights on its branches: capacities `W_C` and inverse inductances `W_K`
//! ([objects §5](../../../../docs/ELEMENTARY_OBJECTS.md#5-parametron)). In the node-flux chart
//!
//! ```text
//! C = Bᵀ W_C B        K = Bᵀ W_K B        a mode:  K v = ω² C v
//! x(θ) = cos θ · v    ẋ = −ω sin θ · v
//! ½⟨ẋ, C ẋ⟩ + ½⟨x, K x⟩ = ω² sin²θ · ½⟨v, C v⟩ + cos²θ · ½⟨v, K v⟩ = ω² · ½⟨v, C v⟩
//! ```
//!
//! Storage and flow exchange along a mode while the mode energy is conserved. Only `ω²` enters,
//! so the exchange is exact: for the single LC ring `ω² = 1/(LC)` is carried as a ratio and no
//! root is taken. The phase is read in the Cayley chart of the circle, so `cos θ` and `sin θ` are
//! rational.
//!
//! The ring's phase carrier is `e^{iθ}`. A pump couples to the doubled phase,
//! `−p cos(2θ − ψ)`, and so cannot tell the two **half-turn sheets** `θ` and `θ + π` apart; the
//! half-turn `e^{iπ} = −1` negates the carrier. On the locked sheets the coupling
//! `−w cos(θ_i − θ_j)` is exactly the Ising pairing `−w σ_i σ_j`, and a drive `h_i` couples to a
//! reference carrier at phase `0`. The energy-minimizing sheet of a site is the threshold
//! `sign(Σ_j w_ij σ_j + h_i)`: **a perceptron is one receiver face of a coupled parametron
//! population**. A ring stepping `1/d` of a turn crosses its section `(r + N)/d` times in `N`
//! micro-steps from residue `r < d`; each crossing is a clock tick.
//!
//! [open] Pump/Floquet locking (that the pump selects the two sheets as attracting basins) is not
//! proved; the locked sheets are taken as given.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Objects/Parametron.modeEnergy_conserved`, `modeEnergy_exchange` (node-flux chart; the charge-chart `lc_energy_conserved` is its one-ring dual) | [`Parametron::mode_energy`] |
//! | `Physics/CoupledIncidence.diagonalStorage`, `diagonalResponse`, `IsGeneralizedMode` | [`Parametron::storage`], [`Parametron::is_mode`] |
//! | `Objects/Parametron.modeWitness` | tests |
//! | `Physics/PhaseCarrier.pumpStorage`, `pumpStorage_halfTurnSheet`, `phaseCarrier_halfTurnSheet` | [`pump_storage`], [`Carrier::half_turn`] |
//! | `Physics/PhaseCarrier.phaseCoupling`, `isingCoupling`, `phaseNetworkEnergy_binaryPhase` | [`Population::phase_energy`], [`Population::ising_energy`] |
//! | `Objects/Parametron.drivenIsing_update`, `thresholdSheet_minimizes`, `perceptron_is_a_face` | [`Population::local_field`], [`threshold_sheet`] |
//! | `Objects/Parametron.globalHalfTurn_composite`, `drive_breaks_halfTurn` | tests |
//! | `Objects/Parametron.ringCrossings_eq`, `no_crossing_of_denominator_one` | [`ring_crossings`] |

use num_bigint::BigUint;
use num_traits::{One, Signed, Zero};
use thiserror::Error;

use crate::geometry::rational_circle;
use crate::geometry::screw::RationalPhase;
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};
use crate::ratio::{Rat, integer};

/// Every refusal of a parametron. Bad input is a typed return, never a panic.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum ParametronError {
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("a constitutive weight must be nonnegative, found {weight}")]
    NegativeWeight { weight: Rat },
    #[error("an LC ring needs a positive inductance and capacitance")]
    NonpositiveElement,
    #[error("({cos}, {sin}) is not a point of the unit circle")]
    NotOnCircle { cos: Rat, sin: Rat },
    #[error("site {site} lies outside a population of {sites}")]
    SiteOutside { site: usize, sites: usize },
    #[error("an edge joins site {site} to itself")]
    SelfLoop { site: usize },
    #[error("a ring residue {residue} must lie below its denominator {denominator}")]
    ResidueOutside {
        residue: BigUint,
        denominator: BigUint,
    },
}

// -------------------------------------------------------------------------------------------
// the ring: storage and flow

/// **The ring**: oriented incidence with capacity and inverse-inductance weights on its branches.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Parametron {
    incidence: ExactRatMatrix,
    capacity: Vec<Rat>,
    stiffness: Vec<Rat>,
}

/// The two exchanging energies of a mode at one phase.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModeEnergy {
    /// `½⟨ẋ, C ẋ⟩`, the capacitive storage of the node velocity.
    pub capacitive: Rat,
    /// `½⟨x, K x⟩`, the inductive energy of the node flux.
    pub inductive: Rat,
}

impl ModeEnergy {
    pub fn total(&self) -> Rat {
        &self.capacitive + &self.inductive
    }
}

impl Parametron {
    /// A ring on `incidence` (branches × nodes) with one capacity and one inverse inductance per
    /// branch, each nonnegative.
    pub fn new(
        incidence: ExactRatMatrix,
        capacity: Vec<Rat>,
        stiffness: Vec<Rat>,
    ) -> Result<Self, ParametronError> {
        for weights in [&capacity, &stiffness] {
            if weights.len() != incidence.rows() {
                return Err(ParametronError::Shape {
                    what: "branch weights",
                    expected: incidence.rows(),
                    found: weights.len(),
                });
            }
            if let Some(weight) = weights.iter().find(|weight| weight.is_negative()) {
                return Err(ParametronError::NegativeWeight {
                    weight: weight.clone(),
                });
            }
        }
        Ok(Self {
            incidence,
            capacity,
            stiffness,
        })
    }

    /// **The LC ring**: one branch on one node, capacity `C` and inverse inductance `1/L`, whose
    /// single mode has `ω² = 1/(LC)`.
    pub fn lc(inductance: &Rat, capacitance: &Rat) -> Result<Self, ParametronError> {
        if !inductance.is_positive() || !capacitance.is_positive() {
            return Err(ParametronError::NonpositiveElement);
        }
        Self::new(
            ExactRatMatrix::identity(1)?,
            vec![capacitance.clone()],
            vec![inductance.recip()],
        )
    }

    pub fn nodes(&self) -> usize {
        self.incidence.columns()
    }

    fn weighted(&self, weights: &[Rat]) -> Result<ExactRatMatrix, ParametronError> {
        let diagonal = ExactRatMatrix::from_diagonal(weights.to_vec())?;
        Ok(self
            .incidence
            .transpose()?
            .multiply(&diagonal)?
            .multiply(&self.incidence)?)
    }

    /// `C = Bᵀ W_C B`.
    pub fn capacitance(&self) -> Result<ExactRatMatrix, ParametronError> {
        self.weighted(&self.capacity)
    }

    /// `K = Bᵀ W_K B`.
    pub fn stiffness(&self) -> Result<ExactRatMatrix, ParametronError> {
        self.weighted(&self.stiffness)
    }

    /// The diagonal storage `½ Σ_b W_b (B v)_b²` of a node state under branch weights.
    pub fn storage(&self, weights: &[Rat], state: &[Rat]) -> Result<Rat, ParametronError> {
        let drops = self.incidence.apply(state)?;
        Ok(weights
            .iter()
            .zip(&drops)
            .map(|(weight, drop)| weight * drop * drop)
            .sum::<Rat>()
            / integer(2))
    }

    /// **A generalized mode**: `v ≠ 0` with `K v = ω² C v`.
    pub fn is_mode(&self, omega_squared: &Rat, state: &[Rat]) -> Result<bool, ParametronError> {
        if state.iter().all(Zero::is_zero) {
            return Ok(false);
        }
        let stiff = self.stiffness()?.apply(state)?;
        let capacitive = self.capacitance()?.apply(state)?;
        Ok(stiff
            .iter()
            .zip(&capacitive)
            .all(|(k, c)| k == &(omega_squared * c)))
    }

    /// **The two energies along `x(θ) = cos θ · v`** at a phase read in the Cayley chart:
    /// `½⟨ẋ, C ẋ⟩ = ω² sin²θ · ½⟨v, C v⟩` and `½⟨x, K x⟩ = cos²θ · ½⟨v, K v⟩`.
    pub fn mode_energy(
        &self,
        omega_squared: &Rat,
        state: &[Rat],
        phase: &RationalPhase,
    ) -> Result<ModeEnergy, ParametronError> {
        let (cos, sin) = phase.chart();
        Ok(ModeEnergy {
            capacitive: omega_squared * &sin * &sin * self.storage(&self.capacity, state)?,
            inductive: &cos * &cos * self.storage(&self.stiffness, state)?,
        })
    }

    pub fn capacity(&self) -> &[Rat] {
        &self.capacity
    }

    pub fn inverse_inductance(&self) -> &[Rat] {
        &self.stiffness
    }
}

// -------------------------------------------------------------------------------------------
// the carrier, the pump and the half-turn sheets

/// **The phase carrier** `e^{iθ}` as a rational point `(cos θ, sin θ)` of the unit circle.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Carrier {
    cos: Rat,
    sin: Rat,
}

impl Carrier {
    pub fn new(cos: Rat, sin: Rat) -> Result<Self, ParametronError> {
        if &cos * &cos + &sin * &sin != Rat::one() {
            return Err(ParametronError::NotOnCircle { cos, sin });
        }
        Ok(Self { cos, sin })
    }

    /// The carrier at a Cayley half-angle parameter.
    pub fn at(parameter: &Rat) -> Self {
        let (cos, sin) = rational_circle(parameter);
        Self { cos, sin }
    }

    /// **A locked sheet**: `false` is the zero-phase sheet (`+1`), `true` the half-turn sheet
    /// (`−1`).
    pub fn sheet(half_turn: bool) -> Self {
        Self {
            cos: integer(if half_turn { -1 } else { 1 }),
            sin: Rat::zero(),
        }
    }

    /// **The half-turn** `e^{iπ} · e^{iθ} = −e^{iθ}`.
    pub fn half_turn(&self) -> Self {
        Self {
            cos: -&self.cos,
            sin: -&self.sin,
        }
    }

    pub fn cos(&self) -> &Rat {
        &self.cos
    }

    pub fn sin(&self) -> &Rat {
        &self.sin
    }

    /// `cos(θ − φ)` between two carriers.
    pub fn cos_between(&self, other: &Self) -> Rat {
        &self.cos * &other.cos + &self.sin * &other.sin
    }

    /// The sheet reading: the half-turn sheet exactly when `cos θ < 0`.
    pub fn sheet_reading(&self) -> bool {
        self.cos.is_negative()
    }
}

/// **The pump storage** `−p cos(2θ − ψ)`: it reads the doubled phase, so it cannot tell the two
/// half-turn sheets apart.
pub fn pump_storage(strength: &Rat, pump: &Carrier, carrier: &Carrier) -> Rat {
    let doubled_cos = &carrier.cos * &carrier.cos - &carrier.sin * &carrier.sin;
    let doubled_sin = integer(2) * &carrier.cos * &carrier.sin;
    -strength * (doubled_cos * &pump.cos + doubled_sin * &pump.sin)
}

/// The spin face of a locked sheet: `+1` on the zero sheet, `−1` on the half-turn sheet.
pub fn spin(half_turn: bool) -> Rat {
    integer(if half_turn { -1 } else { 1 })
}

/// **The threshold unit**: the half-turn sheet exactly when the field is negative.
pub fn threshold_sheet(field: &Rat) -> bool {
    field.is_negative()
}

// -------------------------------------------------------------------------------------------
// a coupled population

/// **A coupled parametron population**: weighted edges between sites and a drive per site.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Population {
    sites: usize,
    edges: Vec<(usize, usize, Rat)>,
    drive: Vec<Rat>,
}

impl Population {
    /// A population without self-loops; every edge joins two sites of the population.
    pub fn new(edges: Vec<(usize, usize, Rat)>, drive: Vec<Rat>) -> Result<Self, ParametronError> {
        let sites = drive.len();
        for (first, second, _) in &edges {
            for site in [*first, *second] {
                if site >= sites {
                    return Err(ParametronError::SiteOutside { site, sites });
                }
            }
            if first == second {
                return Err(ParametronError::SelfLoop { site: *first });
            }
        }
        Ok(Self {
            sites,
            edges,
            drive,
        })
    }

    fn check(&self, length: usize) -> Result<(), ParametronError> {
        if length == self.sites {
            Ok(())
        } else {
            Err(ParametronError::Shape {
                what: "population state",
                expected: self.sites,
                found: length,
            })
        }
    }

    /// **The driven phase energy** `Σ −w cos(θ_i − θ_j) + Σ −h_i cos θ_i`, the drive coupling each
    /// site to a reference carrier at phase `0`.
    pub fn phase_energy(&self, carriers: &[Carrier]) -> Result<Rat, ParametronError> {
        self.check(carriers.len())?;
        let coupling: Rat = self
            .edges
            .iter()
            .map(|(i, j, weight)| -(weight * carriers[*i].cos_between(&carriers[*j])))
            .sum();
        let driven: Rat = self
            .drive
            .iter()
            .zip(carriers)
            .map(|(h, carrier)| -(h * &carrier.cos))
            .sum();
        Ok(coupling + driven)
    }

    /// **The driven Ising energy** `Σ −w σ_i σ_j + Σ −h_i σ_i` on locked sheets.
    pub fn ising_energy(&self, state: &[bool]) -> Result<Rat, ParametronError> {
        self.check(state.len())?;
        let coupling: Rat = self
            .edges
            .iter()
            .map(|(i, j, weight)| -(weight * spin(state[*i]) * spin(state[*j])))
            .sum();
        let driven: Rat = self
            .drive
            .iter()
            .zip(state)
            .map(|(h, sheet)| -(h * spin(*sheet)))
            .sum();
        Ok(coupling + driven)
    }

    /// **The local field** `Σ_j w_ij σ_j + h_i` at one site.
    pub fn local_field(&self, state: &[bool], site: usize) -> Result<Rat, ParametronError> {
        self.check(state.len())?;
        if site >= self.sites {
            return Err(ParametronError::SiteOutside {
                site,
                sites: self.sites,
            });
        }
        let coupled: Rat = self
            .edges
            .iter()
            .map(|(i, j, weight)| {
                if *i == site {
                    weight * spin(state[*j])
                } else if *j == site {
                    weight * spin(state[*i])
                } else {
                    Rat::zero()
                }
            })
            .sum();
        Ok(coupled + &self.drive[site])
    }

    /// **The perceptron face**: the threshold sheet of a site's local field.
    pub fn perceptron(&self, state: &[bool], site: usize) -> Result<bool, ParametronError> {
        Ok(threshold_sheet(&self.local_field(state, site)?))
    }
}

// -------------------------------------------------------------------------------------------
// the tick

/// **Section crossings of a ring** stepping `1/d` of a turn: `N` micro-steps from residue `r < d`
/// cross the section `(r + N)/d` times, each crossing one clock tick. A ring of one step is always
/// on its section, so no step leaves it and it never crosses.
pub fn ring_crossings(
    denominator: &BigUint,
    residue: &BigUint,
    micro_steps: &BigUint,
) -> Result<BigUint, ParametronError> {
    if residue >= denominator {
        return Err(ParametronError::ResidueOutside {
            residue: residue.clone(),
            denominator: denominator.clone(),
        });
    }
    if denominator.is_one() {
        return Ok(BigUint::zero());
    }
    Ok((residue + micro_steps) / denominator)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geometry::winding::Odometer;
    use crate::ratio::rat;

    fn phases() -> Vec<RationalPhase> {
        [integer(0), rat(1, 2), integer(1), integer(3), rat(-2, 7)]
            .into_iter()
            .map(|t| RationalPhase::new(t, 0))
            .collect()
    }

    /// Lean `Objects/Parametron.modeEnergy_conserved` and `modeEnergy_exchange` at one branch and
    /// one node: with `ω² = 1/(LC)` carried as a ratio, the LC ring's storage and flow exchange at
    /// every rational phase while their sum stays `ω²·½⟨v, C v⟩ = A²/(2L)`, and each term vanishes
    /// where the other carries the whole energy. This is the node-flux chart (`C` on `ẋ`, `1/L` on
    /// `x`). `lc_energy_conserved` states the same exchange in the charge chart `q = C ẋ`, whose
    /// amplitude `CωA` gives the same total `(CωA)²/(2C) = A²/(2L)`; the test checks that duality.
    #[test]
    fn the_lc_ring_exchanges_storage_and_flow_at_constant_energy() {
        let (inductance, capacitance) = (integer(2), rat(1, 8));
        let ring = Parametron::lc(&inductance, &capacitance).unwrap();
        let omega_squared = (&inductance * &capacitance).recip();
        assert_eq!(omega_squared, integer(4));
        let amplitude = vec![rat(3, 2)];
        assert!(ring.is_mode(&omega_squared, &amplitude).unwrap());
        let expected = &amplitude[0] * &amplitude[0] / (integer(2) * &inductance);
        let charge_amplitude = &capacitance * &amplitude[0];
        assert_eq!(
            &charge_amplitude * &charge_amplitude * &omega_squared / (integer(2) * &capacitance),
            expected
        );
        for phase in phases() {
            let energy = ring
                .mode_energy(&omega_squared, &amplitude, &phase)
                .unwrap();
            assert_eq!(energy.total(), expected);
        }
        let rest = ring
            .mode_energy(
                &omega_squared,
                &amplitude,
                &RationalPhase::new(integer(0), 0),
            )
            .unwrap();
        assert!(rest.capacitive.is_zero() && rest.inductive == expected);
        let quarter = ring
            .mode_energy(
                &omega_squared,
                &amplitude,
                &RationalPhase::new(integer(1), 0),
            )
            .unwrap();
        assert!(quarter.inductive.is_zero() && quarter.capacitive == expected);
    }

    /// Lean `Objects/Parametron.modeWitness`, `modeEnergy_conserved`: on the chain
    /// `ground–0–1–ground`, `(1, −1)` is a mode at `ω² = 3` and `(1, 1)` one at `ω² = 1`, `K` is
    /// not a multiple of `C`, and each mode's energy is `ω² · ½⟨v, C v⟩` at every phase.
    #[test]
    fn generalized_modes_conserve_their_energy_on_the_chain() {
        let incidence = ExactRatMatrix::new(vec![
            vec![integer(1), integer(0)],
            vec![integer(-1), integer(1)],
            vec![integer(0), integer(1)],
        ])
        .unwrap();
        let ring = Parametron::new(
            incidence,
            vec![integer(1), integer(0), integer(1)],
            vec![integer(1), integer(1), integer(1)],
        )
        .unwrap();
        assert_ne!(ring.stiffness().unwrap(), ring.capacitance().unwrap());
        for (omega_squared, mode) in [
            (integer(3), vec![integer(1), integer(-1)]),
            (integer(1), vec![integer(1), integer(1)]),
        ] {
            assert!(ring.is_mode(&omega_squared, &mode).unwrap());
            assert!(!ring.is_mode(&(&omega_squared + integer(1)), &mode).unwrap());
            let conserved = &omega_squared * ring.storage(ring.capacity(), &mode).unwrap();
            for phase in phases() {
                assert_eq!(
                    ring.mode_energy(&omega_squared, &mode, &phase)
                        .unwrap()
                        .total(),
                    conserved
                );
            }
        }
    }

    /// Lean `pumpStorage_halfTurnSheet`, `phaseCarrier_halfTurnSheet`, `globalHalfTurn_composite`,
    /// `drive_breaks_halfTurn`: the pump reads the doubled phase and cannot tell the sheets apart,
    /// a global half-turn negates every carrier and keeps every coupling energy, and a drive breaks
    /// that symmetry.
    #[test]
    fn the_half_turn_negates_carriers_and_only_a_drive_sees_it() {
        let pump = Carrier::at(&rat(2, 3));
        let carriers = vec![
            Carrier::at(&rat(1, 5)),
            Carrier::at(&rat(-3, 4)),
            Carrier::at(&integer(2)),
        ];
        for carrier in &carriers {
            let turned = carrier.half_turn();
            assert_eq!(
                pump_storage(&rat(5, 2), &pump, &turned),
                pump_storage(&rat(5, 2), &pump, carrier)
            );
            assert_eq!(
                (turned.cos(), turned.sin()),
                (&-carrier.cos(), &-carrier.sin())
            );
        }
        let turned: Vec<Carrier> = carriers.iter().map(Carrier::half_turn).collect();
        let edges = vec![(0, 1, rat(3, 2)), (1, 2, integer(-1)), (0, 2, integer(2))];
        let free = Population::new(edges.clone(), vec![Rat::zero(); 3]).unwrap();
        assert_eq!(
            free.phase_energy(&turned).unwrap(),
            free.phase_energy(&carriers).unwrap()
        );
        let driven = Population::new(edges, vec![integer(1), Rat::zero(), Rat::zero()]).unwrap();
        assert_ne!(
            driven.phase_energy(&turned).unwrap(),
            driven.phase_energy(&carriers).unwrap()
        );
        assert!(Carrier::new(integer(1), integer(1)).is_err());
    }

    /// Lean `phaseNetworkEnergy_binaryPhase`, `drivenIsing_update`, `thresholdSheet_minimizes`,
    /// `perceptron_is_a_face`: on the locked sheets the driven phase energy is the driven Ising
    /// energy, and the threshold of a site's local field is the sheet of least energy given its
    /// neighbours: the perceptron is that face.
    #[test]
    fn locked_sheets_are_ising_and_the_threshold_sheet_minimizes() {
        let population = Population::new(
            vec![(0, 1, rat(3, 2)), (1, 2, integer(-2)), (0, 2, rat(1, 3))],
            vec![rat(-1, 2), integer(1), Rat::zero()],
        )
        .unwrap();
        for word in 0u8..8 {
            let state: Vec<bool> = (0..3).map(|bit| word >> bit & 1 == 1).collect();
            let carriers: Vec<Carrier> = state.iter().map(|sheet| Carrier::sheet(*sheet)).collect();
            assert_eq!(
                population.phase_energy(&carriers).unwrap(),
                population.ising_energy(&state).unwrap()
            );
            assert!(
                carriers
                    .iter()
                    .zip(&state)
                    .all(|(c, s)| c.sheet_reading() == *s)
            );
            for site in 0..3 {
                let chosen = population.perceptron(&state, site).unwrap();
                let energy = |sheet: bool| {
                    let mut moved = state.clone();
                    moved[site] = sheet;
                    population.ising_energy(&moved).unwrap()
                };
                assert!(energy(chosen) <= energy(!chosen));
            }
        }
        assert!(Population::new(vec![(1, 1, integer(1))], vec![Rat::zero(); 2]).is_err());
    }

    /// Lean `ringCrossings_eq`, `no_crossing_of_denominator_one`: `N` micro-steps of `1/d` from
    /// residue `r < d` cross the section `(r + N)/d` times, the carries of the ring's odometer.
    #[test]
    fn ring_crossings_are_the_odometer_carries() {
        for d in 2u32..6 {
            for r in 0..d {
                for n in 0u32..17 {
                    let (d, r, n) = (BigUint::from(d), BigUint::from(r), BigUint::from(n));
                    let mut ring = Odometer::with_digits(vec![d.clone()], vec![r.clone()]).unwrap();
                    ring.advance(&n);
                    assert_eq!(
                        &ring_crossings(&d, &r, &n).unwrap(),
                        ring.overflow_winding()
                    );
                }
            }
        }
        assert_eq!(
            ring_crossings(&BigUint::one(), &BigUint::zero(), &BigUint::from(9u32)).unwrap(),
            BigUint::zero()
        );
    }
}
