//! **The population at a port: families whose faces a Holarchy's port reads** (THE_REBUILD U1,
//! "One machine"; the module header of `receiver::population`).
//!
//! [definition; agent-inferred] **The receiving composition at the field's port.** A [`Population`]
//! weighs families that carry their own faces and likelihoods ([`Family`](super::Family)). At the HNN's receiving
//! port the families' faces are the machine's own readings: the landmark tree's executed face `q_T`,
//! read from the tree the constitution holds (its one authoritative update is the constitution's
//! landmark deposit), and the combined face `q_C` (the tree's grain logits plus the wave), read from
//! the field. Neither is a family's private state, so the population at a port carries only what
//! the population itself retains: each family's prior and its likelihood `L_f = ∏_t P_f(x_t)`, never
//! a record of the cells. Its face, its code, its posteriors and its deaths are the population's
//! laws, read through the same telescope and the same outward bounds ([`super::PRECISION`]) as
//! [`Population`]'s:
//!
//! ```text
//! q_t(x) = Σ_f w_f P_f(x),  w_f = π_f L_f / Σ_g π_g L_g           the population's face (Bayes)
//! ∏_(t<n) q_t(x_t) = Σ_f π_f L_f                                  the telescope, read once
//! P_f(x_t) = 0  ⇒  f dies at t                                    exact death, never a floor
//! ```
//!
//! [definition; agent-inferred] **The enclosure contract.** A face read at a port may lie in an
//! algebraic extension: the combined face lives in `ℚ(θ)`, `θ^(L_R) = 2`. So a family's face of a
//! class enters as its exact enclosure `[lo, hi]` (`ratio::algebraic::ExactInterval`), a point where
//! the face is rational (the tree's dyadic executed face). The likelihood is carried as the product
//! of the lower endpoints below and of the upper endpoints above, each kept at the population's
//! precision and rounded outward, so the population's code encloses the true mixture's code exactly
//! (Lean `Compression/Landmark/Context/Population.population_mixture_enclosed`): no rational chart
//! of `q_C`, no carried ratio and no drift. Zero is the only enclosure of an exactly zero face,
//! and it is exact death; a face whose enclosure reaches zero without being zero is not a death
//! (its likelihood's lower bound reads zero until it is decided).
//!
//! [definition; agent-inferred] **The receiver's two families** (`hnn::receiving`): the tree and
//! the combined face at matched priors, one bit of description each, so `π = ½/½` and nothing is
//! reserved. At that prior the population is the sequential mixture (Lean
//! `Compression/Landmark/Context/LocalWeighing.two_face_prior` at `π = ½`: `priorMix (1/2) = seqMix`),
//! stepped cell by cell in the receiver's prequential order, deposits inside a receiving window
//! included. The retired carried ratio `β` of `hnn::receiving::Mixture` (THE_REBUILD U1, history at
//! `19f1eb61`) stepped the same law
//! through a rational chart and a rebase; against it this population's face differs at cell `t` by
//! at most `|Σ_(s<t) log₂ ρ_s|` bits and its passage code by at most `Σ_t |log₂ ρ_t|`, the chart's
//! certified drift (Lean `Population.{executed_face_within_population,
//! executed_mixture_within_population}`).
//!
//! [definition] The computational object is the helical pair interaction read at the receiving port.
//! Of the winding guide's six general objects this owner touches **faces and placement** (each
//! family's face of the received class and the population's weighed face) and the **tube** (the
//! receiving window as a clocked span, its cells received in cell order); the helix, the pair, the
//! cell holonomy and the tower thread stay attached through the families' own owners (the field's
//! word and the landmark tree's address).
//!
//! | Lean | Rust |
//! |---|---|
//! | `Compression/Landmark/Context/Population.{population_mixture, population_mixture_enclosed}` | [`PortPopulation::code`], [`PortPopulation::face_of`] |
//! | `Computation/HolonicAdjointNormalization.{bayes_eq_face, replicator_eq_zero_iff}` | [`PortPopulation::receive`] (death at an exactly zero face) |
//! | `Compression/Landmark/Context/LocalWeighing.two_face_prior` (`π = ½`) | the receiver's two families at matched priors |
//! | `Compression/Landmark/Context/Population.{executed_face_within_population, executed_mixture_within_population}` | the bound against the retired carried ratio (the U1 acceptance) |

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::{
    Bound, Population, PopulationError, Posterior, code_between, kraft, mass_code, refuse, weigh,
    weight_of,
};
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;

/// One family read at the port: its declared description, its normalized prior, its likelihood's
/// outward bounds and the cell it died at.
#[derive(Clone, Debug, PartialEq, Eq)]
struct PortMember {
    description: u64,
    prior: Rat,
    likelihood: (Bound, Bound),
    died: Option<u64>,
}

/// [definition; agent-inferred] **The population at a port** (module header): the declared
/// families' priors and likelihoods, the cells received, and nothing else.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortPopulation {
    members: Vec<PortMember>,
    mass: Rat,
    cells: u64,
}

impl PortPopulation {
    /// **Declare the population** over families of the given descriptions: their Kraft sum
    /// `M = Σ_f 2^(−ℓ_f)` is at most one, the prior is `2^(−ℓ_f)/M` and `1 − M` is reserved.
    /// Refused without a family or past Kraft's sum.
    pub fn new(descriptions: &[u64]) -> Result<Self, PopulationError> {
        if descriptions.is_empty() {
            return Err(refuse(
                "a population at a port",
                "it declares at least one family",
            ));
        }
        let masses = descriptions
            .iter()
            .map(|&description| kraft(description))
            .collect::<Result<Vec<Rat>, _>>()?;
        let mass: Rat = masses.iter().sum();
        if mass > Rat::one() {
            return Err(refuse(
                "a population's descriptions",
                "their Kraft sum passes one: they are no prefix code's lengths",
            ));
        }
        let members = descriptions
            .iter()
            .zip(masses)
            .map(|(&description, weight)| PortMember {
                description,
                prior: weight / &mass,
                likelihood: (Bound::one(), Bound::one()),
                died: None,
            })
            .collect();
        Ok(Self {
            members,
            mass,
            cells: 0,
        })
    }

    /// The declared families.
    pub fn families(&self) -> usize {
        self.members.len()
    }

    /// The cells received.
    pub fn cells(&self) -> u64 {
        self.cells
    }

    /// **The declared total mass** `M = Σ_f 2^(−ℓ_f)`.
    pub fn mass(&self) -> &Rat {
        &self.mass
    }

    /// Family `f`'s declared description `ℓ_f`.
    pub fn description(&self, family: usize) -> Option<u64> {
        self.members.get(family).map(|member| member.description)
    }

    /// Family `f`'s normalized prior `π_f = 2^(−ℓ_f)/M`.
    pub fn prior(&self, family: usize) -> Option<&Rat> {
        self.members.get(family).map(|member| &member.prior)
    }

    /// The cell family `f` died at, if it died.
    pub fn died(&self, family: usize) -> Option<u64> {
        self.members.get(family).and_then(|member| member.died)
    }

    /// Each member's `c_f = π_f L_f` bounds; zero once dead.
    fn charged(&self) -> Vec<(Bound, Bound)> {
        self.members
            .iter()
            .map(|member| {
                if member.died.is_some() {
                    return (Bound::zero(), Bound::zero());
                }
                (
                    Bound::of_rat(&member.prior, false).times(&member.likelihood.0, false),
                    Bound::of_rat(&member.prior, true).times(&member.likelihood.1, true),
                )
            })
            .collect()
    }

    /// `W = Σ_f c_f`'s bounds, refused when every family is dead.
    fn whole(&self, charged: &[(Bound, Bound)]) -> Result<(Bound, Bound), PopulationError> {
        let whole = Population::total(charged, 0..charged.len());
        if whole.0.is_zero() && self.members.iter().all(|member| member.died.is_some()) {
            return Err(PopulationError::Extinct {
                cell: self.cells as usize,
            });
        }
        Ok(whole)
    }

    /// **Admission before anything moves**: one face per declared family, each an enclosure within
    /// the unit interval.
    fn admit(&self, faces: &[ExactInterval]) -> Result<(), PopulationError> {
        if faces.len() != self.members.len() {
            return Err(refuse(
                "the faces read at a port",
                "one face is read for every declared family",
            ));
        }
        if faces
            .iter()
            .any(|face| face.lower.is_negative() || face.upper > Rat::one())
        {
            return Err(refuse(
                "a family's face read at a port",
                "its enclosure lies in the unit interval",
            ));
        }
        Ok(())
    }

    /// The population's face of one class, as outward bounds, from each family's face of it.
    fn face_bounds(&self, faces: &[ExactInterval]) -> Result<(Bound, Bound), PopulationError> {
        self.admit(faces)?;
        let charged = self.charged();
        let whole = self.whole(&charged)?;
        if whole.0.is_zero() {
            return Err(refuse(
                "the population's face at a port",
                "a living family's likelihood bound kept at the precision is positive",
            ));
        }
        let mut sum = (Bound::zero(), Bound::zero());
        for ((member, charged), face) in self.members.iter().zip(&charged).zip(faces) {
            if member.died.is_some() {
                continue;
            }
            weigh(
                &mut sum,
                &weight_of(charged, &whole),
                &(
                    Bound::of_rat(&face.lower, false),
                    Bound::of_rat(&face.upper, true),
                ),
            );
        }
        Ok(sum)
    }

    /// **The population's face of one class** `q(c) = Σ_f w_f P_f(c)` before the next cell, from
    /// each declared family's face of that class (a dead family's is not read), enclosed on the
    /// grid `2^(−P)` (module header).
    pub fn face_of(&self, faces: &[ExactInterval]) -> Result<ExactInterval, PopulationError> {
        let (lower, upper) = self.face_bounds(faces)?;
        Ok(ExactInterval::new(
            lower.to_rat(false),
            upper.to_rat(true).min(Rat::one()),
        )?)
    }

    /// **The code of one class** `−log₂ q(c)` under the population's face, enclosed from the face's
    /// outward bounds (the receiver's scored code of a received cell, read before it is received).
    /// Refused where the face's lower bound is zero: an exactly zero face has no code.
    pub fn code_of(&self, faces: &[ExactInterval]) -> Result<ExactInterval, PopulationError> {
        let (lower, upper) = self.face_bounds(faces)?;
        if lower.is_zero() {
            return Err(refuse(
                "the code of a received class",
                "the population's face of it is positive",
            ));
        }
        code_between(&lower, &upper)
    }

    /// **Receive one cell** (module header): each living family's face of the received class
    /// multiplies its likelihood's bounds; a family whose face is exactly zero dies there, keeping
    /// its likelihood as it died, and its mass passes to the survivors (the telescope's
    /// normalization). Returns the families that died. Refused, with nothing moved, at a face
    /// outside the unit interval and at a cell every living family gives exactly zero.
    pub fn receive(&mut self, faces: &[ExactInterval]) -> Result<Vec<usize>, PopulationError> {
        self.admit(faces)?;
        let dying: Vec<usize> = (0..self.members.len())
            .filter(|&f| self.members[f].died.is_none() && faces[f].upper.is_zero())
            .collect();
        if self
            .members
            .iter()
            .zip(faces)
            .all(|(member, face)| member.died.is_some() || face.upper.is_zero())
        {
            return Err(PopulationError::Extinct {
                cell: self.cells as usize,
            });
        }
        for (f, (member, face)) in self.members.iter_mut().zip(faces).enumerate() {
            if member.died.is_some() {
                continue;
            }
            if dying.contains(&f) {
                member.died = Some(self.cells);
                continue;
            }
            member.likelihood = (
                member
                    .likelihood
                    .0
                    .times(&Bound::of_rat(&face.lower, false), false),
                member
                    .likelihood
                    .1
                    .times(&Bound::of_rat(&face.upper, true), true),
            );
        }
        self.cells += 1;
        Ok(dying)
    }

    /// **The population's code** `−log₂ W = −log₂ Σ_f π_f L_f`, an exact enclosure (the
    /// telescope). Refused when every family is dead.
    pub fn code(&self) -> Result<ExactInterval, PopulationError> {
        let charged = self.charged();
        let (lower, upper) = self.whole(&charged)?;
        if lower.is_zero() {
            return Err(refuse(
                "the population's code at a port",
                "a living family's likelihood bound kept at the precision is positive",
            ));
        }
        code_between(&lower, &upper)
    }

    /// **Family `f`'s code alone** `−log₂ L_f` since the opening, enclosed; none once it died, or
    /// while its likelihood's lower bound reads zero (an undecided face).
    pub fn family_code(&self, family: usize) -> Result<Option<ExactInterval>, PopulationError> {
        let Some(member) = self.members.get(family) else {
            return Err(refuse(
                "a family's code at a port",
                "it names a declared family",
            ));
        };
        if member.died.is_some() || member.likelihood.0.is_zero() {
            return Ok(None);
        }
        Ok(Some(code_between(
            &member.likelihood.0,
            &member.likelihood.1,
        )?))
    }

    /// **Family `f`'s weight** `w_f = π_f L_f / Σ_g π_g L_g` before the next cell, enclosed on the
    /// grid `2^(−P)`; exactly zero once it died.
    pub fn weight(&self, family: usize) -> Result<ExactInterval, PopulationError> {
        let Some(member) = self.members.get(family) else {
            return Err(refuse("a weight at a port", "it names a declared family"));
        };
        if member.died.is_some() {
            return Ok(ExactInterval::point(Rat::zero()));
        }
        let charged = self.charged();
        let (lower, upper) = self.whole(&charged)?;
        if lower.is_zero() {
            return Err(refuse(
                "a weight's enclosure",
                "a living family's likelihood bound kept at the precision is positive",
            ));
        }
        let (weight_lower, weight_upper) = weight_of(&charged[family], &(lower, upper));
        Ok(ExactInterval::new(
            weight_lower.to_rat(false),
            weight_upper.to_rat(true).min(Rat::one()),
        )?)
    }

    /// **Family `f`'s posterior** `−log₂ w_f`, enclosed; `Dead` once it died.
    pub fn posterior(&self, family: usize) -> Result<Posterior, PopulationError> {
        let Some(member) = self.members.get(family) else {
            return Err(refuse(
                "a posterior at a port",
                "it names a declared family",
            ));
        };
        if member.died.is_some() {
            return Ok(Posterior::Dead);
        }
        let charged = self.charged();
        let (lower, upper) = self.whole(&charged)?;
        let (part_lower, part_upper) = &charged[family];
        if lower.is_zero() || part_lower.is_zero() {
            return Err(refuse(
                "a posterior's enclosure",
                "a living family's likelihood bound kept at the precision is positive",
            ));
        }
        Ok(Posterior::Bits(mass_code(
            &part_lower.over(&upper, false),
            &part_upper.over(&lower, true),
        )?))
    }

    /// **Its exact bits**: each family's prior (numerator and denominator) and its likelihood's two
    /// bounds (each mantissa and its exponent with its sign), and the cells received.
    pub fn bits(&self) -> u64 {
        let rat = |x: &Rat| x.numer().bits() + x.denom().bits();
        let bound = |b: &Bound| b.mantissa.bits() + BigInt::from(b.exponent).bits() + 1;
        self.members
            .iter()
            .map(|member| {
                rat(&member.prior) + bound(&member.likelihood.0) + bound(&member.likelihood.1)
            })
            .sum::<u64>()
            + BigInt::from(self.cells).bits().max(1)
    }
}
