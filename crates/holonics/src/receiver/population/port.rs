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
//! stepped cell by cell in the receiver's prequential order, deposits inside a receiving epoch
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
//! receiving epoch as a clocked span, its cells received in cell order); the helix, the pair, the
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

/// One family face in two reads of the same frozen population window.
/// `Shared` asserts expression identity, not merely equal enclosure endpoints.
/// The producing comparison owner must establish that identity. This numerical
/// type alone does not authenticate a read or authorize material publication.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ComparedFace {
    Shared(ExactInterval),
    Changed {
        before: ExactInterval,
        after: ExactInterval,
    },
}

impl ComparedFace {
    fn before(&self) -> &ExactInterval {
        match self {
            Self::Shared(face) | Self::Changed { before: face, .. } => face,
        }
    }
    fn after(&self) -> &ExactInterval {
        match self {
            Self::Shared(face) | Self::Changed { after: face, .. } => face,
        }
    }
}

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

/// [definition; agent-inferred, October 4; the reception carry §9] **A population's retained
/// reading** ([`PortPopulation::reading`]): each family's likelihood bounds `m·2^e` and the cell it
/// died at, and the cells received.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortReading {
    members: Vec<((Bound, Bound), Option<u64>)>,
    cells: u64,
}

impl PortReading {
    /// **The reading as text**, every value exact: `population F cells`, then one line a family,
    /// `lower-mantissa lower-exponent upper-mantissa upper-exponent died` (`-` for a living family).
    pub fn write(&self, s: &mut String) {
        *s += &format!("population {} {}\n", self.members.len(), self.cells);
        for ((lo, hi), died) in &self.members {
            let died = died.map_or_else(|| "-".to_string(), |cell| cell.to_string());
            *s += &format!(
                "{} {} {} {} {died}\n",
                lo.mantissa, lo.exponent, hi.mantissa, hi.exponent
            );
        }
    }

    /// **The reading read from its text** ([`PortReading::write`]), refused with what was out of
    /// its form; its fit to a declaration is checked where it is placed
    /// ([`PortPopulation::with_reading`]).
    pub fn read<'t>(lines: &mut impl Iterator<Item = &'t str>) -> Result<Self, &'static str> {
        let what = "a saved population";
        let head: Vec<u64> = lines
            .next()
            .and_then(|line| line.strip_prefix("population "))
            .ok_or(what)?
            .split_whitespace()
            .map(|word| word.parse().map_err(|_| what))
            .collect::<Result<_, _>>()?;
        let [families, cells] = head[..] else {
            return Err(what);
        };
        let families = usize::try_from(families).map_err(|_| what)?;
        let mut members = Vec::with_capacity(families);
        for _ in 0..families {
            let words: Vec<&str> = lines.next().ok_or(what)?.split_whitespace().collect();
            let [lo_m, lo_e, hi_m, hi_e, died] = words[..] else {
                return Err(what);
            };
            let bound = |m: &str, e: &str| -> Result<Bound, &'static str> {
                Ok(Bound {
                    mantissa: m.parse().map_err(|_| what)?,
                    exponent: e.parse().map_err(|_| what)?,
                })
            };
            let died = match died {
                "-" => None,
                cell => Some(cell.parse().map_err(|_| what)?),
            };
            members.push(((bound(lo_m, lo_e)?, bound(hi_m, hi_e)?), died));
        }
        Ok(Self { members, cells })
    }
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

    /// [definition; agent-inferred, October 4; the reception carry §9] **The population at its
    /// founding**: its declared families' priors, every likelihood `1`, none dead, no cell received.
    pub fn founding(&self) -> Self {
        Self {
            members: self
                .members
                .iter()
                .map(|member| PortMember {
                    likelihood: (Bound::one(), Bound::one()),
                    died: None,
                    ..member.clone()
                })
                .collect(),
            mass: self.mass.clone(),
            cells: 0,
        }
    }

    /// [definition; agent-inferred, October 4; the reception carry §9] **What the population
    /// retains past its declaration** ([`PortReading`]): each family's likelihood bounds and the cell
    /// it died at, and the cells received. A saved state carries it whole; the declared priors stay
    /// with the declared opening.
    pub fn reading(&self) -> PortReading {
        PortReading {
            members: self
                .members
                .iter()
                .map(|member| (member.likelihood.clone(), member.died))
                .collect(),
            cells: self.cells,
        }
    }

    /// **The population with a saved reading placed on its declaration**: refused where the
    /// reading has another family count, a bound past the kept precision, or a death after the
    /// cells received.
    pub fn with_reading(&self, reading: &PortReading) -> Result<Self, PopulationError> {
        if reading.members.len() != self.members.len() {
            return Err(refuse(
                "a saved population's reading",
                "it reads one likelihood for every declared family",
            ));
        }
        if reading.members.iter().any(|((lo, hi), died)| {
            lo.mantissa.bits() > super::PRECISION
                || hi.mantissa.bits() > super::PRECISION
                || died.is_some_and(|cell| cell >= reading.cells)
        }) {
            return Err(refuse(
                "a saved population's reading",
                "its bounds are kept at the precision and its deaths precede the cells received",
            ));
        }
        Ok(Self {
            members: self
                .members
                .iter()
                .zip(&reading.members)
                .map(|(member, (likelihood, died))| PortMember {
                    likelihood: likelihood.clone(),
                    died: *died,
                    ..member.clone()
                })
                .collect(),
            mass: self.mass.clone(),
            cells: reading.cells,
        })
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

    /// Living retained likelihoods that are intervals rather than exact points.
    /// More arithmetic precision cannot recover the evidence discarded into these
    /// intervals. Correlated comparisons can nevertheless cancel shared uncertainty.
    pub fn retained_interval_members(&self) -> usize {
        self.members
            .iter()
            .filter(|member| member.died.is_none() && member.likelihood.0 != member.likelihood.1)
            .count()
    }

    /// The same retained likelihood bounds, on one common relative scale. This
    /// avoids materializing an exponentially small history and avoids introducing
    /// the fixed Bound arithmetic grid into a higher-precision transient read.
    fn scaled_charged_at(&self, bits: u32) -> Result<Vec<ExactInterval>, PopulationError> {
        let extent = || {
            refuse(
                "population precision",
                "relative bound exponents fit their exact carrier",
            )
        };
        let common = self
            .members
            .iter()
            .filter(|member| member.died.is_none())
            .filter(|member| !member.likelihood.1.is_zero())
            .map(|member| {
                member
                    .likelihood
                    .1
                    .exponent
                    .checked_add(
                        i64::try_from(member.likelihood.1.mantissa.bits()).map_err(|_| extent())?,
                    )
                    .ok_or_else(extent)
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .max()
            .ok_or(PopulationError::Extinct {
                cell: self.cells as usize,
            })?;
        let read = |bound: &Bound, up: bool| -> Result<Rat, PopulationError> {
            let shift = bound
                .exponent
                .checked_sub(common)
                .and_then(|shift| shift.checked_add(i64::from(bits)))
                .ok_or_else(extent)?;
            let numerator = if shift >= 0 {
                &bound.mantissa << usize::try_from(shift).map_err(|_| extent())?
            } else {
                let right = shift.unsigned_abs();
                let (mut numerator, discarded) = if right >= bound.mantissa.bits() {
                    (num_bigint::BigUint::zero(), !bound.is_zero())
                } else {
                    let right = usize::try_from(right).map_err(|_| extent())?;
                    let numerator = &bound.mantissa >> right;
                    let discarded = (&numerator << right) != bound.mantissa;
                    (numerator, discarded)
                };
                if up && discarded {
                    numerator += 1u32;
                }
                numerator
            };
            Ok(Rat::new(
                BigInt::from(numerator),
                BigInt::one() << bits as usize,
            ))
        };
        self.members
            .iter()
            .map(|member| {
                if member.died.is_some() {
                    return Ok(ExactInterval::point(Rat::zero()));
                }
                Ok(ExactInterval::new(
                    read(&member.likelihood.0, false)? * &member.prior,
                    read(&member.likelihood.1, true)? * &member.prior,
                )?)
            })
            .collect()
    }

    /// Read the same population mixture at a requested arithmetic precision.
    /// Retained likelihood intervals remain unchanged; this is not new evidence.
    pub fn face_of_at(
        &self,
        faces: &[ExactInterval],
        bits: u32,
    ) -> Result<ExactInterval, PopulationError> {
        self.admit(faces)?;
        let charged = self.scaled_charged_at(bits)?;
        let mut numerator = ExactInterval::point(Rat::zero());
        let mut denominator = ExactInterval::point(Rat::zero());
        for (charge, face) in charged.iter().zip(faces) {
            let product = charge.times(face)?;
            numerator.lower += product.lower;
            numerator.upper += product.upper;
            denominator.lower += &charge.lower;
            denominator.upper += &charge.upper;
        }
        if !denominator.lower.is_positive() {
            return Err(refuse(
                "population precision",
                "a living retained lower likelihood is positive at the requested precision",
            ));
        }
        Ok(ExactInterval::new(
            &numerator.lower / &denominator.upper,
            (&numerator.upper / &denominator.lower).min(Rat::one()),
        )?
        .round_out(bits)?)
    }

    /// Code for the same mixture using requested-precision logarithms. This may
    /// remain an interval even as bits increases because history is interval-valued.
    pub fn code_of_at(
        &self,
        faces: &[ExactInterval],
        bits: u32,
    ) -> Result<ExactInterval, PopulationError> {
        let face = self.face_of_at(faces, bits)?;
        if !face.lower.is_positive() {
            return Err(refuse(
                "the code of a received class",
                "the population's face of it is positive",
            ));
        }
        let log = crate::ratio::algebraic::log2_of_enclosure_at(&face, bits)?;
        Ok(ExactInterval::new(-log.upper, -log.lower)?)
    }

    /// Enclose `code(after) - code(before)` for one frozen population window.
    /// Rows are successive phases, columns are declared families. The population
    /// is not advanced. Its common normalization cancels in the likelihood ratio;
    /// explicitly shared factors cancel in the product difference. Every retained
    /// likelihood interval remains present, including its correlations with itself.
    /// This can certify a change hidden by independently enclosed absolute scores.
    pub fn code_change_at(
        &self,
        window: &[Vec<ComparedFace>],
        bits: u32,
    ) -> Result<ExactInterval, PopulationError> {
        for row in window {
            self.admit(
                &row.iter()
                    .map(|face| face.before().clone())
                    .collect::<Vec<_>>(),
            )?;
            self.admit(
                &row.iter()
                    .map(|face| face.after().clone())
                    .collect::<Vec<_>>(),
            )?;
        }
        if window.is_empty() {
            return Ok(ExactInterval::point(Rat::zero()));
        }
        let charges = self.scaled_charged_at(bits)?;
        let mut before_sum = ExactInterval::point(Rat::zero());
        let mut after_sum = ExactInterval::point(Rat::zero());
        let mut difference = ExactInterval::point(Rat::zero());
        let add = |sum: &mut ExactInterval, value: ExactInterval| {
            sum.lower += value.lower;
            sum.upper += value.upper;
        };
        for (family, charge) in charges.iter().enumerate() {
            let mut before = ExactInterval::point(Rat::one());
            let mut after = ExactInterval::point(Rat::one());
            let mut delta = ExactInterval::point(Rat::zero());
            // Inductively A' - B' = (A-B)*b + A*(a-b). A shared
            // factor has exactly zero difference even if its enclosure is wide.
            for row in window {
                let face = &row[family];
                let mut next_delta = delta.times(face.before())?;
                if let ComparedFace::Changed {
                    before,
                    after: next,
                } = face
                {
                    let change = ExactInterval::new(
                        &next.lower - &before.upper,
                        &next.upper - &before.lower,
                    )?;
                    add(&mut next_delta, after.times(&change)?);
                }
                delta = next_delta;
                before = before.times(face.before())?;
                after = after.times(face.after())?;
            }
            add(&mut before_sum, charge.times(&before)?);
            add(&mut after_sum, charge.times(&after)?);
            add(&mut difference, charge.times(&delta)?);
        }
        if !before_sum.lower.is_positive() {
            return Err(refuse(
                "a frozen population comparison",
                "the baseline window likelihood has a positive lower bound",
            ));
        }
        let reciprocal = ExactInterval::new(before_sum.upper.recip(), before_sum.lower.recip())?;
        let delta_ratio = difference.times(&reciprocal)?;
        let ordinary_ratio = after_sum.times(&reciprocal)?;
        let ratio = ExactInterval::new(
            (Rat::one() + delta_ratio.lower).max(ordinary_ratio.lower),
            (Rat::one() + delta_ratio.upper).min(ordinary_ratio.upper),
        )?;
        if !ratio.lower.is_positive() {
            return Err(refuse(
                "a frozen population comparison",
                "the candidate likelihood ratio has a positive lower bound",
            ));
        }
        let log = crate::ratio::algebraic::log2_of_enclosure_at(&ratio, bits)?;
        Ok(ExactInterval::new(-log.upper, -log.lower)?)
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

    /// Full immutable diagnostic payload extent, without cloning its retained reading.
    /// Unlike physical `bits`, this includes descriptions, deaths, mass and metadata.
    /// The pair counts integer magnitude/sign bits and conservative structural items.
    pub(crate) fn diagnostic_extent(&self) -> Option<(u64, u64)> {
        let rat = |x: &Rat| {
            x.numer()
                .bits()
                .checked_add(x.denom().bits())?
                .checked_add(2)
        };
        let mut bits = rat(&self.mass)?.checked_add(128)?;
        for member in &self.members {
            bits = bits
                .checked_add(rat(&member.prior)?)?
                .checked_add(member.likelihood.0.mantissa.bits())?
                .checked_add(member.likelihood.1.mantissa.bits())?
                // Both signed exponents, description, optional death and flags.
                .checked_add(320)?;
        }
        Some((
            bits,
            u64::try_from(self.members.len())
                .ok()?
                .checked_mul(16)?
                .checked_add(8)?,
        ))
    }
}

#[cfg(test)]
mod precision_tests {
    use super::*;

    #[test]
    fn population_precision_refines_arithmetic_without_refounding_history() {
        let population = PortPopulation::new(&[1, 1]).unwrap();
        let half = Rat::new(BigInt::one(), BigInt::from(2));
        let epsilon = Rat::new(BigInt::one(), BigInt::one() << 160usize);
        let before = vec![ExactInterval::point(half.clone()); 2];
        let after = vec![before[0].clone(), ExactInterval::point(&half + epsilon)];
        let low = population.code_of_at(&after, 96).unwrap();
        let high = population.code_of_at(&after, 256).unwrap();
        assert!(low.lower <= Rat::one() && low.upper >= Rat::one());
        assert!(high.upper < Rat::one());
        assert!(high.lower >= low.lower && high.upper <= low.upper);
        assert_eq!(population.retained_interval_members(), 0);
        assert_eq!(
            population.code_of_at(&before, 256).unwrap(),
            ExactInterval::point(Rat::one())
        );
    }

    #[test]
    fn population_precision_correlated_change_preserves_shared_history() {
        let mut population = PortPopulation::new(&[1, 1]).unwrap();
        let q = |n: i64, d: i64| Rat::new(BigInt::from(n), BigInt::from(d));
        population
            .receive(&[
                ExactInterval::new(q(1, 4), q(3, 4)).unwrap(),
                ExactInterval::new(q(1, 3), q(2, 3)).unwrap(),
            ])
            .unwrap();
        let shared = ExactInterval::new(q(1, 4), q(3, 4)).unwrap();
        let epsilon = Rat::new(BigInt::one(), BigInt::one() << 160usize);
        let before = ExactInterval::point(q(1, 2));
        let after = ExactInterval::point(q(1, 2) + epsilon);
        let original = population.clone();
        let absolute_before = population
            .code_of_at(&[shared.clone(), before.clone()], 256)
            .unwrap();
        let absolute_after = population
            .code_of_at(&[shared.clone(), after.clone()], 256)
            .unwrap();
        assert!(absolute_after.upper >= absolute_before.lower);
        let window = vec![vec![
            ComparedFace::Shared(shared.clone()),
            ComparedFace::Changed {
                before: before.clone(),
                after: after.clone(),
            },
        ]];
        let refined = population.code_change_at(&window, 256).unwrap();
        assert!(refined.upper < Rat::zero());
        assert!(population.code_change_at(&window, 96).unwrap().upper >= Rat::zero());
        let equal = vec![vec![
            ComparedFace::Shared(shared.clone()),
            ComparedFace::Shared(before.clone()),
        ]];
        assert_eq!(
            population.code_change_at(&equal, 256).unwrap(),
            ExactInterval::point(Rat::zero())
        );
        // Identical interval endpoints do not assert the same expression.
        let unshared = vec![vec![
            ComparedFace::Changed {
                before: shared.clone(),
                after: shared,
            },
            ComparedFace::Shared(before),
        ]];
        let uncertain = population.code_change_at(&unshared, 256).unwrap();
        assert!(uncertain.lower < Rat::zero() && uncertain.upper > Rat::zero());
        // A two-phase telescope agrees with an exact endpoint realization.
        let two = vec![window[0].clone(), window[0].clone()];
        let change = population.code_change_at(&two, 256).unwrap();
        assert!(change.upper < Rat::zero());
        for tree_charge in [q(1, 4), q(3, 4)] {
            for combined_charge in [q(1, 3), q(2, 3)] {
                for tree_face in [q(1, 4), q(3, 4)] {
                    let tree = &tree_charge * &tree_face * &tree_face;
                    let numerator = &tree + &combined_charge * &after.lower * &after.lower;
                    let denominator = &tree + &combined_charge * q(1, 2) * q(1, 2);
                    let exact =
                        crate::ratio::algebraic::log2_enclosure_at(&(numerator / denominator), 384)
                            .unwrap();
                    assert!(change.lower <= -&exact.upper && change.upper >= -&exact.lower);
                }
            }
        }
        assert_eq!(population, original);
    }

    #[test]
    fn population_precision_keeps_retained_interval_uncertainty_visible() {
        let mut population = PortPopulation::new(&[1, 1]).unwrap();
        let half = Rat::new(BigInt::one(), BigInt::from(2));
        population
            .receive(&[
                ExactInterval::point(half),
                ExactInterval::new(
                    Rat::new(BigInt::one(), BigInt::from(4)),
                    Rat::new(BigInt::from(3), BigInt::from(4)),
                )
                .unwrap(),
            ])
            .unwrap();
        let saved = population.clone();
        let faces = vec![
            ExactInterval::point(Rat::new(BigInt::one(), BigInt::from(4))),
            ExactInterval::point(Rat::new(BigInt::from(3), BigInt::from(4))),
        ];
        let reading = population.code_of_at(&faces, 256).unwrap();
        assert!(!reading.is_point());
        assert!(population.retained_interval_members() > 0);
        assert_eq!(population, saved);
    }
}
