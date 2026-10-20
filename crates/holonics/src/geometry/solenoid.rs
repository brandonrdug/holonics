//! **Finite coherent residue towers joined to longitudinal phase and carry.**
//!
//! [definition; implemented-exact] For caller-declared positive moduli `N_i | N_(i+1)`,
//! a chart holds `0 <= s < 1`, compatible residues `z_i` and a signed longitudinal winding `w`.
//! Its circle face is `theta_i = (s + z_i)/N_i` in turns. Advancing by a rational `a` sets
//! `c = floor(s+a)`, `s' = s+a-c`, `z_i' = z_i+c (mod N_i)`, `w' = w+c`.
//! Thus the carry joins the longitudinal passage to the transverse tower. Addition uses the
//! same floor cocycle. The unreduced longitudinal lift `w+s` is retained beside the circle faces.
//!
//! This is a chart of the existing navigator, winding and tower objects, independent of a source
//! modality. It uses [`Tower`] and [`CompatibleSection`] for transverse restrictions; it does not
//! replace the mixed-radix [`super::winding::Odometer`] or the Cayley
//! [`crate::navigator::PhaseLift`]. A rational turn here is **not** a rational Cayley parameter.
//!
//! [proved-standard; implementation bridge owed] Divisibility gives
//! `theta_i = (N_j/N_i)*theta_j (mod 1)` for `i <= j`; the floor cocycle makes advance and addition
//! commute with restriction. Module tests check declared instances, not universal proofs. The
//! existing Lean `Geometry/PhaseCarry` and `Foundation/ContinuingTower` supply the separate laws;
//! a formal proof of this particular join remains owed.
//!
//! [assumption for inverse-limit interpretation] An actual solenoid requires an unbounded
//! compatible family of circle covers. An unbounded divisibility chain with unbounded moduli is
//! further data, never inferred from a finite prefix. Finite residues leave finer transverse
//! fibres unresolved. Only rational longitudinal coordinates are represented here; real-circle
//! completion is additional structure. This module implements neither an infinite object nor a compactness or
//! continuation theorem; [`SolenoidalChart::extend`] checks a supplied finite continuation.
//! Physical identifications of this chart are modeling hypotheses, not consequences of these
//! operators. No physical unification conjecture is asserted as a proved law here.
//!
//! Retention consists only of the current phase, winding and compatible section, never an event
//! archive. Moduli and levels are the caller's finite aperture; no factorization search or
//! arbitrary depth limit is introduced.

pub mod field;
pub mod pump;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};
use thiserror::Error;

use crate::holon::restriction::tower::{CompatibleSection, ResidueTower, Tower, TowerRefusal};
use crate::ratio::Rat;

/// A refused finite chart, with the incompatible operands retained in the refusal.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum SolenoidError {
    #[error("a finite solenoidal chart needs at least one declared modulus")]
    EmptyTower,
    #[error("modulus at level {level} is zero")]
    ZeroModulus { level: usize },
    #[error("modulus {coarse} at level {level} does not divide its successor {fine}")]
    NonDivisible {
        level: usize,
        coarse: BigUint,
        fine: BigUint,
    },
    #[error("the tower has {levels} levels but was supplied {residues} residues")]
    ResidueCount { levels: usize, residues: usize },
    #[error("a rational turn cannot have a zero denominator")]
    ZeroDenominator,
    #[error("the phase {phase} is outside the turn section [0, 1)")]
    PhaseOutsideSection { phase: Rat },
    #[error("level {level} is outside the {levels} declared levels")]
    LevelMissing { level: usize, levels: usize },
    #[error("a restriction must retain between one and {levels} levels, requested {requested}")]
    RestrictionDepth { requested: usize, levels: usize },
    #[error("addition requires the same declared modulus chain")]
    DifferentTowers,
    #[error("a continuation must extend the existing modulus chain as a prefix")]
    NotAnExtension,
    #[error("a continuation changed the retained residue at level {level}")]
    ContinuationDisagrees {
        level: usize,
        retained: BigUint,
        supplied: BigUint,
    },
    #[error(transparent)]
    Tower(#[from] TowerRefusal<usize, BigUint>),
}

/// A finite declared divisibility chain, implementing the existing transverse [`Tower`].
/// Modulus one and repeated moduli are allowed: they are genuine trivial covers.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FiniteSolenoidalTower {
    moduli: Vec<BigUint>,
}

impl FiniteSolenoidalTower {
    /// Check positivity and actual divisibility, without assuming pairwise coprimality.
    pub fn new(moduli: Vec<BigUint>) -> Result<Self, SolenoidError> {
        if moduli.is_empty() {
            return Err(SolenoidError::EmptyTower);
        }
        for (level, modulus) in moduli.iter().enumerate() {
            if modulus.is_zero() {
                return Err(SolenoidError::ZeroModulus { level });
            }
        }
        for (level, adjacent) in moduli.windows(2).enumerate() {
            if !(&adjacent[1] % &adjacent[0]).is_zero() {
                return Err(SolenoidError::NonDivisible {
                    level,
                    coarse: adjacent[0].clone(),
                    fine: adjacent[1].clone(),
                });
            }
        }
        Ok(Self { moduli })
    }

    /// Read explicitly supplied levels through the existing power-tower modulus owner.
    /// The caller owns the cost of these declared powers, as with [`ResidueTower::modulus`].
    /// No prime hypothesis is needed for these finite residue restrictions.
    pub fn from_residue_tower(tower: &ResidueTower, levels: &[u32]) -> Result<Self, SolenoidError> {
        Self::new(levels.iter().map(|level| tower.modulus(*level)).collect())
    }

    pub fn moduli(&self) -> &[BigUint] {
        &self.moduli
    }

    pub fn levels(&self) -> usize {
        self.moduli.len()
    }

    /// The ratio of cover degrees, after checking that both levels belong to this tower.
    pub fn cover_degree(&self, coarse: usize, fine: usize) -> Result<BigUint, SolenoidError> {
        if !self.refines(&coarse, &fine) {
            return Err(TowerRefusal::NotARefinement { coarse, fine }.into());
        }
        Ok(&self.moduli[fine] / &self.moduli[coarse])
    }
}

impl Tower for FiniteSolenoidalTower {
    type Index = usize;
    type Face = BigUint;

    fn refines(&self, coarse: &usize, fine: &usize) -> bool {
        coarse <= fine && *fine < self.levels()
    }

    fn carries(&self, chart: &usize, face: &BigUint) -> bool {
        self.moduli
            .get(*chart)
            .is_some_and(|modulus| face < modulus)
    }

    fn restrict(
        &self,
        coarse: &usize,
        fine: &usize,
        face: &BigUint,
    ) -> Result<BigUint, TowerRefusal<usize, BigUint>> {
        if !self.refines(coarse, fine) {
            return Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            });
        }
        if !self.carries(fine, face) {
            return Err(TowerRefusal::FaceNotCarried {
                chart: *fine,
                face: face.clone(),
            });
        }
        Ok(face % &self.moduli[*coarse])
    }
}

/// The current finite circle-cover chart and the longitudinal lift it carries.
///
/// Equality includes winding. Two states may have equal finite circle faces but different
/// longitudinal lifts; the observation does not erase that difference from retained state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SolenoidalChart {
    tower: FiniteSolenoidalTower,
    phase: Rat,
    winding: BigInt,
    section: CompatibleSection<usize, BigUint>,
}

impl SolenoidalChart {
    /// Admit a normal chart `s, w, (z_i)`, checking every transverse compatibility pair through
    /// the existing owner. Supplied residues are current section coordinates, not a history.
    pub fn new(
        tower: FiniteSolenoidalTower,
        phase: Rat,
        winding: BigInt,
        residues: Vec<BigUint>,
    ) -> Result<Self, SolenoidError> {
        let phase = canonical_rat(&phase)?;
        if phase.is_negative() || phase >= Rat::one() {
            return Err(SolenoidError::PhaseOutsideSection { phase });
        }
        if residues.len() != tower.levels() {
            return Err(SolenoidError::ResidueCount {
                levels: tower.levels(),
                residues: residues.len(),
            });
        }
        let section = CompatibleSection::check(&tower, residues.into_iter().enumerate().collect())?;
        Ok(Self {
            tower,
            phase,
            winding,
            section,
        })
    }

    /// Start at a coherent transversal and advance by an unreduced rational longitudinal lift.
    /// Integer turns shift the transversal by their signed carry. Negative passage is supported.
    pub fn from_transverse(
        tower: FiniteSolenoidalTower,
        longitudinal: Rat,
        transverse_residues: Vec<BigUint>,
    ) -> Result<Self, SolenoidError> {
        Self::new(tower, Rat::zero(), BigInt::zero(), transverse_residues)?.advance(&longitudinal)
    }

    pub fn tower(&self) -> &FiniteSolenoidalTower {
        &self.tower
    }

    pub fn phase(&self) -> &Rat {
        &self.phase
    }

    /// Signed crossings of the base circle section, including negative crossings.
    pub fn winding(&self) -> &BigInt {
        &self.winding
    }

    /// The unreduced longitudinal lift, distinct from any finite circle observation.
    pub fn longitudinal_lift(&self) -> Rat {
        &self.phase + Rat::from_integer(self.winding.clone())
    }

    pub fn section(&self) -> &CompatibleSection<usize, BigUint> {
        &self.section
    }

    pub fn residue(&self, level: usize) -> Result<&BigUint, SolenoidError> {
        self.section
            .witness(&level)
            .ok_or(SolenoidError::LevelMissing {
                level,
                levels: self.tower.levels(),
            })
    }

    /// The opening transversal class `z_i-w (mod N_i)`. This is constant along a longitudinal
    /// leaf under [`Self::advance`], and is finite current data, not a stored opening event.
    pub fn transverse_residue(&self, level: usize) -> Result<BigUint, SolenoidError> {
        let residue = self.residue(level)?;
        Ok(signed_residue(
            &(BigInt::from(residue.clone()) - &self.winding),
            &self.tower.moduli[level],
        ))
    }

    /// The canonical rational turn face `(s+z_i)/N_i` of the circle cover at this level.
    /// This is an exact angle in turns; no trigonometric or floating approximation is formed.
    pub fn circle_turn(&self, level: usize) -> Result<Rat, SolenoidError> {
        let residue = self.residue(level)?;
        Ok(
            (&self.phase + Rat::from_integer(BigInt::from(residue.clone())))
                / Rat::from_integer(BigInt::from(self.tower.moduli[level].clone())),
        )
    }

    /// Advance the current leaf by `delta`, retaining only its current section and total carry.
    /// Composition is exact: `advance(a).advance(b) = advance(a+b)`.
    pub fn advance(&self, delta: &Rat) -> Result<Self, SolenoidError> {
        let total = &self.phase + canonical_rat(delta)?;
        let (phase, carry) = split_turn(&total);
        let residues = self
            .tower
            .moduli
            .iter()
            .enumerate()
            .map(|(level, modulus)| {
                Ok(signed_residue(
                    &(BigInt::from(self.residue(level)?.clone()) + &carry),
                    modulus,
                ))
            })
            .collect::<Result<Vec<_>, SolenoidError>>()?;
        Self::new(self.tower.clone(), phase, &self.winding + carry, residues)
    }

    /// Add two charts with their floor carry. Longitudinal winding is added with that same carry;
    /// it is never reconstructed from a finite residue face.
    pub fn add(&self, other: &Self) -> Result<Self, SolenoidError> {
        if self.tower != other.tower {
            return Err(SolenoidError::DifferentTowers);
        }
        let (phase, carry) = split_turn(&(&self.phase + &other.phase));
        let residues = self
            .tower
            .moduli
            .iter()
            .enumerate()
            .map(|(level, modulus)| {
                Ok(signed_residue(
                    &(BigInt::from(self.residue(level)?.clone())
                        + BigInt::from(other.residue(level)?.clone())
                        + &carry),
                    modulus,
                ))
            })
            .collect::<Result<Vec<_>, SolenoidError>>()?;
        Self::new(
            self.tower.clone(),
            phase,
            &self.winding + &other.winding + carry,
            residues,
        )
    }

    /// Additive inverse, including the negative section crossing when `s > 0`.
    pub fn inverse(&self) -> Result<Self, SolenoidError> {
        let (phase, carry) = split_turn(&(-&self.phase));
        let residues = self
            .tower
            .moduli
            .iter()
            .enumerate()
            .map(|(level, modulus)| {
                Ok(signed_residue(
                    &(-BigInt::from(self.residue(level)?.clone()) + &carry),
                    modulus,
                ))
            })
            .collect::<Result<Vec<_>, SolenoidError>>()?;
        Self::new(self.tower.clone(), phase, -&self.winding + carry, residues)
    }

    /// Retain a nonempty prefix of the tower. The longitudinal lift is unchanged; only the
    /// transverse aperture narrows. This commutes with [`Self::add`] and [`Self::advance`].
    pub fn restrict(&self, levels: usize) -> Result<Self, SolenoidError> {
        if levels == 0 || levels > self.tower.levels() {
            return Err(SolenoidError::RestrictionDepth {
                requested: levels,
                levels: self.tower.levels(),
            });
        }
        let tower = FiniteSolenoidalTower::new(self.tower.moduli[..levels].to_vec())?;
        let residues = (0..levels)
            .map(|level| self.residue(level).cloned())
            .collect::<Result<Vec<_>, _>>()?;
        Self::new(tower, self.phase.clone(), self.winding.clone(), residues)
    }

    /// Check a supplied coherent finite continuation. Existing chart restrictions must agree
    /// exactly; a finer residue is not guessed or recovered from the current coarse face.
    pub fn extend(
        &self,
        tower: FiniteSolenoidalTower,
        residues: Vec<BigUint>,
    ) -> Result<Self, SolenoidError> {
        if !tower.moduli.starts_with(&self.tower.moduli) {
            return Err(SolenoidError::NotAnExtension);
        }
        let extended = Self::new(tower, self.phase.clone(), self.winding.clone(), residues)?;
        for level in 0..self.tower.levels() {
            let retained = self.residue(level)?;
            let supplied = extended.residue(level)?;
            if retained != supplied {
                return Err(SolenoidError::ContinuationDisagrees {
                    level,
                    retained: retained.clone(),
                    supplied: supplied.clone(),
                });
            }
        }
        Ok(extended)
    }
}

fn canonical_rat(value: &Rat) -> Result<Rat, SolenoidError> {
    if value.denom().is_zero() {
        return Err(SolenoidError::ZeroDenominator);
    }
    Ok(Rat::new(value.numer().clone(), value.denom().clone()))
}

// Euclidean floor, rather than BigInt's truncation toward zero, is essential on negative leaves.
fn split_turn(value: &Rat) -> (Rat, BigInt) {
    let mut whole = value.numer() / value.denom();
    if (value.numer() % value.denom()).is_negative() {
        whole -= BigInt::one();
    }
    (value - Rat::from_integer(whole.clone()), whole)
}

fn signed_residue(value: &BigInt, modulus: &BigUint) -> BigUint {
    let modulus = BigInt::from(modulus.clone());
    let mut residue = value % &modulus;
    if residue.is_negative() {
        residue += modulus;
    }
    residue.magnitude().clone()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::holon::restriction::tower::check_restriction_laws;
    use crate::ratio::{integer, rat};

    fn naturals(values: &[u32]) -> Vec<BigUint> {
        values.iter().copied().map(BigUint::from).collect()
    }

    fn tower() -> FiniteSolenoidalTower {
        FiniteSolenoidalTower::new(naturals(&[1, 4, 12, 60])).unwrap()
    }

    fn point(longitudinal: Rat) -> SolenoidalChart {
        SolenoidalChart::from_transverse(tower(), longitudinal, naturals(&[0, 3, 11, 59])).unwrap()
    }

    fn fractional(value: Rat) -> Rat {
        split_turn(&value).0
    }

    #[test]
    fn signed_leaf_motion_carries_into_every_transverse_level() {
        let opening = point(rat(17, 6));
        assert_eq!(opening.phase(), &rat(5, 6));
        assert_eq!(opening.winding(), &BigInt::from(2));
        for level in 1..opening.tower().levels() {
            assert_eq!(opening.residue(level).unwrap(), &BigUint::one());
        }
        let crossed = opening.advance(&rat(1, 3)).unwrap();
        assert_eq!(crossed.phase(), &rat(1, 6));
        assert_eq!(crossed.winding(), &BigInt::from(3));
        assert_eq!(crossed.residue(3).unwrap(), &BigUint::from(2u32));
        let reversed = opening.advance(&rat(-31, 6)).unwrap();
        assert_eq!(reversed.longitudinal_lift(), rat(-7, 3));
        assert_eq!(reversed.phase(), &rat(2, 3));
        assert_eq!(reversed.winding(), &BigInt::from(-3));
        assert_eq!(reversed.residue(1).unwrap(), &BigUint::zero());
        assert_eq!(reversed.residue(2).unwrap(), &BigUint::from(8u32));
        assert_eq!(reversed.residue(3).unwrap(), &BigUint::from(56u32));
        for level in 0..opening.tower().levels() {
            assert_eq!(
                opening.transverse_residue(level),
                crossed.transverse_residue(level)
            );
            assert_eq!(
                opening.transverse_residue(level),
                reversed.transverse_residue(level)
            );
        }
        assert_eq!(crossed.advance(&rat(-1, 3)).unwrap(), opening);
    }

    #[test]
    fn finite_cover_faces_restrict_by_the_actual_degree() {
        let tower = tower();
        let chart = point(rat(-7, 5));
        let charts: Vec<_> = (0..tower.levels()).collect();
        let faces: Vec<_> = charts
            .iter()
            .map(|level| (*level, chart.residue(*level).unwrap().clone()))
            .collect();
        check_restriction_laws(&tower, &charts, &faces).unwrap();
        for coarse in 0..tower.levels() {
            for fine in coarse..tower.levels() {
                let degree =
                    Rat::from_integer(BigInt::from(tower.cover_degree(coarse, fine).unwrap()));
                assert_eq!(
                    chart.circle_turn(coarse).unwrap(),
                    fractional(degree * chart.circle_turn(fine).unwrap())
                );
            }
        }
        assert_eq!(tower.cover_degree(1, 3).unwrap(), BigUint::from(15u32));
        assert!(tower.restrict(&2, &1, &BigUint::one()).is_err());
        assert!(tower.cover_degree(0, 4).is_err());
        assert!(!tower.refines(&4, &4));
    }

    #[test]
    fn group_laws_and_leaf_action_keep_the_same_floor_cocycle() {
        let identity =
            SolenoidalChart::from_transverse(tower(), Rat::zero(), naturals(&[0, 0, 0, 0]))
                .unwrap();
        let b = SolenoidalChart::from_transverse(tower(), rat(-13, 7), naturals(&[0, 2, 10, 34]))
            .unwrap();
        let c = point(rat(11, 3));
        for numerator in -9..=9 {
            let a = point(rat(numerator, 5));
            assert_eq!(a.add(&identity).unwrap(), a);
            assert_eq!(a.add(&a.inverse().unwrap()).unwrap(), identity);
            assert_eq!(a.add(&b).unwrap(), b.add(&a).unwrap());
            assert_eq!(
                a.add(&b).unwrap().add(&c).unwrap(),
                a.add(&b.add(&c).unwrap()).unwrap()
            );
            assert_eq!(
                a.advance(&rat(-19, 6))
                    .unwrap()
                    .advance(&rat(17, 4))
                    .unwrap(),
                a.advance(&(rat(-19, 6) + rat(17, 4))).unwrap()
            );
            assert_eq!(
                a.add(&b).unwrap().longitudinal_lift(),
                a.longitudinal_lift() + b.longitudinal_lift()
            );
            for level in 0..tower().levels() {
                assert_eq!(
                    a.add(&b).unwrap().circle_turn(level).unwrap(),
                    fractional(a.circle_turn(level).unwrap() + b.circle_turn(level).unwrap())
                );
            }
        }
    }

    #[test]
    fn advance_addition_and_inverse_commute_with_finite_restriction() {
        let a = point(rat(17, 6));
        let b = point(rat(-23, 9));
        for levels in 1..=tower().levels() {
            let restricted = a.restrict(levels).unwrap();
            assert_eq!(restricted.longitudinal_lift(), a.longitudinal_lift());
            assert_eq!(
                a.advance(&rat(-1001, 7)).unwrap().restrict(levels).unwrap(),
                restricted.advance(&rat(-1001, 7)).unwrap()
            );
            assert_eq!(
                a.add(&b).unwrap().restrict(levels).unwrap(),
                restricted.add(&b.restrict(levels).unwrap()).unwrap()
            );
            assert_eq!(
                a.inverse().unwrap().restrict(levels).unwrap(),
                restricted.inverse().unwrap()
            );
            for shallower in 1..=levels {
                assert_eq!(
                    restricted.restrict(shallower).unwrap(),
                    a.restrict(shallower).unwrap()
                );
            }
        }
    }

    #[test]
    fn a_finite_face_does_not_erase_winding_or_choose_a_finer_branch() {
        let opening = point(rat(1, 3));
        let after_full_cover = opening.advance(&integer(60)).unwrap();
        assert_ne!(opening, after_full_cover);
        assert_eq!(
            after_full_cover.winding() - opening.winding(),
            BigInt::from(60)
        );
        for level in 0..tower().levels() {
            assert_eq!(
                opening.circle_turn(level),
                after_full_cover.circle_turn(level)
            );
        }

        let coarse = SolenoidalChart::new(
            FiniteSolenoidalTower::new(naturals(&[4])).unwrap(),
            rat(1, 3),
            BigInt::from(7),
            naturals(&[1]),
        )
        .unwrap();
        let fine = FiniteSolenoidalTower::new(naturals(&[4, 12])).unwrap();
        let first = coarse.extend(fine.clone(), naturals(&[1, 1])).unwrap();
        let second = coarse.extend(fine.clone(), naturals(&[1, 5])).unwrap();
        assert_ne!(
            first.circle_turn(1).unwrap(),
            second.circle_turn(1).unwrap()
        );
        assert_eq!(first.restrict(1).unwrap(), coarse);
        assert_eq!(second.restrict(1).unwrap(), coarse);
        assert!(matches!(
            coarse.extend(fine.clone(), naturals(&[1, 2])),
            Err(SolenoidError::Tower(
                TowerRefusal::IncompatibleWitness { .. }
            ))
        ));
        assert!(matches!(
            coarse.extend(fine, naturals(&[2, 2])),
            Err(SolenoidError::ContinuationDisagrees { level: 0, .. })
        ));
        assert!(matches!(
            coarse.extend(tower(), naturals(&[0, 1, 1, 1])),
            Err(SolenoidError::NotAnExtension)
        ));
    }

    #[test]
    fn malformed_inputs_refuse_instead_of_repairing_the_declared_tower() {
        assert_eq!(
            FiniteSolenoidalTower::new(vec![]),
            Err(SolenoidError::EmptyTower)
        );
        assert!(matches!(
            FiniteSolenoidalTower::new(naturals(&[1, 0])),
            Err(SolenoidError::ZeroModulus { level: 1 })
        ));
        assert!(matches!(
            FiniteSolenoidalTower::new(naturals(&[7, 11, 33])),
            Err(SolenoidError::NonDivisible { level: 0, .. })
        ));
        assert!(matches!(
            SolenoidalChart::new(tower(), rat(1, 2), BigInt::zero(), naturals(&[0])),
            Err(SolenoidError::ResidueCount { .. })
        ));
        assert!(matches!(
            SolenoidalChart::new(tower(), integer(1), BigInt::zero(), naturals(&[0, 0, 0, 0])),
            Err(SolenoidError::PhaseOutsideSection { .. })
        ));
        assert!(matches!(
            SolenoidalChart::new(
                tower(),
                Rat::zero(),
                BigInt::zero(),
                naturals(&[0, 4, 4, 4])
            ),
            Err(SolenoidError::Tower(TowerRefusal::FaceNotCarried {
                chart: 1,
                ..
            }))
        ));
        let a = point(rat(2, 3));
        assert_eq!(
            a.advance(&Rat::new_raw(BigInt::one(), BigInt::zero())),
            Err(SolenoidError::ZeroDenominator)
        );
        assert_eq!(
            a.advance(&Rat::new_raw((-1).into(), (-2).into())),
            a.advance(&rat(1, 2))
        );
        assert!(a.residue(4).is_err());
        assert!(a.circle_turn(4).is_err());
        assert!(a.restrict(0).is_err());
        assert!(a.restrict(5).is_err());
        assert_eq!(
            a.add(&a.restrict(1).unwrap()),
            Err(SolenoidError::DifferentTowers)
        );
    }

    #[test]
    fn an_existing_residue_tower_supplies_its_actual_declared_moduli() {
        let existing = ResidueTower::new(BigUint::from(3u32)).unwrap();
        let finite = FiniteSolenoidalTower::from_residue_tower(&existing, &[0, 1, 3]).unwrap();
        assert_eq!(finite.moduli(), naturals(&[1, 3, 27]));
        assert_eq!(finite.cover_degree(1, 2).unwrap(), BigUint::from(9u32));
        let chart =
            SolenoidalChart::from_transverse(finite, rat(7, 4), naturals(&[0, 2, 20])).unwrap();
        assert_eq!(chart.residue(1).unwrap(), &BigUint::zero());
        assert_eq!(chart.residue(2).unwrap(), &BigUint::from(21u32));
        assert_eq!(
            existing
                .restrict(&1, &3, chart.residue(2).unwrap())
                .unwrap(),
            chart.residue(1).unwrap().clone()
        );
        assert!(FiniteSolenoidalTower::from_residue_tower(&existing, &[2, 1]).is_err());
    }
}
