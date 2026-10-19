//! **Pair-contact and parametron readings in a declared common chart.**
//!
//! This is an operational join, not another contact, storage or fluid law. The owners are
//! `holon::contact::{PairContact, ContactMaterial}` and `holon::parametron`. Rational phase
//! closure belongs to `geometry::solenoid`; fluid divergence and pressure belong to
//! `physics::fluid::control_volume`. None of those meanings of closure implies another.
//!
//! Epistemic contract:
//! - [proved-derived; formal-checked] `Holonics.Zeta.ZeroPairLock.reflectedPairPower_eq`,
//!   `reflected_pair_locked_iff_on_seam`, and `locked_iff_foster_inductance_positive` prove the
//!   rational reflected-pair algebra, with the last theorem requiring `γ ≠ 0`.
//!   `Holonics.Zeta.FosterTanks.{inductance_pos_real_iff,tank_eq_parallel_LC}` own the tank algebra.
//!   These references describe existing Lean declarations; this Rust module is not a Lean proof.
//! - [runtime-checked] Constructors enforce the material, LC and chart hypotheses exactly;
//!   contact kernels, local sheet energies and rational impedance are executable readings.
//!   The positive-real impedance reading below additionally checks `Re(s) > 0` at each call.
//! - [physical-model hypothesis] Interpreting the supplied coordinates as a source's zeros,
//!   matching a measured constitution to this LC mode, or supplying locked sheets requires
//!   evidence from that source. No such evidence is accepted or manufactured here.
//! - [open] No zero-location theorem, RH, continuum fluid equivalence, universal locking tongue,
//!   persistent kinematic lock or dynamical sheet stability follows from these readings.
//!
//! [agent-inferred] Reuse the constitutive owners and expose their distinct kernels. This avoids
//! September 29 lesson 3 (carrying a located defect into a consumer), and October 9 lessons
//! 12–14 (a fixture or detached feature replacing the requested capability). In particular a
//! semidefinite material's zero power is never promoted to no slip.

use num_traits::{One, Signed, Zero};
use thiserror::Error;

pub mod flow;

use crate::geometry::RatVec3;
use crate::geometry::screw::{RationalPhase, ScrewGenerator, ScrewPair, SituatedScrew};
use crate::holon::contact::{ContactError, ContactMaterial, PairContact};
use crate::holon::parametron::{
    ModeEnergy, Parametron, ParametronError, Population, threshold_sheet,
};
use crate::holon::port::Bond;
use crate::ratio::linear::ExactLinearError;
use crate::ratio::linear::inertia::{InertiaError, SymmetricForm};
use crate::ratio::{GaussianError, GaussianRat, Rat, integer, rat};

/// Refusals retain the hypothesis that did not hold.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum SolenoidalError {
    #[error(transparent)]
    Contact(#[from] ContactError),
    #[error(transparent)]
    Parametron(#[from] ParametronError),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Inertia(#[from] InertiaError),
    #[error(transparent)]
    Gaussian(#[from] GaussianError),
    #[error("a positive Foster tank requires a nonzero angular coordinate")]
    ZeroAngularCoordinate,
    #[error("a positive Foster tank requires advance 1/2; declared advance is {sigma}")]
    OffSeam { sigma: Rat },
    #[error("the impedance chart requires Re(s) > 0; declared real part is {real}")]
    OutsideRightHalfPlane { real: Rat },
    #[error("the declared operands did not satisfy the exact certificate identity")]
    CertificateMismatch,
}

/// The two kernels and the current reading, kept separate even at zero power.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactReading {
    pub slip: RatVec3,
    pub dissipated_power: Rat,
    /// Actual rate-port return: flow `Ju`, effort `-wDJu`, power `-dissipated_power`.
    pub bond: Bond,
    /// Instantaneous `J u = 0`; at `u = 0` this is rest, not a declared rate ratio.
    pub no_slip: bool,
    pub zero_power: bool,
    /// The owner's rank certificate `rank(w D J) = rank(J)`.
    pub definite_on_slips: bool,
    pub no_slip_kernel: Vec<Vec<Rat>>,
    pub zero_power_kernel: Vec<Vec<Rat>>,
}

impl ContactReading {
    /// Read the existing material on the pair, at the supplied rate and retained configuration.
    /// No claim about the subsequent trajectory is made.
    pub fn at(
        contact: &PairContact,
        material: &ContactMaterial,
        rates: &[Rat; 2],
    ) -> Result<Self, SolenoidalError> {
        let slip_map = contact.slip()?;
        let slip = contact.relative_velocity(rates);
        let dissipated_power = material.power(&slip_map, rates)?;
        let bond = material.bond(&slip_map, rates)?;
        if bond.power() != -&dissipated_power {
            return Err(SolenoidalError::CertificateMismatch);
        }
        Ok(Self {
            no_slip: slip == RatVec3::zero(),
            zero_power: dissipated_power.is_zero(),
            definite_on_slips: material.definite_on_slips(&slip_map)?,
            no_slip_kernel: slip_map.kernel_basis()?,
            zero_power_kernel: material.zero_power_kernel(&slip_map)?,
            slip,
            dissipated_power,
            bond,
        })
    }
}

/// A positive single LC mode, consumed through the existing parametron owner.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LcMode {
    inductance: Rat,
    capacitance: Rat,
    omega_squared: Rat,
    ring: Parametron,
}

impl LcMode {
    pub fn new(inductance: Rat, capacitance: Rat) -> Result<Self, SolenoidalError> {
        let ring = Parametron::lc(&inductance, &capacitance)?;
        let omega_squared = (inductance.clone() * &capacitance).recip();
        if !ring.is_mode(&omega_squared, &[Rat::one()])? {
            return Err(SolenoidalError::CertificateMismatch);
        }
        Ok(Self {
            inductance,
            capacitance,
            omega_squared,
            ring,
        })
    }

    pub fn inductance(&self) -> &Rat {
        &self.inductance
    }
    pub fn capacitance(&self) -> &Rat {
        &self.capacitance
    }
    pub fn omega_squared(&self) -> &Rat {
        &self.omega_squared
    }
    pub fn ring(&self) -> &Parametron {
        &self.ring
    }

    /// Unit-amplitude node-flux mode; the existing owner computes both exchanging energies.
    pub fn energy(&self, phase: &RationalPhase) -> Result<ModeEnergy, SolenoidalError> {
        Ok(self
            .ring
            .mode_energy(&self.omega_squared, &[Rat::one()], phase)?)
    }
}

/// A local energy comparison on sheets **supplied** to the existing population. It does not
/// certify that physical motion reaches or stays on those sheets.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalSheetReading {
    pub field: Rat,
    pub half_turn: bool,
    pub tied: bool,
    pub energy_before: Rat,
    pub energy_after: Rat,
}

pub fn local_sheet(
    population: &Population,
    sheets: &[bool],
    site: usize,
) -> Result<LocalSheetReading, SolenoidalError> {
    let field = population.local_field(sheets, site)?;
    let half_turn = threshold_sheet(&field);
    let mut moved = sheets.to_vec();
    // local_field has already checked the site's extent and the complete sheet chart.
    moved[site] = half_turn;
    Ok(LocalSheetReading {
        tied: field.is_zero(),
        field,
        half_turn,
        energy_before: population.ising_energy(sheets)?,
        energy_after: population.ising_energy(&moved)?,
    })
}

/// Declared rational coordinates `(σ, γ)`, not a certified zero of any function.
/// The actual z-axis screws at `(1,0,0)` have velocities `(0,γ,σ)` and `(0,γ,1−σ)`.
/// This permutes Lean's `(σ,γ,0)` chart orthogonally and preserves its isotropic power.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReflectedPair {
    sigma: Rat,
    gamma: Rat,
    contact: PairContact,
    material: ContactMaterial,
}

impl ReflectedPair {
    pub fn new(sigma: Rat, gamma: Rat) -> Result<Self, SolenoidalError> {
        let situated = |advance: Rat| {
            SituatedScrew::new(
                ScrewGenerator::new(
                    RatVec3::new(Rat::zero(), Rat::zero(), gamma.clone()),
                    RatVec3::new(Rat::zero(), Rat::zero(), advance),
                ),
                RatVec3::new(Rat::one(), Rat::zero(), Rat::zero()),
            )
        };
        let contact = PairContact::of(ScrewPair::new(
            situated(sigma.clone()),
            situated(Rat::one() - &sigma),
        ));
        let material = ContactMaterial::new(
            SymmetricForm::from_rows(vec![
                vec![Rat::one(), Rat::zero(), Rat::zero()],
                vec![Rat::zero(), Rat::one(), Rat::zero()],
                vec![Rat::zero(), Rat::zero(), Rat::one()],
            ])?,
            Rat::one(),
        )?;
        Ok(Self {
            sigma,
            gamma,
            contact,
            material,
        })
    }

    pub fn sigma(&self) -> &Rat {
        &self.sigma
    }
    pub fn gamma(&self) -> &Rat {
        &self.gamma
    }
    pub fn contact(&self) -> &PairContact {
        &self.contact
    }

    /// Unit isotropic material, both rates one: power `(2σ−1)²`, independent of `γ`.
    pub fn read(&self) -> Result<ContactReading, SolenoidalError> {
        ContactReading::at(&self.contact, &self.material, &[Rat::one(), Rat::one()])
    }

    /// The Gaussian-rational algebraic inductance `−2 / ((σ−1/2)+iγ)²`.
    /// A non-real or negative result remains such; the centre has no inverse and is refused.
    pub fn inductance(&self) -> Result<GaussianRat, SolenoidalError> {
        let centered = GaussianRat::new(&self.sigma - rat(1, 2), self.gamma.clone());
        Ok(GaussianRat::real(integer(-2)).div(&centered.pow(2))?)
    }

    /// The exact hypotheses of `locked_iff_foster_inductance_positive` are enforced here.
    pub fn certify_foster(&self) -> Result<FosterTank, SolenoidalError> {
        if self.gamma.is_zero() {
            return Err(SolenoidalError::ZeroAngularCoordinate);
        }
        if self.sigma != rat(1, 2) {
            return Err(SolenoidalError::OffSeam {
                sigma: self.sigma.clone(),
            });
        }
        let inductance = self.inductance()?;
        if !inductance.is_real() || !inductance.re.is_positive() || !self.read()?.no_slip {
            return Err(SolenoidalError::CertificateMismatch);
        }
        let mode = LcMode::new(inductance.re, rat(1, 2))?;
        if mode.omega_squared() != &(&self.gamma * &self.gamma) {
            return Err(SolenoidalError::CertificateMismatch);
        }
        Ok(FosterTank { mode })
    }
}

/// A positive parallel LC tank from the explicitly checked reflected-pair hypotheses.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FosterTank {
    mode: LcMode,
}

impl FosterTank {
    pub fn lc_mode(&self) -> &LcMode {
        &self.mode
    }

    /// `Z(s) = s L / (1 + s² L C)` on the open right half plane.
    /// With positive `L,C`, `Re Z = L Re(s) (1 + LC |s|²)/|1+LC s²|² > 0`.
    /// This rational chart checks the domain and its returned sign. It is not a realization
    /// of any infinite Foster sum, a source impedance, or a theorem about zero locations.
    pub fn impedance(&self, s: &GaussianRat) -> Result<GaussianRat, SolenoidalError> {
        if !s.re.is_positive() {
            return Err(SolenoidalError::OutsideRightHalfPlane { real: s.re.clone() });
        }
        let lc = self.mode.inductance() * self.mode.capacitance();
        let denominator = GaussianRat::one().add(&s.pow(2).scale(&lc));
        let impedance = s.scale(self.mode.inductance()).div(&denominator)?;
        if !impedance.re.is_positive() {
            return Err(SolenoidalError::CertificateMismatch);
        }
        Ok(impedance)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn semidefinite_material_has_a_genuine_nonzero_zero_power_slip() {
        let pair = ReflectedPair::new(rat(3, 4), integer(2)).unwrap();
        // The pair slips axially; this passive material reads only the transverse coordinates.
        let material = ContactMaterial::new(
            SymmetricForm::from_rows(vec![
                vec![integer(1), integer(0), integer(0)],
                vec![integer(0), integer(1), integer(0)],
                vec![integer(0), integer(0), integer(0)],
            ])
            .unwrap(),
            integer(1),
        )
        .unwrap();
        let reading =
            ContactReading::at(pair.contact(), &material, &[integer(1), integer(1)]).unwrap();
        assert!(reading.zero_power);
        assert!(!reading.no_slip);
        assert!(!reading.definite_on_slips);
        assert_eq!(reading.slip.z, rat(1, 2));
        assert_eq!(reading.no_slip_kernel.len(), 0);
        assert_eq!(reading.zero_power_kernel.len(), 1);
        assert!(matches!(
            pair.certify_foster(),
            Err(SolenoidalError::OffSeam { .. })
        ));
    }

    #[test]
    fn reflected_pair_reads_existing_contact_and_refuses_a_false_foster_claim() {
        for sigma in [integer(-1), integer(0), rat(1, 2), rat(3, 4), integer(2)] {
            for gamma in [integer(-3), integer(0), rat(2, 3)] {
                let pair = ReflectedPair::new(sigma.clone(), gamma.clone()).unwrap();
                let reading = pair.read().unwrap();
                let defect = integer(2) * &sigma - integer(1);
                assert_eq!(reading.dissipated_power, &defect * &defect);
                assert_eq!(reading.bond.power(), -&reading.dissipated_power);
                assert_eq!(reading.no_slip, sigma == rat(1, 2));
                assert_eq!(reading.zero_power, reading.no_slip);
                assert!(reading.definite_on_slips);
                assert_eq!(
                    pair.certify_foster().is_ok(),
                    sigma == rat(1, 2) && !gamma.is_zero()
                );
            }
        }
        let centre = ReflectedPair::new(rat(1, 2), integer(0)).unwrap();
        assert!(centre.read().unwrap().no_slip);
        assert!(centre.inductance().is_err());
        assert_eq!(
            centre.certify_foster(),
            Err(SolenoidalError::ZeroAngularCoordinate)
        );
    }

    #[test]
    fn foster_tank_joins_the_owner_mode_and_exact_impedance() {
        let tank = ReflectedPair::new(rat(1, 2), integer(-3))
            .unwrap()
            .certify_foster()
            .unwrap();
        let mode = tank.lc_mode();
        assert_eq!(mode.inductance(), &rat(2, 9));
        assert_eq!(mode.omega_squared(), &integer(9));
        let at_rest = mode.energy(&RationalPhase::new(integer(0), 0)).unwrap();
        let at_quarter = mode.energy(&RationalPhase::new(integer(1), 0)).unwrap();
        assert_eq!(at_rest.total(), at_quarter.total());
        assert!(at_rest.capacitive.is_zero());
        assert!(at_quarter.inductive.is_zero());
        for s in [
            GaussianRat::from_i64(1, 0),
            GaussianRat::new(rat(2, 3), rat(-7, 5)),
        ] {
            let z = tank.impedance(&s).unwrap();
            let algebraic = s
                .scale(&integer(2))
                .div(&s.pow(2).add(&GaussianRat::real(integer(9))))
                .unwrap();
            assert_eq!(z, algebraic);
            assert!(z.re.is_positive());
        }
        assert!(matches!(
            tank.impedance(&GaussianRat::i()),
            Err(SolenoidalError::OutsideRightHalfPlane { .. })
        ));
        assert!(matches!(
            tank.impedance(&GaussianRat::from_i64(-1, 2)),
            Err(SolenoidalError::OutsideRightHalfPlane { .. })
        ));
        assert!(LcMode::new(integer(0), integer(1)).is_err());
        assert!(LcMode::new(integer(1), integer(-1)).is_err());
    }

    #[test]
    fn local_sheet_receipt_is_energy_minimization_with_ties_and_shape_refusals() {
        let population =
            Population::new(vec![(0, 1, integer(2))], vec![integer(-1), integer(0)]).unwrap();
        let reading = local_sheet(&population, &[true, false], 0).unwrap();
        assert_eq!(reading.field, integer(1));
        assert!(!reading.half_turn);
        assert!(!reading.tied);
        assert_eq!(&reading.energy_before - &reading.energy_after, integer(2));
        let tied = Population::new(vec![], vec![integer(0)]).unwrap();
        let reading = local_sheet(&tied, &[true], 0).unwrap();
        assert!(reading.tied);
        assert_eq!(reading.energy_before, reading.energy_after);
        assert!(local_sheet(&population, &[false], 0).is_err());
        assert!(local_sheet(&population, &[false, false], 2).is_err());
    }
}
