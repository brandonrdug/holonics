//! The ratio covector at a thermal port: the port's constitution, the protocol's work, heat and
//! production, and the heat's return to the bath.

use num_traits::{One, Zero};

use crate::aeon::PositiveLaw;
use crate::physics::thermal::{EntropyEnclosure, ThermalCell};
use crate::ratio::exponentiated::exponentiate;
use crate::ratio::surprisal::SymbolicSurprisal;
use crate::ratio::{LogRatio, Rat};

use super::InformationError;

pub(super) fn same_extent(
    what: &'static str,
    expected: usize,
    found: usize,
) -> Result<(), InformationError> {
    if expected == found {
        Ok(())
    } else {
        Err(InformationError::Shape {
            what,
            expected,
            found,
        })
    }
}

/// `U(E, r) = Σ rᵢ Eᵢ`: the energy of a law on levels given as exact forms.
fn energy(law: &PositiveLaw, levels: &[SymbolicSurprisal]) -> SymbolicSurprisal {
    law.masses()
        .iter()
        .zip(levels)
        .fold(SymbolicSurprisal::zero(), |sum, (mass, level)| {
            sum.plus(&level.scaled(mass))
        })
}

/// `H₂(r) = C(r, r)`, the entropy in bits, from the owner's cross-entropy.
fn entropy(law: &PositiveLaw) -> Result<SymbolicSurprisal, InformationError> {
    Ok(law.cross_entropy(law)?)
}

/// `D₂(p‖q) = C(p, q) − H₂(p)`, from the owner's cross-entropy.
fn divergence(
    population: &PositiveLaw,
    reference: &PositiveLaw,
) -> Result<SymbolicSurprisal, InformationError> {
    Ok(population
        .cross_entropy(reference)?
        .minus(&population.cross_entropy(population)?))
}

/// The Boltzmann weights `2^(−Eᵢ)` of levels in units of `k_B T ln 2`, each exponentiated exactly.
fn weights(levels: &[SymbolicSurprisal]) -> Result<Vec<Rat>, InformationError> {
    Ok(levels
        .iter()
        .map(|level| exponentiate(&level.scaled(&-Rat::one())))
        .collect::<Result<_, _>>()?)
}

/// `log₂ Z(E)`, `Z = Σ 2^(−Eᵢ)` (Lean `PortWork.partition`).
fn log_partition(levels: &[SymbolicSurprisal]) -> Result<SymbolicSurprisal, InformationError> {
    let partition = weights(levels)?
        .into_iter()
        .fold(Rat::zero(), |sum, weight| sum + weight);
    Ok(SymbolicSurprisal::log2_of_ratio(&partition)?)
}

/// [proved-derived; implemented-exact] **The canonical state of levels, computed from them**:
/// `2^(−Eᵢ)/Z(E)` (Lean `PortWork.canonicalState`, `canonicalState_canonical`). Exact when every
/// level's form has integer coefficients; a fractional one leaves ℚ and is refused.
pub fn canonical_state(levels: &[SymbolicSurprisal]) -> Result<PositiveLaw, InformationError> {
    let weights = weights(levels)?;
    let partition = weights.iter().fold(Rat::zero(), |sum, weight| sum + weight);
    Ok(PositiveLaw::new(
        weights
            .into_iter()
            .map(|weight| weight / &partition)
            .collect(),
    )?)
}

/// The value of a form whose only prime is `2` (`log₂ 2 = 1`): a rational number of bits.
fn rational_bits(form: &SymbolicSurprisal) -> Option<Rat> {
    match form.terms().iter().collect::<Vec<_>>().as_slice() {
        [] => Some(Rat::zero()),
        [(2, coefficient)] => Some((*coefficient).clone()),
        _ => None,
    }
}

/// [definition] **One level's ratio covector**: its modulus face `log₂|R|²`, the intensity ratio
/// `log₂(q/p)` of the target to the produced population, and its phase face when it comes from the
/// owner's lift of `log(ψ_T/ψ_H)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LevelCovector {
    modulus_log2: SymbolicSurprisal,
    phase: Option<LogRatio>,
}

impl LevelCovector {
    /// [definition] **The owner's lift** of `log R`, `R = ψ_T/ψ_H` a Gaussian rational ratio with
    /// its winding: the modulus face is `log₂|R|²` ([`LogRatio::modulus_log2`]); the lift itself is
    /// retained as the phase face.
    pub fn of_lift(lift: LogRatio) -> Result<Self, InformationError> {
        Ok(Self {
            modulus_log2: lift.modulus_log2()?,
            phase: Some(lift),
        })
    }

    /// [definition] The intensity ratio `(target : produced)` declared directly, with no phase face.
    pub fn of_intensities(target: &Rat, produced: &Rat) -> Result<Self, InformationError> {
        Ok(Self {
            modulus_log2: SymbolicSurprisal::log2_of_ratio(&(target / produced))?,
            phase: None,
        })
    }

    pub fn modulus_log2(&self) -> &SymbolicSurprisal {
        &self.modulus_log2
    }

    pub fn phase(&self) -> Option<&LogRatio> {
        self.phase.as_ref()
    }
}

/// [definition] **A thermal port**: a bath (a K3 [`ThermalCell`] at temperature `T`), the port's
/// levels `E` in units of `k_B T ln 2`, and its reference `q`, canonical for the levels (Lean
/// `PortWork.Canonical`): `Eᵢ + log₂ qᵢ = −log₂ Z` for every level.
///
/// [definition; agent-inferred] **The unit map.** One port unit of energy, `k_B T ln 2`, is `T`
/// units of the bath's energy when the bath's capacity is read in units of `k_B ln 2`; under that
/// reading the K3 entropy chart `C log U` is in bits, the port's own entropy unit. Reason: the
/// port's heat then enters the bath's rational first law without evaluating `ln 2`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ThermalPort {
    bath: ThermalCell,
    levels: Vec<SymbolicSurprisal>,
    reference: PositiveLaw,
}

impl ThermalPort {
    /// [proved-derived; implemented-exact] A port, refused unless the reference is canonical for
    /// the levels, decided exactly on the forms (Lean `Canonical`).
    pub fn new(
        bath: ThermalCell,
        levels: Vec<SymbolicSurprisal>,
        reference: PositiveLaw,
    ) -> Result<Self, InformationError> {
        same_extent(
            "reference (one mass per level)",
            levels.len(),
            reference.masses().len(),
        )?;
        let gauge = |level: &SymbolicSurprisal, mass: &Rat| {
            SymbolicSurprisal::of_probability(mass).map(|surprisal| level.minus(&surprisal))
        };
        let mut pairs = levels.iter().zip(reference.masses());
        if let Some((level, mass)) = pairs.next() {
            let first = gauge(level, mass)?;
            for (index, (level, mass)) in pairs.enumerate() {
                if gauge(level, mass)? != first {
                    return Err(InformationError::NotCanonical { level: index + 1 });
                }
            }
        }
        Ok(Self {
            bath,
            levels,
            reference,
        })
    }

    /// [proved-derived; implemented-exact] The port whose reference is the canonical state computed
    /// from its levels ([`canonical_state`]).
    pub fn of_levels(
        bath: ThermalCell,
        levels: Vec<SymbolicSurprisal>,
    ) -> Result<Self, InformationError> {
        let reference = canonical_state(&levels)?;
        Self::new(bath, levels, reference)
    }

    pub fn bath(&self) -> &ThermalCell {
        &self.bath
    }

    pub fn levels(&self) -> &[SymbolicSurprisal] {
        &self.levels
    }

    pub fn reference(&self) -> &PositiveLaw {
        &self.reference
    }
}

/// [definition] **What the port returns** when a covector reaches it as a level shift. Energies in
/// units of `k_B T ln 2`, entropies in bits; every quantity an exact form, computed from its own
/// operands, and every law relating them decided exactly by a residual.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortApply {
    /// Per level, the effort `δᵢ`: the covector's modulus face, the level shift.
    pub effort: Vec<SymbolicSurprisal>,
    /// The shifted levels `E + δ` (Lean `shifted`).
    pub shifted_levels: Vec<SymbolicSurprisal>,
    /// The covector's phase faces, retained unconsumed by this port.
    pub retained_phase: Vec<Option<LogRatio>>,
    /// `W_q = Σ pᵢ δᵢ`, levels moved with the population frozen (Lean `quenchWork`).
    pub quench_work: SymbolicSurprisal,
    /// `q′`, the canonical state of the shifted levels, computed from them (Lean `relaxed`).
    pub relaxed: PositiveLaw,
    /// `Q_rel = U(E + δ, q′) − U(E + δ, p)`, the relaxation's heat at fixed levels.
    pub relax_heat: SymbolicSurprisal,
    /// `W_r = log₂ Z(E + δ) − log₂ Z(E)`, the restoring leg's quasi-static work, from the partition
    /// functions (Lean `restoreWork`).
    pub restore_work: SymbolicSurprisal,
    /// `Q_res = U(E, after) − U(E + δ, q′) − W_r`, the restoring leg's energy balance.
    pub restore_heat: SymbolicSurprisal,
    /// The receiver's state after the protocol: the canonical state of the restored levels,
    /// computed from them (Lean `canonicalState`).
    pub after: PositiveLaw,
    /// The port's reference, which the restoration must return (Lean `canonicalState_eq`).
    pub reference: PositiveLaw,
    /// `ΔU = U(E, after) − U(E, p)`.
    pub internal_change: SymbolicSurprisal,
    /// `σ = H₂(after) − H₂(p) − (Q_rel + Q_res)`, from the entropies and the heats (Lean
    /// `protocolProduction`).
    pub production: SymbolicSurprisal,
    /// `σ_res = H₂(after) − H₂(q′) − Q_res` (Lean `restoreProduction`).
    pub restore_production: SymbolicSurprisal,
    /// `D₂(p‖q′)`.
    pub relaxation_divergence: SymbolicSurprisal,
    /// `D₂(p‖q)`.
    pub relative_entropy: SymbolicSurprisal,
    /// `F(p) − F(q)` with `F = U − H₂` at the levels `E`.
    pub free_energy_drop: SymbolicSurprisal,
    /// `σ_free = H₂(q) − H₂(p) − (U(E, q) − U(E, p))`, free relaxation's production (Lean
    /// `freeProduction`).
    pub free_production: SymbolicSurprisal,
}

impl PortApply {
    /// The heat the ensemble drew from the bath over both legs.
    pub fn heat(&self) -> SymbolicSurprisal {
        self.relax_heat.plus(&self.restore_heat)
    }

    /// The work done on the ensemble, `W_q + W_r`; the work extracted is its negative.
    pub fn work(&self) -> SymbolicSurprisal {
        self.quench_work.plus(&self.restore_work)
    }

    /// `σ − D₂(p‖q′)` (Lean `protocol_production`).
    pub fn production_residual(&self) -> SymbolicSurprisal {
        self.production.minus(&self.relaxation_divergence)
    }

    /// `(F(p) − F(q)) − D₂(p‖q)` (Lean `freeEnergy_difference_eq_thermalScale_mul_kl`).
    pub fn gibbs_kl_residual(&self) -> SymbolicSurprisal {
        self.free_energy_drop.minus(&self.relative_entropy)
    }

    /// `−W − (F(p) − F(q) − D₂(p‖q′))` (Lean `extracted_work_general`).
    pub fn extracted_work_residual(&self) -> SymbolicSurprisal {
        self.work()
            .scaled(&-Rat::one())
            .minus(&self.free_energy_drop.minus(&self.relaxation_divergence))
    }

    /// `σ_free − D₂(p‖q)` (Lean `free_relaxation_production`).
    pub fn free_production_residual(&self) -> SymbolicSurprisal {
        self.free_production.minus(&self.relative_entropy)
    }

    /// `−W − (σ_free − σ)` (Lean `work_or_production`).
    pub fn work_or_production_residual(&self) -> SymbolicSurprisal {
        self.work()
            .scaled(&-Rat::one())
            .minus(&self.free_production.minus(&self.production))
    }

    /// Whether every law closes exactly: the restoration returns the reference, the restoring leg
    /// produces nothing, the protocol produces `D₂(p‖q′)`, the Gibbs/KL identity, the extracted
    /// work, free relaxation's production and work-or-production.
    pub fn balances(&self) -> bool {
        self.after == self.reference
            && self.restore_production.is_zero()
            && self.production_residual().is_zero()
            && self.gibbs_kl_residual().is_zero()
            && self.extracted_work_residual().is_zero()
            && self.free_production_residual().is_zero()
            && self.work_or_production_residual().is_zero()
    }

    /// [proved-derived; implemented-exact] **The heat returns to the bath**: the K3 cell after the
    /// ensemble drew `Q`, `U_bath − T·Q` in the bath's units (the port's unit map). Refused when the
    /// heat's form is irrational, which the bath's rational first law cannot receive exactly, or when
    /// the bath would be emptied.
    pub fn bath_after(&self, port: &ThermalPort) -> Result<ThermalCell, InformationError> {
        let heat = self.heat();
        let bits = rational_bits(&heat).ok_or(InformationError::IrrationalHeat { heat })?;
        let bath = port.bath();
        Ok(ThermalCell::new(
            bath.capacity().clone(),
            bath.energy() - bath.temperature() * bits,
        )?)
    }

    /// The bath's entropy change over the protocol, enclosed (Lean
    /// `Physics/Thermal/Exchange.cell_entropy_enclosure`).
    pub fn bath_entropy(&self, port: &ThermalPort) -> Result<EntropyEnclosure, InformationError> {
        Ok(EntropyEnclosure::of_cell(
            port.bath(),
            &self.bath_after(port)?,
        ))
    }
}

/// [proved-derived; implemented-exact] **A covector reaches the thermal port as a level shift**
/// (Lean `Physics/Information/PortWork`). Refused unless the population is a law on the port's
/// levels and there is one covector per level. Any modulus face is admitted: the protocol quenches
/// the levels by it, relaxes at the shifted levels to their computed canonical state, and restores
/// the levels quasi-statically; the return carries each quantity computed from its own operands and
/// the residuals of the laws relating them. The matched covector `log₂(q/p)` (the modulus face of
/// the full ratio covector comparing this reference with this population) relaxes to `p` itself
/// and produces nothing (Lean `matched_relaxed`, `reversible_production_zero`); any other produces
/// `D₂(p‖q′) > 0` and extracts less work. Exact when the shifted levels' forms have integer
/// coefficients.
pub fn apply(
    port: &ThermalPort,
    population: &PositiveLaw,
    covector: &[LevelCovector],
) -> Result<PortApply, InformationError> {
    let levels = port.levels();
    same_extent(
        "population (one mass per level)",
        levels.len(),
        population.masses().len(),
    )?;
    same_extent("covector (one per level)", levels.len(), covector.len())?;
    let effort: Vec<SymbolicSurprisal> = covector
        .iter()
        .map(|level| level.modulus_log2().clone())
        .collect();
    let shifted_levels: Vec<SymbolicSurprisal> = levels
        .iter()
        .zip(&effort)
        .map(|(level, shift)| level.plus(shift))
        .collect();
    let quench_work = energy(population, &effort);
    let relaxed = canonical_state(&shifted_levels)?;
    let relax_heat = energy(&relaxed, &shifted_levels).minus(&energy(population, &shifted_levels));
    let restore_work = log_partition(&shifted_levels)?.minus(&log_partition(levels)?);
    let after = canonical_state(levels)?;
    let restore_heat = energy(&after, levels)
        .minus(&energy(&relaxed, &shifted_levels))
        .minus(&restore_work);
    let heat = relax_heat.plus(&restore_heat);
    let entropy_before = entropy(population)?;
    let entropy_after = entropy(&after)?;
    let production = entropy_after.minus(&entropy_before).minus(&heat);
    let restore_production = entropy_after
        .minus(&entropy(&relaxed)?)
        .minus(&restore_heat);
    let reference = port.reference();
    let (energy_before, energy_reference) = (energy(population, levels), energy(reference, levels));
    let entropy_reference = entropy(reference)?;
    let free_energy_drop = energy_before
        .minus(&entropy_before)
        .minus(&energy_reference.minus(&entropy_reference));
    let free_production = entropy_reference
        .minus(&entropy_before)
        .minus(&energy_reference.minus(&energy_before));
    Ok(PortApply {
        retained_phase: covector
            .iter()
            .map(|level| level.phase().cloned())
            .collect(),
        internal_change: energy(&after, levels).minus(&energy_before),
        relaxation_divergence: divergence(population, &relaxed)?,
        relative_entropy: divergence(population, reference)?,
        effort,
        shifted_levels,
        quench_work,
        relaxed,
        relax_heat,
        restore_work,
        restore_heat,
        after,
        reference: reference.clone(),
        production,
        restore_production,
        free_energy_drop,
        free_production,
    })
}
