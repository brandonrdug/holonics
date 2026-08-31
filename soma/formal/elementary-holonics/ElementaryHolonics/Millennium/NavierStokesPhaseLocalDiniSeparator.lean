import ElementaryHolonics.Millennium.NavierStokesCriticalPhaseAlignmentSeparator

/-!
# Cross-shell separation of the phase-local Dini receiver

**[proved-derived; formal-checked]**  The genuine phase-local shell owner first reconstructs the
complete complex population on the spatial torus and only then takes its supremum norm.  This file
tests the corresponding `B^0_{infinity,1}`/Dini population across all dyadic addresses.

The coherent family below is normalized by the inverse cube of the shell radius.  Its strongest
energy-paid frozen square mass is the reciprocal radius square and is summable.  At the zero torus
chart all characters still align, so the spatial shell supremum is exactly one at every scale and
its Dini population is not summable.

This is an exact receiver separator, not a Navier--Stokes solution or a blow-up construction.  It
shows that retaining phase until after shell reconstruction is necessary but not sufficient:
terminal control also owes a constitutive estimate excluding coherent concentration across the
transported shell population.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPhaseLocalDiniSeparator

open Soma.Holonics.Millennium.NavierStokesCriticalEnergySquareSeparator
open Soma.Holonics.Millennium.NavierStokesCriticalPhaseAlignmentSeparator

/-- A real constant section, retained as a complete phase-bearing occurrence population. -/
def constantCriticalEnergyShellSection (level : ℕ) (amplitude : ℝ) :
    CriticalEnergyShellSection level := fun _ ↦ (amplitude : ℂ)

theorem energyPaidFrozenShellSquareMass_constant
    (level : ℕ) (amplitude : ℝ) :
    energyPaidFrozenShellSquareMass
        (constantCriticalEnergyShellSection level amplitude) =
      (criticalEnergyShellRadius level : ℝ) ^ 4 * amplitude ^ 2 := by
  unfold energyPaidFrozenShellSquareMass constantCriticalEnergyShellSection
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, Finset.sum_const,
    Finset.card_univ, card_criticalEnergyShellOccurrence, nsmul_eq_mul,
    Nat.cast_pow]
  ring

/-- The coherent family is normalized so its signed spatial amplitude is exactly one at every
dyadic shell. -/
def coherentDiniFiringSection (level : ℕ) :
    CriticalEnergyShellSection level :=
  constantCriticalEnergyShellSection level
    ((criticalEnergyShellRadius level : ℝ)⁻¹ ^ 3)

theorem coherentDiniFiringSection_absoluteMass (level : ℕ) :
    criticalEnergyShellAbsoluteMass (coherentDiniFiringSection level) = 1 := by
  have hradius : (criticalEnergyShellRadius level : ℝ) ≠ 0 := by
    exact_mod_cast (criticalEnergyShellRadius_pos level).ne'
  unfold criticalEnergyShellAbsoluteMass coherentDiniFiringSection
    constantCriticalEnergyShellSection
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_inv,
    abs_of_pos (by exact_mod_cast criticalEnergyShellRadius_pos level :
      (0 : ℝ) < criticalEnergyShellRadius level), Finset.sum_const,
    Finset.card_univ, card_criticalEnergyShellOccurrence, nsmul_eq_mul,
    Nat.cast_pow]
  field_simp

theorem coherentDiniFiringSection_zeroAmplitude (level : ℕ) :
    ‖∑ occurrence : CriticalEnergyShellOccurrence level,
        coherentDiniFiringSection level occurrence‖ = 1 := by
  have hradius : (criticalEnergyShellRadius level : ℝ) ≠ 0 := by
    exact_mod_cast (criticalEnergyShellRadius_pos level).ne'
  unfold coherentDiniFiringSection constantCriticalEnergyShellSection
  rw [Finset.sum_const, Finset.card_univ, card_criticalEnergyShellOccurrence]
  simp only [nsmul_eq_mul, Complex.norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_pow, abs_inv,
    abs_of_pos (by exact_mod_cast criticalEnergyShellRadius_pos level :
      (0 : ℝ) < criticalEnergyShellRadius level), Nat.cast_pow]
  field_simp
  rw [norm_pow, Complex.norm_natCast]

/-- The genuine torus spatial-supremum shell receiver is exactly one: the upper bound is absolute
mass, while the lower bound is the coherent signed return at the zero chart. -/
theorem coherentDiniFiringSection_spatialSup (level : ℕ) :
    criticalEnergyShellSpatialSup (coherentDiniFiringSection level) = 1 := by
  apply le_antisymm
  · exact (criticalEnergyShellSpatialSup_le_absoluteMass _).trans_eq
      (coherentDiniFiringSection_absoluteMass level)
  · rw [← coherentDiniFiringSection_zeroAmplitude level]
    exact norm_sum_le_criticalEnergyShellSpatialSup
      (coherentDiniFiringSection level)

/-- The strongest energy-paid frozen square mass of the same coherent shell is the reciprocal
radius square. -/
theorem coherentDiniFiringSection_energyPaidFrozenShellSquareMass (level : ℕ) :
    energyPaidFrozenShellSquareMass (coherentDiniFiringSection level) =
      (criticalEnergyShellRadius level : ℝ)⁻¹ ^ 2 := by
  have hconstant := energyPaidFrozenShellSquareMass_constant level
    ((criticalEnergyShellRadius level : ℝ)⁻¹ ^ 3)
  have hradius : (criticalEnergyShellRadius level : ℝ) ≠ 0 := by
    exact_mod_cast (criticalEnergyShellRadius_pos level).ne'
  calc
    energyPaidFrozenShellSquareMass (coherentDiniFiringSection level) =
        (criticalEnergyShellRadius level : ℝ) ^ 4 *
          ((criticalEnergyShellRadius level : ℝ)⁻¹ ^ 3) ^ 2 := by
      simpa only [coherentDiniFiringSection] using hconstant
    _ = (criticalEnergyShellRadius level : ℝ)⁻¹ ^ 2 := by field_simp

/-- The energy-paid square population of the complete coherent firing family is summable. -/
theorem summable_coherentDiniFiringSection_energyPaidFrozenShellSquareMass :
    Summable (fun level : ℕ ↦
      energyPaidFrozenShellSquareMass (coherentDiniFiringSection level)) := by
  apply (summable_geometric_of_norm_lt_one
    (x := ((2 : ℝ)⁻¹) ^ 2) (by norm_num)).congr
  intro level
  rw [coherentDiniFiringSection_energyPaidFrozenShellSquareMass]
  simp only [criticalEnergyShellRadius, Nat.cast_pow]
  change (((2 : ℝ)⁻¹) ^ 2) ^ level = (((2 : ℝ) ^ level)⁻¹) ^ 2
  conv_rhs => rw [← inv_pow]
  rw [← pow_mul]
  rw [← pow_mul]
  rw [Nat.mul_comm]

/-- Its genuine phase-local spatial Dini population is the constant unit sequence and is not
summable. -/
theorem not_summable_coherentDiniFiringSection_spatialSup :
    ¬ Summable (fun level : ℕ ↦
      criticalEnergyShellSpatialSup (coherentDiniFiringSection level)) := by
  rw [show (fun level : ℕ ↦
      criticalEnergyShellSpatialSup (coherentDiniFiringSection level)) =
        fun _ : ℕ ↦ (1 : ℝ) by
    funext level
    exact coherentDiniFiringSection_spatialSup level]
  rw [summable_const_iff]
  norm_num

/-- **Global phase-local separator.**  Summability of the strongest energy-paid square shell
population does not imply summability of the phase-preserving spatial Dini population. -/
theorem energyPaidSquareSummable_not_enough_for_phaseLocalSpatialDini :
    ∃ carrier : ∀ level : ℕ, CriticalEnergyShellSection level,
      Summable (fun level ↦ energyPaidFrozenShellSquareMass (carrier level)) ∧
        ¬ Summable (fun level ↦ criticalEnergyShellSpatialSup (carrier level)) := by
  exact ⟨coherentDiniFiringSection,
    summable_coherentDiniFiringSection_energyPaidFrozenShellSquareMass,
    not_summable_coherentDiniFiringSection_spatialSup⟩

/-- There is no universal implication from energy-paid square summability to the phase-local
spatial Dini endpoint, even though each norm is delayed until after genuine torus synthesis. -/
theorem no_phaseLocalSpatialDini_of_energyPaidSquareSummable :
    ¬ ∀ carrier : ∀ level : ℕ, CriticalEnergyShellSection level,
      Summable (fun level ↦ energyPaidFrozenShellSquareMass (carrier level)) →
        Summable (fun level ↦ criticalEnergyShellSpatialSup (carrier level)) := by
  intro h
  exact not_summable_coherentDiniFiringSection_spatialSup
    (h coherentDiniFiringSection
      summable_coherentDiniFiringSection_energyPaidFrozenShellSquareMass)

section Audit

#print axioms energyPaidFrozenShellSquareMass_constant
#print axioms coherentDiniFiringSection_absoluteMass
#print axioms coherentDiniFiringSection_zeroAmplitude
#print axioms coherentDiniFiringSection_spatialSup
#print axioms coherentDiniFiringSection_energyPaidFrozenShellSquareMass
#print axioms summable_coherentDiniFiringSection_energyPaidFrozenShellSquareMass
#print axioms not_summable_coherentDiniFiringSection_spatialSup
#print axioms energyPaidSquareSummable_not_enough_for_phaseLocalSpatialDini
#print axioms no_phaseLocalSpatialDini_of_energyPaidSquareSummable

end Audit

end Soma.Holonics.Millennium.NavierStokesPhaseLocalDiniSeparator
