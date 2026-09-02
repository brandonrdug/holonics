import ElementaryHolonics.Millennium.NavierStokesWeightedTailEnergy
import ElementaryHolonics.Millennium.NavierStokesBandCoherence

/-!
# The incoherent band mass: the lattice weight removes the count from the shell-step cost

The band mass `Σ_{p ∈ cube N} ℓ¹(û(p))` was paid by the count `(2N+1)³` times the half-density of
the initial energy: every tooth of the band composed with aligned phase.  The lattice weight
already proved, `Σ_{p ≠ 0} |p|_∞⁻⁴ ≤ 52`, pays it incoherently instead:

```text
bandMass(N) ≤ ℓ¹(û(0)) + √52 · √( Σ_{p ∈ cube N, p ≠ 0} |p|_∞⁴ ℓ¹(û(p))² )
            ≤ ℓ¹(û(0)) + √(52 · 3 / (2π)²) · √( Σ_{p ∈ cube N, p ≠ 0} |p|_∞² E_p ),
```

the second line through Lagrange on the modes.  No count of modes remains; the band is paid by
its own second moment of vorticity energy and the zero mode.  This is the half power of the
record on the band comb, now unconditional, because Cauchy--Schwarz against a summable weight is
the incoherent composition made exact.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesIncoherentBandMass

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesModeLagrange
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesShellStepCost
open Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge

theorem one_le_frequencySup_of_ne_zero {p : SpatialFrequency} (hp : p ≠ 0) :
    1 ≤ frequencySup p := by
  by_contra h
  push Not at h
  apply hp
  funext coordinate
  have : (p coordinate).natAbs ≤ frequencySup p :=
    Finset.le_sup (f := fun c ↦ (p c).natAbs) (Finset.mem_univ coordinate)
  simp only [Pi.zero_apply]
  omega

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
  (t : Ioo 0 T)

/-- The fourth-moment `ℓ¹` population of the band's nonzero modes. -/
def bandFourthMoment (radius : ℕ) : ℝ :=
  ∑ p ∈ (frequencyCube radius).erase 0,
    ((frequencySup p : ℕ) : ℝ) ^ 4 *
      complexVectorL1 (openPeriodicVelocityFourierMode solution t p) ^ 2

/-- The second moment of vorticity energy over the band's nonzero modes. -/
def bandSecondMoment (radius : ℕ) : ℝ :=
  ∑ p ∈ (frequencyCube radius).erase 0,
    ((frequencySup p : ℕ) : ℝ) ^ 2 * modalEnergy (velocity := velocity) p t.1

/-- **The incoherent band mass.**  Cauchy--Schwarz against the lattice weight. -/
theorem bandMass_le_incoherent (radius : ℕ) :
    bandMass solution t radius ≤
      complexVectorL1 (openPeriodicVelocityFourierMode solution t 0) +
        Real.sqrt 52 * Real.sqrt (bandFourthMoment solution t radius) := by
  unfold bandMass
  have h0 : (0 : SpatialFrequency) ∈ frequencyCube radius := by
    rw [mem_frequencyCube_iff]; intro c; simp
  rw [← Finset.add_sum_erase _ _ h0]
  apply add_le_add le_rfl
  set F := (frequencyCube radius).erase 0 with hF
  have hF1 : ∀ p ∈ F, 1 ≤ frequencySup p := by
    intro p hp
    exact one_le_frequencySup_of_ne_zero (Finset.ne_of_mem_erase hp)
  set a : SpatialFrequency → ℝ := fun p ↦ 1 / ((frequencySup p : ℕ) : ℝ) ^ 2 with ha
  set b : SpatialFrequency → ℝ := fun p ↦
    ((frequencySup p : ℕ) : ℝ) ^ 2 * complexVectorL1 (openPeriodicVelocityFourierMode solution t p)
    with hb
  have hprod : ∀ p ∈ F, complexVectorL1 (openPeriodicVelocityFourierMode solution t p) = a p * b p := by
    intro p hp
    have hp0 : (0 : ℝ) < ((frequencySup p : ℕ) : ℝ) := by exact_mod_cast hF1 p hp
    simp only [ha, hb]
    field_simp
  rw [Finset.sum_congr rfl hprod]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq F a b
  have hA : ∑ p ∈ F, a p ^ 2 ≤ 52 := by
    have : ∀ p ∈ F, a p ^ 2 = 1 / ((frequencySup p : ℕ) : ℝ) ^ 4 := by
      intro p _
      simp only [ha]
      field_simp
    rw [Finset.sum_congr rfl this]
    exact sum_inv_pow_four_le F hF1
  have hB : ∑ p ∈ F, b p ^ 2 = bandFourthMoment solution t radius := by
    unfold bandFourthMoment
    apply Finset.sum_congr rfl
    intro p _
    simp only [hb]
    ring
  have hsum_nonneg : 0 ≤ ∑ p ∈ F, a p * b p :=
    Finset.sum_nonneg fun p _ ↦ mul_nonneg (by positivity) (mul_nonneg (by positivity) (complexVectorL1_nonneg _))
  have hB0 : 0 ≤ ∑ p ∈ F, b p ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hsq : (∑ p ∈ F, a p * b p) ^ 2 ≤ 52 * bandFourthMoment solution t radius := by
    rw [← hB]
    exact hcs.trans (mul_le_mul_of_nonneg_right hA hB0)
  rw [← Real.sqrt_sq hsum_nonneg, ← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 52)]
  exact Real.sqrt_le_sqrt hsq

/-- Each nonzero mode's fourth-moment tooth is paid by its second-moment energy: Lagrange. -/
theorem fourthMoment_tooth_le (p : SpatialFrequency) :
    ((frequencySup p : ℕ) : ℝ) ^ 4 *
        complexVectorL1 (openPeriodicVelocityFourierMode solution t p) ^ 2 ≤
      3 / (2 * Real.pi) ^ 2 *
        (((frequencySup p : ℕ) : ℝ) ^ 2 * modalEnergy (velocity := velocity) p t.1) := by
  set v := openPeriodicVelocityFourierMode solution t p with hv
  have hE : modalEnergy (velocity := velocity) p t.1 =
      (2 * Real.pi) ^ 2 * frequencySquared p * ∑ i : Fin 3, ‖v i‖ ^ 2 := by
    rw [modalEnergy_eq_sum_norm_sq_curl solution t p]
    exact sum_norm_sq_frequencyCurlMultiplier p v (openPeriodicVelocityFourierMode_divergenceFree solution t p)
  have hl1 : complexVectorL1 v ^ 2 ≤ 3 * ∑ i : Fin 3, ‖v i‖ ^ 2 := by
    rw [Fin.sum_univ_three]
    unfold complexVectorL1
    nlinarith [sq_nonneg (‖v 0‖ - ‖v 1‖), sq_nonneg (‖v 1‖ - ‖v 2‖), sq_nonneg (‖v 0‖ - ‖v 2‖)]
  have hsup := frequencySup_sq_le_frequencySquared p
  have hS : 0 ≤ ∑ i : Fin 3, ‖v i‖ ^ 2 := Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have hpi : (0 : ℝ) < (2 * Real.pi) ^ 2 := by positivity
  rw [hE]
  have hsup0 : (0 : ℝ) ≤ ((frequencySup p : ℕ) : ℝ) ^ 2 := by positivity
  have key : ((frequencySup p : ℕ) : ℝ) ^ 4 * complexVectorL1 v ^ 2 ≤
      3 * (((frequencySup p : ℕ) : ℝ) ^ 2 * (frequencySquared p * ∑ i : Fin 3, ‖v i‖ ^ 2)) := by
    have h1 : ((frequencySup p : ℕ) : ℝ) ^ 4 * complexVectorL1 v ^ 2 ≤
        ((frequencySup p : ℕ) : ℝ) ^ 4 * (3 * ∑ i : Fin 3, ‖v i‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hl1 (by positivity)
    have h2 : ((frequencySup p : ℕ) : ℝ) ^ 2 * ∑ i : Fin 3, ‖v i‖ ^ 2 ≤
        frequencySquared p * ∑ i : Fin 3, ‖v i‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hsup hS
    calc ((frequencySup p : ℕ) : ℝ) ^ 4 * complexVectorL1 v ^ 2
        ≤ ((frequencySup p : ℕ) : ℝ) ^ 4 * (3 * ∑ i : Fin 3, ‖v i‖ ^ 2) := h1
      _ = 3 * (((frequencySup p : ℕ) : ℝ) ^ 2 * (((frequencySup p : ℕ) : ℝ) ^ 2 * ∑ i : Fin 3, ‖v i‖ ^ 2)) := by ring
      _ ≤ 3 * (((frequencySup p : ℕ) : ℝ) ^ 2 * (frequencySquared p * ∑ i : Fin 3, ‖v i‖ ^ 2)) := by
          gcongr
  calc ((frequencySup p : ℕ) : ℝ) ^ 4 * complexVectorL1 v ^ 2
      ≤ 3 * (((frequencySup p : ℕ) : ℝ) ^ 2 * (frequencySquared p * ∑ i : Fin 3, ‖v i‖ ^ 2)) := key
    _ = 3 / (2 * Real.pi) ^ 2 *
        (((frequencySup p : ℕ) : ℝ) ^ 2 *
          ((2 * Real.pi) ^ 2 * frequencySquared p * ∑ i : Fin 3, ‖v i‖ ^ 2)) := by
        field_simp

theorem bandFourthMoment_le (radius : ℕ) :
    bandFourthMoment solution t radius ≤
      3 / (2 * Real.pi) ^ 2 * bandSecondMoment (velocity := velocity) t radius := by
  unfold bandFourthMoment bandSecondMoment
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum fun p _ ↦ fourthMoment_tooth_le solution t p

/-- **The band mass is paid by the zero mode and the band's second moment of vorticity energy.**
No count of modes enters. -/
theorem bandMass_le_secondMoment (radius : ℕ) :
    bandMass solution t radius ≤
      complexVectorL1 (openPeriodicVelocityFourierMode solution t 0) +
        Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) *
          Real.sqrt (bandSecondMoment (velocity := velocity) t radius) := by
  refine (bandMass_le_incoherent solution t radius).trans ?_
  apply add_le_add le_rfl
  calc Real.sqrt 52 * Real.sqrt (bandFourthMoment solution t radius)
      ≤ Real.sqrt 52 *
          Real.sqrt (3 / (2 * Real.pi) ^ 2 * bandSecondMoment (velocity := velocity) t radius) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (bandFourthMoment_le solution t radius))
          (Real.sqrt_nonneg _)
    _ = Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) *
          Real.sqrt (bandSecondMoment (velocity := velocity) t radius) := by
        rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 3 / (2 * Real.pi) ^ 2),
          Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 52)]
        ring

/-- **The band feed at a tail mode, paid incoherently.** -/
theorem norm_bandFeed_le_secondMoment {radius : ℕ} {k : SpatialFrequency}
    (hk : k ∉ frequencyCube (2 * radius)) (output : Fin 3) :
    ‖bandFeed solution t radius k output‖ ≤
      (complexVectorL1 (openPeriodicVelocityFourierMode solution t 0) +
        Real.sqrt (52 * (3 / (2 * Real.pi) ^ 2)) *
          Real.sqrt (bandSecondMoment (velocity := velocity) t radius)) *
        openPeriodicJacobianCoefficientTailMass solution t (frequencyCube radius) :=
  (norm_bandFeed_le solution t hk output).trans
    (mul_le_mul_of_nonneg_right (bandMass_le_secondMoment solution t radius) (norm_nonneg _))

section Audit

#print axioms bandMass_le_incoherent
#print axioms fourthMoment_tooth_le
#print axioms bandMass_le_secondMoment
#print axioms norm_bandFeed_le_secondMoment

end Audit

end Soma.Holonics.Millennium.NavierStokesIncoherentBandMass
