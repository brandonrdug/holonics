import ElementaryHolonics.Millennium.NavierStokesWeightedFourierReconstruction
import ElementaryHolonics.Millennium.NavierStokesPeriodicFlux

/-!
# Pointwise incompressibility of the native weighted H³ reconstruction

A modewise divergence-free native weighted `H³` state reconstructs to an actual real, spatially
`C¹`, one-periodic Euclidean velocity whose pointwise divergence vanishes.  The proof retains the
complete Fourier population: it unweights the mode constraint, identifies every coordinate
derivative with its full multiplier series, commutes the finite coordinate receiver with that
summable series, and only then applies the real receiver.
-/

noncomputable section

open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesWeightedFourierDivergenceReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Unweighting the native mode constraint -/

/-- The native weighted modewise constraint is exactly the ordinary complex dot-product
constraint on the complete unweighted coefficient population. -/
theorem complexDot_nativeUnweightedComponent_eq_zero
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsModewiseDivergenceFree state) (k : SpatialFrequency) :
    (∑ component : Fin 3,
        (k component : ℂ) * nativeUnweightedComponent state component k) = 0 := by
  have hmode := hstate k
  change (∑ component : Fin 3,
    (k component : ℂ) * state component k) = 0 at hmode
  let scale : ℂ :=
    (((Real.sqrt (periodicSobolevWeight 3 k))⁻¹ : ℝ) : ℂ)
  change (∑ component : Fin 3,
    (k component : ℂ) * (scale * state component k)) = 0
  calc
    (∑ component : Fin 3,
        (k component : ℂ) * (scale * state component k)) =
        scale * (∑ component : Fin 3,
          (k component : ℂ) * state component k) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro component _
      ring
    _ = 0 := by rw [hmode, mul_zero]

/-! ## Trace of the complete differentiated Fourier population -/

/-- Each addressed Fourier mode contributes zero to the trace of the differentiated complex
velocity. -/
theorem sum_spatialDerivativeMultiplier_eq_zero
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsModewiseDivergenceFree state)
    (k : SpatialFrequency) (x : Space) :
    (∑ component : Fin 3,
      2 * Real.pi * Complex.I * (k component) *
        nativeUnweightedComponent state component k *
          euclideanFourierCharacter k x) = 0 := by
  calc
    (∑ component : Fin 3,
      2 * Real.pi * Complex.I * (k component) *
        nativeUnweightedComponent state component k *
          euclideanFourierCharacter k x) =
        (2 * Real.pi * Complex.I) *
          (∑ component : Fin 3,
            (k component : ℂ) *
              nativeUnweightedComponent state component k) *
            euclideanFourierCharacter k x := by
      simp only [Fin.sum_univ_three]
      ring
    _ = 0 := by
      rw [complexDot_nativeUnweightedComponent_eq_zero hstate k]
      ring

/-- Finite coordinate summation commutes with the absolutely summable differentiated population;
the resulting complete complex trace is zero. -/
theorem sum_tsum_spatialDerivativeMultiplier_eq_zero
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsModewiseDivergenceFree state) (x : Space) :
    (∑ component : Fin 3,
      ∑' k : SpatialFrequency,
        2 * Real.pi * Complex.I * (k component) *
          nativeUnweightedComponent state component k *
            euclideanFourierCharacter k x) = 0 := by
  calc
    (∑ component : Fin 3,
      ∑' k : SpatialFrequency,
        2 * Real.pi * Complex.I * (k component) *
          nativeUnweightedComponent state component k *
            euclideanFourierCharacter k x) =
        ∑' k : SpatialFrequency,
          ∑ component : Fin 3,
            2 * Real.pi * Complex.I * (k component) *
              nativeUnweightedComponent state component k *
                euclideanFourierCharacter k x := by
      symm
      exact Summable.tsum_finsetSum (s := Finset.univ)
        (fun component _ ↦
          summable_spatialDerivativeMultiplierSeries
            state component component x)
    _ = 0 := by
      simp_rw [sum_spatialDerivativeMultiplier_eq_zero hstate]
      simp

/-! ## Pointwise Euclidean divergence -/

/-- The trace of the actual real Fréchet derivative of the reconstructed velocity vanishes at
every spatial point. -/
theorem sum_fderiv_reconstructedVelocity_coordinate_eq_zero
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsModewiseDivergenceFree state) (x : Space) :
    (∑ component : Fin 3,
      (fderiv ℝ (reconstructedVelocity state) x
        (EuclideanSpace.single component 1)) component) = 0 := by
  calc
    (∑ component : Fin 3,
      (fderiv ℝ (reconstructedVelocity state) x
        (EuclideanSpace.single component 1)) component) =
        ∑ component : Fin 3,
          fderiv ℝ (fun y : Space ↦ reconstructedVelocity state y component) x
            (EuclideanSpace.single component 1) := by
      apply Finset.sum_congr rfl
      intro component _
      exact fderiv_reconstructedVelocity_apply_component
        state x (EuclideanSpace.single component 1) component
    _ = ∑ component : Fin 3,
        (∑' k : SpatialFrequency,
          2 * Real.pi * Complex.I * (k component) *
            nativeUnweightedComponent state component k *
              euclideanFourierCharacter k x).re := by
      apply Finset.sum_congr rfl
      intro component _
      exact fderiv_reconstructedVelocity_component_apply_single
        state component component x
    _ = (∑ component : Fin 3,
        ∑' k : SpatialFrequency,
          2 * Real.pi * Complex.I * (k component) *
            nativeUnweightedComponent state component k *
              euclideanFourierCharacter k x).re := by
      simp only [Fin.sum_univ_three, Complex.add_re]
    _ = 0 := by
      rw [sum_tsum_spatialDerivativeMultiplier_eq_zero hstate x]
      rfl

/-- A modewise divergence-free native weighted `H³` state reconstructs to a pointwise
divergence-free actual Euclidean velocity. -/
theorem divergence_reconstructedVelocity_eq_zero
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsModewiseDivergenceFree state) (x : Space) :
    divergence (reconstructedVelocity state) x = 0 := by
  rw [← sum_coordinate_fderiv_eq_divergence]
  change (∑ coordinate : Fin 3,
      ((fderiv ℝ (reconstructedVelocity state) x)
        (EuclideanSpace.single coordinate 1)).ofLp coordinate) = 0
  exact sum_fderiv_reconstructedVelocity_coordinate_eq_zero hstate x

/-- The complete reconstruction consequence: the field is real-valued by construction, `C¹`,
one-periodic, and pointwise incompressible. -/
theorem reconstructedVelocity_c1_onePeriodic_divergenceFree
    {state : PeriodicVectorWeightedSobolev 3}
    (hstate : IsModewiseDivergenceFree state) :
    ContDiff ℝ 1 (reconstructedVelocity state) ∧
      IsOnePeriodic (reconstructedVelocity state) ∧
        ∀ x, divergence (reconstructedVelocity state) x = 0 := by
  exact ⟨contDiff_one_reconstructedVelocity state,
    isOnePeriodic_reconstructedVelocity state,
    divergence_reconstructedVelocity_eq_zero hstate⟩

section Audit

#print axioms complexDot_nativeUnweightedComponent_eq_zero
#print axioms sum_tsum_spatialDerivativeMultiplier_eq_zero
#print axioms divergence_reconstructedVelocity_eq_zero
#print axioms reconstructedVelocity_c1_onePeriodic_divergenceFree

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedFourierDivergenceReconstruction
