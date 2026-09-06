import ElementaryHolonics.Millennium.NavierStokesWeightedJointSmoothnessScale

/-!
# Second time jet of the native projected velocity field

The scale-indexed projected vector field is differentiated on the complete half-open native
aperture.  The Stokes term receives the order-`m+2` native time jet and the Leray bilinear term
receives both ordered order-`m+1` jets.
-/

noncomputable section

open Function Set Filter
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesVelocitySecondTimeJet

open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessScale
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

theorem hasDerivWithinAt_nativeProjectedVectorFieldExtensionAtOrder_Ico
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (hnu : 0 < (nu : ℝ)) (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) (m : ℕ)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt
      (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m)
      ((nu : ℂ) •
          (∑ coordinate : Fin 3,
            diagonalSecondDerivativeAtOrder m coordinate
              (nativeProjectedVectorFieldExtensionAtOrder hT tower nu (m + 2) t)) -
        ((periodicVectorWeightedLerayDivergenceConvolutionContinuous
          (m + 4) (by omega)).bilinearRestrictScalars ℝ
          (nativeProjectedVectorFieldExtensionAtOrder hT tower nu (m + 1) t)
          (smoothTowerLiftExtension hT tower (m + 1) t) +
        (periodicVectorWeightedLerayDivergenceConvolutionContinuous
          (m + 4) (by omega)).bilinearRestrictScalars ℝ
          (smoothTowerLiftExtension hT tower (m + 1) t)
          (nativeProjectedVectorFieldExtensionAtOrder hT tower nu (m + 1) t)))
      (Ico (0 : ℝ) T) t := by
  let U2 : ℝ → PeriodicVectorWeightedSobolev (m + 5) :=
    smoothTowerLiftExtension hT tower (m + 2)
  let U1 : ℝ → PeriodicVectorWeightedSobolev (m + 4) :=
    smoothTowerLiftExtension hT tower (m + 1)
  have hU2 := hasDerivWithinAt_smoothTowerLiftExtension_vectorField_Ico
    hT tower nu hnu initial hfixed hreal (m + 2) ht
  have hU1 := hasDerivWithinAt_smoothTowerLiftExtension_vectorField_Ico
    hT tower nu hnu initial hfixed hreal (m + 1) ht
  have hsum : HasDerivWithinAt
      (fun tau ↦ ∑ coordinate : Fin 3,
        diagonalSecondDerivativeAtOrder m coordinate (U2 tau))
      (∑ coordinate : Fin 3,
        diagonalSecondDerivativeAtOrder m coordinate
          (nativeProjectedVectorFieldExtensionAtOrder hT tower nu (m + 2) t))
      (Ico (0 : ℝ) T) t := by
    exact HasDerivWithinAt.sum (u := Finset.univ) (fun coordinate _ ↦ by
      let D := (diagonalSecondDerivativeAtOrder m coordinate).restrictScalars ℝ
      have hD : HasDerivWithinAt (fun _ : ℝ ↦ D)
          (0 : PeriodicVectorWeightedSobolev (m + 5) →L[ℝ]
            PeriodicVectorWeightedSobolev (m + 3))
          (Ico (0 : ℝ) T) t :=
        hasDerivWithinAt_const t (Ico (0 : ℝ) T) D
      simpa [D] using hD.clm_apply hU2)
  have hvisc := hsum.const_smul (nu : ℂ)
  let B : PeriodicVectorWeightedSobolev (m + 4) →L[ℝ]
      PeriodicVectorWeightedSobolev (m + 4) →L[ℝ]
        PeriodicVectorWeightedSobolev (m + 3) :=
    (periodicVectorWeightedLerayDivergenceConvolutionContinuous
      (m + 4) (by omega)).bilinearRestrictScalars ℝ
  have hBfixed : HasDerivWithinAt (fun _ : ℝ ↦ B)
      (0 : PeriodicVectorWeightedSobolev (m + 4) →L[ℝ]
        PeriodicVectorWeightedSobolev (m + 4) →L[ℝ]
          PeriodicVectorWeightedSobolev (m + 3))
      (Ico (0 : ℝ) T) t :=
    hasDerivWithinAt_const t (Ico (0 : ℝ) T) B
  have hBU := hBfixed.clm_apply hU1
  have hsource := hBU.clm_apply hU1
  have htotal := hvisc.sub hsource
  have hfun :
      (fun tau ↦ nativeProjectedVectorFieldExtensionAtOrder hT tower nu m tau) =ᶠ[
        nhdsWithin t (Ico (0 : ℝ) T)]
        ((fun tau ↦ (nu : ℂ) • ∑ coordinate,
          (diagonalSecondDerivativeAtOrder m coordinate) (U2 tau)) -
          (fun tau ↦ (B (U1 tau)) (U1 tau))) := by
    filter_upwards [] with tau
    rfl
  have hnew := htotal.congr_of_eventuallyEq hfun (by rfl)
  simpa only [U2, U1, B,
    ContinuousLinearMap.bilinearRestrictScalars_apply_apply,
    periodicVectorWeightedLerayDivergenceConvolutionContinuous_apply,
    zero_apply, zero_add, add_zero] using hnew

theorem hasDerivAt_nativeProjectedVectorFieldExtensionAtOrder
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (hnu : 0 < (nu : ℝ)) (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) (m : ℕ)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m)
      ((nu : ℂ) •
          (∑ coordinate : Fin 3,
            diagonalSecondDerivativeAtOrder m coordinate
              (nativeProjectedVectorFieldExtensionAtOrder hT tower nu (m + 2) t)) -
        ((periodicVectorWeightedLerayDivergenceConvolutionContinuous
          (m + 4) (by omega)).bilinearRestrictScalars ℝ
          (nativeProjectedVectorFieldExtensionAtOrder hT tower nu (m + 1) t)
          (smoothTowerLiftExtension hT tower (m + 1) t) +
        (periodicVectorWeightedLerayDivergenceConvolutionContinuous
          (m + 4) (by omega)).bilinearRestrictScalars ℝ
          (smoothTowerLiftExtension hT tower (m + 1) t)
          (nativeProjectedVectorFieldExtensionAtOrder hT tower nu (m + 1) t))) t := by
  apply (hasDerivWithinAt_nativeProjectedVectorFieldExtensionAtOrder_Ico
    hT tower nu hnu initial hfixed hreal m ⟨ht.1.le, ht.2⟩).hasDerivAt
  exact Ico_mem_nhds ht.1 ht.2

#print axioms hasDerivWithinAt_nativeProjectedVectorFieldExtensionAtOrder_Ico
#print axioms hasDerivAt_nativeProjectedVectorFieldExtensionAtOrder

end Soma.Holonics.Millennium.NavierStokesVelocitySecondTimeJet
