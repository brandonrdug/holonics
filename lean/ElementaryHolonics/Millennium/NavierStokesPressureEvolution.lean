import ElementaryHolonics.Millennium.NavierStokesWeightedPressureTimeSmoothness

/-!
# Time evolution of scale-indexed native pressure

The pressure derivative is obtained by differentiating the actual two-sided quadratic source on
the half-open native aperture.  Both ordered Leibniz terms are retained before the bounded
elliptic pressure map is applied.
-/

noncomputable section

open Function Set Filter
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesPressureEvolution

open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessScale
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedPressureTimeSmoothness
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- The actual ordered quadratic pressure time source, including its elliptic reconstruction. -/
def pressureTimeJetAtOrder
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) (m : ℕ) (t : ℝ) :
    PeriodicWeightedSobolev (m + 3) :=
  nativePressureRealCLM m
    (unprojectedQuadraticRealBilinear m
      (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m t)
      (smoothTowerLiftExtension hT tower m t) +
    unprojectedQuadraticRealBilinear m
      (smoothTowerLiftExtension hT tower m t)
      (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m t))

theorem hasDerivWithinAt_nativePressureExtensionAtOrder_Ico
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (m : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt
      (fun tau ↦ nativePressureExtensionAtOrder hT tower m tau)
      (nativePressureRealCLM m
        (unprojectedQuadraticRealBilinear m
          (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m t)
          (smoothTowerLiftExtension hT tower m t) +
        unprojectedQuadraticRealBilinear m
          (smoothTowerLiftExtension hT tower m t)
          (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m t)))
      (Ico (0 : ℝ) T) t := by
  let B : PeriodicVectorWeightedSobolev (m + 3) →L[ℝ]
      PeriodicVectorWeightedSobolev (m + 3) →L[ℝ]
        PeriodicVectorWeightedSobolev (m + 2) := unprojectedQuadraticRealBilinear m
  let P : PeriodicVectorWeightedSobolev (m + 2) →L[ℝ]
      PeriodicWeightedSobolev (m + 3) := nativePressureRealCLM m
  let U : ℝ → PeriodicVectorWeightedSobolev (m + 3) :=
    smoothTowerLiftExtension hT tower m
  let Ut : ℝ → PeriodicVectorWeightedSobolev (m + 3) :=
    nativeProjectedVectorFieldExtensionAtOrder hT tower nu m
  have hU := hasDerivWithinAt_smoothTowerLiftExtension_vectorField_Ico
    hT tower nu hnu initial hfixed hreal m ht
  have hBfixed : HasDerivWithinAt (fun _ : ℝ ↦ B)
      (0 : PeriodicVectorWeightedSobolev (m + 3) →L[ℝ]
        PeriodicVectorWeightedSobolev (m + 3) →L[ℝ]
          PeriodicVectorWeightedSobolev (m + 2))
      (Ico (0 : ℝ) T) t :=
    hasDerivWithinAt_const t (Ico (0 : ℝ) T) B
  have hBU : HasDerivWithinAt (fun tau ↦ B (U tau))
      (B (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m t))
      (Ico (0 : ℝ) T) t := by
    simpa using hBfixed.clm_apply hU
  have hBUUt := hBU.clm_apply hU
  have hsource : HasDerivWithinAt
      (fun tau ↦ B (U tau) (U tau))
      (B (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m t)
          (smoothTowerLiftExtension hT tower m t) +
        B (smoothTowerLiftExtension hT tower m t)
          (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m t))
      (Ico (0 : ℝ) T) t := by
    simpa [U, Ut, B] using hBUUt
  have hPfixed : HasDerivWithinAt (fun _ : ℝ ↦ P)
      (0 : PeriodicVectorWeightedSobolev (m + 2) →L[ℝ]
        PeriodicWeightedSobolev (m + 3))
      (Ico (0 : ℝ) T) t :=
    hasDerivWithinAt_const t (Ico (0 : ℝ) T) P
  have hpressure := hPfixed.clm_apply hsource
  change HasDerivWithinAt
    (fun tau ↦ P (B (U tau) (U tau))) _ _ _
  simpa [P, U, Ut, B] using hpressure

theorem hasDerivAt_nativePressureExtensionAtOrder
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (m : ℕ) {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun tau ↦ nativePressureExtensionAtOrder hT tower m tau)
      (nativePressureRealCLM m
        (unprojectedQuadraticRealBilinear m
          (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m t)
          (smoothTowerLiftExtension hT tower m t) +
        unprojectedQuadraticRealBilinear m
          (smoothTowerLiftExtension hT tower m t)
          (nativeProjectedVectorFieldExtensionAtOrder hT tower nu m t))) t := by
  apply (hasDerivWithinAt_nativePressureExtensionAtOrder_Ico
    hT tower nu hnu initial hfixed hreal m ⟨ht.1.le, ht.2⟩).hasDerivAt
  exact Ico_mem_nhds ht.1 ht.2

#print axioms hasDerivWithinAt_nativePressureExtensionAtOrder_Ico
#print axioms hasDerivAt_nativePressureExtensionAtOrder

end Soma.Holonics.Millennium.NavierStokesPressureEvolution
