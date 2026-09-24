import ElementaryHolonics.Millennium.NavierStokesWeightedJointSmoothnessScale
import ElementaryHolonics.Millennium.NavierStokesWeightedUnprojectedPressureScalePath

/-!
# Time-smooth pressure transport on the complete Sobolev scale

**[proved-derived]** The coherent velocity lift is already time-`C∞` at every Sobolev order on
the half-open native aperture.  This owner conducts that returned passage through the genuine
unprojected quadratic convolution and the scale-indexed zero-gauge pressure map.  Both operations
are used as real continuous multilinear passages over the time chart; no coefficientwise jet is
postulated.

The result is a compatible time-smooth pressure tower, including the one-sided initial face.  It
does not by itself assert joint spacetime smoothness; the parameterized Fourier reconstruction is
the separate remaining receiver.
-/

noncomputable section

open Function Set
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedPressureTimeSmoothness

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderTame
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessScale
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPressureScale
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert
open Soma.Holonics.Millennium.NavierStokesWeightedUnprojectedPressureScalePath

/-! ## The complex bilinear source read on the real time chart -/

/-- The arbitrary-order unprojected quadratic passage with both complex-linear ports restricted
to the real scalar field used by the time chart. -/
def unprojectedQuadraticRealBilinear (m : ℕ) :
    PeriodicVectorWeightedSobolev (m + 3) →L[ℝ]
      PeriodicVectorWeightedSobolev (m + 3) →L[ℝ]
        PeriodicVectorWeightedSobolev (m + 2) :=
  (ContinuousLinearMap.restrictScalarsL ℂ
      (PeriodicVectorWeightedSobolev (m + 3))
      (PeriodicVectorWeightedSobolev (m + 2)) ℝ ℝ).comp
    ((periodicVectorWeightedDivergenceConvolutionContinuous
      (m + 3) (by omega)).restrictScalars ℝ)

@[simp]
theorem unprojectedQuadraticRealBilinear_apply
    (m : ℕ) (left right : PeriodicVectorWeightedSobolev (m + 3)) :
    unprojectedQuadraticRealBilinear m left right =
      periodicVectorWeightedDivergenceConvolution
        (m + 3) (by omega) left right :=
  rfl

/-- Endpoint projection of the coherent raw quadratic source before pressure is applied. -/
def unprojectedQuadraticExtensionAtOrder
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ) (t : ℝ) :
    PeriodicVectorWeightedSobolev (m + 2) :=
  unprojectedQuadraticRealBilinear m
    (smoothTowerLiftExtension hT tower m t)
    (smoothTowerLiftExtension hT tower m t)

/-- On the addressed aperture the totalized source is exactly the already returned coherent
source face. -/
theorem unprojectedQuadraticExtensionAtOrder_of_mem
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    unprojectedQuadraticExtensionAtOrder hT tower m t =
      CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder
        tower m ⟨t, ⟨ht.1, ht.2.le⟩⟩ := by
  rw [CoherentWeightedSmoothPathTower.unprojectedQuadraticPathAtOrder_apply]
  unfold unprojectedQuadraticExtensionAtOrder smoothTowerLiftExtension
  rw [unprojectedQuadraticRealBilinear_apply]
  change periodicVectorWeightedDivergenceConvolution (m + 3) (by omega)
      (Set.IccExtend hT (tower.lift m) t)
      (Set.IccExtend hT (tower.lift m) t) = _
  rw [Set.IccExtend_of_mem hT _ ⟨ht.1, ht.2.le⟩]

/-- Every scale-indexed raw quadratic source is genuinely time-`C∞` on the half-open native
aperture, including its one-sided initial face. -/
theorem contDiffOn_infty_unprojectedQuadraticExtensionAtOrder_Ico
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) (m : ℕ) :
    ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (unprojectedQuadraticExtensionAtOrder hT tower m)
      (Ico (0 : ℝ) T) := by
  have hlift := contDiffOn_infty_smoothTowerLiftExtension_Ico
    hT tower nu hnu initial hfixed hreal m
  exact ((unprojectedQuadraticRealBilinear m).contDiff.comp_contDiffOn hlift).clm_apply hlift

/-! ## Elliptic pressure transport -/

/-- The scale-indexed complex pressure passage restricted to the real time chart. -/
def nativePressureRealCLM (m : ℕ) :
    PeriodicVectorWeightedSobolev (m + 2) →L[ℝ]
      PeriodicWeightedSobolev (m + 3) :=
  (nativePressureAtOrder m).restrictScalars ℝ

@[simp]
theorem nativePressureRealCLM_apply
    (m : ℕ) (source : PeriodicVectorWeightedSobolev (m + 2)) :
    nativePressureRealCLM m source = nativePressureAtOrder m source :=
  rfl

/-- Endpoint projection of the complete scale-indexed pressure path. -/
def nativePressureExtensionAtOrder
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ) (t : ℝ) :
    PeriodicWeightedSobolev (m + 3) :=
  nativePressureRealCLM m
    (unprojectedQuadraticExtensionAtOrder hT tower m t)

/-- On the addressed aperture the totalized pressure is exactly the coherent pressure face. -/
theorem nativePressureExtensionAtOrder_of_mem
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    nativePressureExtensionAtOrder hT tower m t =
      CoherentWeightedSmoothPathTower.nativePressurePathAtOrder
        tower m ⟨t, ⟨ht.1, ht.2.le⟩⟩ := by
  unfold nativePressureExtensionAtOrder
  rw [nativePressureRealCLM_apply,
    unprojectedQuadraticExtensionAtOrder_of_mem hT tower m ht]
  rfl

/-- Every scale-indexed zero-gauge pressure is genuinely time-`C∞` on the half-open native
aperture, including its one-sided initial face. -/
theorem contDiffOn_infty_nativePressureExtensionAtOrder_Ico
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) (m : ℕ) :
    ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (nativePressureExtensionAtOrder hT tower m)
      (Ico (0 : ℝ) T) := by
  exact (nativePressureRealCLM m).contDiff.comp_contDiffOn
    (contDiffOn_infty_unprojectedQuadraticExtensionAtOrder_Ico
      hT tower nu hnu initial hfixed hreal m)

section Audit

#print axioms contDiffOn_infty_unprojectedQuadraticExtensionAtOrder_Ico
#print axioms contDiffOn_infty_nativePressureExtensionAtOrder_Ico

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedPressureTimeSmoothness
