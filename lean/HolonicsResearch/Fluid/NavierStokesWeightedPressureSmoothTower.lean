import HolonicsResearch.Fluid.NavierStokesWeightedPressureTimeSmoothness

/-!
# The scale pressure paths as one coherent vector reconstruction tower

**[proved-derived]** Repeating a scalar pressure state in the three addressed vector slots lets
the established vector-valued Fourier reconstruction passage act without changing any pressure
coefficient.  Exact high-to-low pressure intertwiners supply a coherent smooth path tower, while
the scale pressure time theorem supplies `C∞` time dependence at every level, including the
one-sided initial face.  The order-zero face is identified exactly with the original weighted
path's zero-gauge pressure state.
-/

noncomputable section

open Function Set
open scoped NNReal

namespace Holonics.Fluid.NavierStokesWeightedPressureSmoothTower

open Holonics.Fluid.NavierStokes
open Holonics.Fluid.NavierStokesH3DivergenceBilinear
open Holonics.Fluid.NavierStokesInfiniteFourierHeatH3
open Holonics.Fluid.NavierStokesMildFourierNonlinearity
open Holonics.Fluid.NavierStokesTorusFourier
open Holonics.Fluid.NavierStokesWeightedJointSmoothnessScale
open Holonics.Fluid.NavierStokesWeightedFourierReconstruction
open Holonics.Fluid.NavierStokesWeightedMildRestart
open Holonics.Fluid.NavierStokesWeightedMildSpacetimeMomentum
open Holonics.Fluid.NavierStokesWeightedOrderRestriction
open Holonics.Fluid.NavierStokesWeightedPathInvariants
open Holonics.Fluid.NavierStokesWeightedPathSpace
open Holonics.Fluid.NavierStokesWeightedPressureCoefficient
open Holonics.Fluid.NavierStokesWeightedPressureReconstruction
open Holonics.Fluid.NavierStokesWeightedPressureScale
open Holonics.Fluid.NavierStokesWeightedPressureTimeSmoothness
open Holonics.Fluid.NavierStokesWeightedReality
open Holonics.Fluid.NavierStokesWeightedSmoothPathTower
open Holonics.Fluid.NavierStokesWeightedSobolevHilbert
open Holonics.Fluid.NavierStokesWeightedUnprojectedPressureScalePath

/-- Repeat one scalar native state in all three vector slots at an arbitrary Sobolev order. -/
def scalarDiagonalAtOrder (order : ℕ) :
    PeriodicWeightedSobolev order →L[ℂ]
      PeriodicVectorWeightedSobolev order :=
  ContinuousLinearMap.pi fun _component : Fin 3 ↦
    ContinuousLinearMap.id ℂ (PeriodicWeightedSobolev order)

@[simp]
theorem scalarDiagonalAtOrder_apply
    (order : ℕ) (state : PeriodicWeightedSobolev order)
    (component : Fin 3) :
    scalarDiagonalAtOrder order state component = state :=
  rfl

/-- The order-zero pressure path repeated in vector slots is the base reconstruction carrier. -/
def pressureDiagonalBasePath
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) : WeightedH3Path T where
  toFun t := scalarDiagonalAtOrder 3
    (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower 0 t)
  continuous_toFun := (scalarDiagonalAtOrder 3).continuous.comp
    (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower 0).continuous

/-- All pressure scales, repeated componentwise, form one exact coherent vector path tower. -/
def pressureDiagonalSmoothPathTower
    {T : ℝ} {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) :
    CoherentWeightedSmoothPathTower (pressureDiagonalBasePath tower) where
  lift m :=
    { toFun := fun t ↦ scalarDiagonalAtOrder (m + 3)
          (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower m t)
      continuous_toFun := (scalarDiagonalAtOrder (m + 3)).continuous.comp
        (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower m).continuous }
  restrict_lift := by
    intro m t
    funext component
    change periodicWeightedSobolevRestrict 3 (m + 3) (by omega)
        (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower m t) =
      CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower 0 t
    simpa only [Nat.zero_add, periodicWeightedSobolevRestrictCLM,
      LinearMap.mkContinuous_apply, LinearMap.coe_mk, AddHom.coe_mk] using
      CoherentWeightedSmoothPathTower.restrict_nativePressurePathAtOrder
        tower 0 m (Nat.zero_le m) t

/-- The order-zero pressure scale is exactly the native pressure path already reconstructed from
the base weighted `H³` path. -/
theorem nativePressurePathAtOrder_zero_eq_weighted
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) :
    CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower 0 t =
      weightedNativePressurePath base t := by
  apply periodicWeightedSobolev_eq_of_coefficients_eq
  intro k
  rw [CoherentWeightedSmoothPathTower.nativePressurePathAtOrder_coefficient_eq_base,
    weightedNativePressurePath_apply hT,
    weightedSobolevCoefficients_weightedNativePressure]
  unfold weightedPressureCoefficient weightedUnprojectedDivergenceMode
  rw [weightedPathExtension_of_mem hT base t.2]

/-- Consequently the synthetic pressure-tower velocity component is exactly the actual real
zero-gauge pressure reconstructed from the original weighted path. -/
theorem reconstructedVelocity_pressureDiagonal_eq_pressure
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (t : Icc (0 : ℝ) T) (x : Space) :
    (pressureDiagonalSmoothPathTower tower).reconstructedVelocity t x 0 =
      weightedReconstructedPressure hT base t.1 x := by
  rw [CoherentWeightedSmoothPathTower.reconstructedVelocity_eq_base]
  change
    reconstructedVelocity
        (scalarNativeDiagonalVector
          (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower 0 t)) x 0 = _
  rw [nativePressurePathAtOrder_zero_eq_weighted hT tower t]
  rw [weightedNativePressurePath_apply hT]
  rfl

/-- Every lift of the synthetic pressure tower has genuine time-`C∞` endpoint extension on the
half-open aperture. -/
theorem contDiffOn_infty_pressureDiagonalLiftExtension_Ico
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ))
    (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base) (m : ℕ) :
    ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (fun t ↦ smoothTowerLiftExtension hT
        (pressureDiagonalSmoothPathTower tower) m t)
      (Ico (0 : ℝ) T) := by
  have hsmooth : ContDiffOn ℝ ((↑(⊤ : ℕ∞)) : WithTop ℕ∞)
      (fun t ↦ scalarDiagonalAtOrder (m + 3)
        (nativePressureExtensionAtOrder hT tower m t))
      (Ico (0 : ℝ) T) :=
    ((scalarDiagonalAtOrder (m + 3)).restrictScalars ℝ).contDiff.comp_contDiffOn
      (contDiffOn_infty_nativePressureExtensionAtOrder_Ico
        hT tower nu hnu initial hfixed hreal m)
  apply hsmooth.congr
  intro t ht
  unfold smoothTowerLiftExtension
  change Set.IccExtend hT
      ((pressureDiagonalSmoothPathTower tower).lift m) t = _
  rw [Set.IccExtend_of_mem hT _ ⟨ht.1, ht.2.le⟩]
  change scalarDiagonalAtOrder (m + 3)
      (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower m
        ⟨t, ⟨ht.1, ht.2.le⟩⟩) = _
  rw [nativePressureExtensionAtOrder_of_mem hT tower m ht]

section Audit

#print axioms pressureDiagonalSmoothPathTower
#print axioms nativePressurePathAtOrder_zero_eq_weighted
#print axioms reconstructedVelocity_pressureDiagonal_eq_pressure
#print axioms contDiffOn_infty_pressureDiagonalLiftExtension_Ico

end Audit

end Holonics.Fluid.NavierStokesWeightedPressureSmoothTower
