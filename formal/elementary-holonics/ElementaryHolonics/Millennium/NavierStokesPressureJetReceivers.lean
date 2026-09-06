import ElementaryHolonics.Millennium.NavierStokesPressureEvolution
import ElementaryHolonics.Millennium.NavierStokesWeightedPressureSmoothTower
import ElementaryHolonics.Millennium.NavierStokesWeightedReconstructionContinuity

/-!
# Bounded pressure-jet receivers carry the actual time source

Ordered spatial derivatives, full Fourier reconstruction and point evaluation compose as one
bounded linear receiver. The derivative-word compatibility is the actual spatial derivative
identity, and the actual pressure evolution crosses the receiver even at the initial right face.
-/

noncomputable section
open Function Set Filter
open scoped Topology NNReal

namespace Soma.Holonics.Millennium.NavierStokesPressureJetReceivers
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedReconstructionContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedPressureReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedPressureScale
open Soma.Holonics.Millennium.NavierStokesWeightedPressureTimeSmoothness
open Soma.Holonics.Millennium.NavierStokesWeightedPressureSmoothTower
open Soma.Holonics.Millennium.NavierStokesWeightedUnprojectedPressureScalePath
open Soma.Holonics.Millennium.NavierStokesWeightedOrderRestriction
open Soma.Holonics.Millennium.NavierStokesWeightedMildSpacetimeMomentum
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesPressureEvolution

def pressureWordComplexReceiver (m r : ℕ) (hr : r ≤ m)
    (word : Fin r → Fin 3) (x : Space) : PeriodicWeightedSobolev (m + 3) →L[ℂ] ℂ :=
  (ContinuousMap.evalCLM ℂ (euclideanToSpatialTorus x)).comp
    ((reconstructedTorusComplexComponentCLM 0).comp
      ((finiteOrderVectorDerivativeToThree m r hr word).comp (scalarDiagonalAtOrder (m + 3))))

def pressureWordReceiver (m r : ℕ) (hr : r ≤ m)
    (word : Fin r → Fin 3) (x : Space) : PeriodicWeightedSobolev (m + 3) →L[ℝ] ℝ :=
  Complex.reCLM.comp ((pressureWordComplexReceiver m r hr word x).restrictScalars ℝ)

theorem pressureWordReceiver_apply (m r : ℕ) (hr : r ≤ m)
    (word : Fin r → Fin 3) (x : Space) (state : PeriodicWeightedSobolev (m + 3)) :
    pressureWordReceiver m r hr word x state =
      reconstructedFiniteOrderRealComponent m r hr word
        (scalarDiagonalAtOrder (m + 3) state) 0 x := rfl

/-- The empty derivative word is the actual physical zero-gauge pressure of the same path. -/
theorem pressureWordReceiver_zero_eq_physical_pressure
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (m : ℕ) (x : Space)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    pressureWordReceiver m 0 (Nat.zero_le m) (fun i ↦ Fin.elim0 i) x
      (nativePressureExtensionAtOrder hT tower m t) =
      weightedReconstructedPressure hT base t x := by
  let τ : Icc (0 : ℝ) T := ⟨t, ⟨ht.1, ht.2.le⟩⟩
  rw [pressureWordReceiver_apply, nativePressureExtensionAtOrder_of_mem hT tower m ht]
  unfold reconstructedFiniteOrderRealComponent reconstructedFiniteOrderComplexComponent
    reconstructedFiniteOrderTorusComplexComponent
  rw [finiteOrderVectorDerivativeToThree_zero]
  have hrestrict := (pressureDiagonalSmoothPathTower tower).restrict_lift m τ
  change periodicVectorWeightedSobolevRestrictCLM 3 (m + 3) (by omega)
      (scalarDiagonalAtOrder (m + 3)
        (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower m τ)) =
    scalarDiagonalAtOrder 3 (CoherentWeightedSmoothPathTower.nativePressurePathAtOrder tower 0 τ)
      at hrestrict
  rw [hrestrict, nativePressurePathAtOrder_zero_eq_weighted hT tower τ,
    weightedNativePressurePath_apply hT]
  rfl

/-- Prepending a coordinate differentiates the same fully reconstructed scalar field. -/
theorem pressureWordReceiver_spatial_derivative
    (m r : ℕ) (hr : r + 1 ≤ m) (word : Fin r → Fin 3)
    (state : PeriodicWeightedSobolev (m + 3)) (coordinate : Fin 3) (x : Space) :
    fderiv ℝ (fun y ↦ pressureWordReceiver m r (by omega) word y state) x
      (EuclideanSpace.single coordinate 1) =
      pressureWordReceiver m (r + 1) hr (Fin.cons coordinate word) x state :=
  fderiv_reconstructedFiniteOrderRealComponent_apply_single m r hr word
    (scalarDiagonalAtOrder (m + 3) state) 0 coordinate x

/-- The initial right derivative uses the same bounded receiver on the actual pressure source. -/
theorem pressureWordReceiver_hasDerivWithinAt_Ico
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3) (x : Space)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    HasDerivWithinAt
      (fun τ ↦ pressureWordReceiver m r hr word x (nativePressureExtensionAtOrder hT tower m τ))
      (pressureWordReceiver m r hr word x (pressureTimeJetAtOrder hT tower nu m t))
      (Ico (0 : ℝ) T) t := by
  have hp := hasDerivWithinAt_nativePressureExtensionAtOrder_Ico
    hT tower nu hnu initial hfixed hreal m ht
  have hL := hasDerivWithinAt_const t (Ico (0 : ℝ) T) (pressureWordReceiver m r hr word x)
  simpa [pressureTimeJetAtOrder] using hL.clm_apply hp

theorem pressureWordReceiver_hasDerivAt
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (m r : ℕ) (hr : r ≤ m) (word : Fin r → Fin 3) (x : Space)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt
      (fun τ ↦ pressureWordReceiver m r hr word x (nativePressureExtensionAtOrder hT tower m τ))
      (pressureWordReceiver m r hr word x (pressureTimeJetAtOrder hT tower nu m t)) t :=
  (pressureWordReceiver_hasDerivWithinAt_Ico hT tower nu hnu initial hfixed hreal
    m r hr word x ⟨ht.1.le, ht.2⟩).hasDerivAt (Ico_mem_nhds ht.1 ht.2)

#print axioms pressureWordReceiver_spatial_derivative
#print axioms pressureWordReceiver_zero_eq_physical_pressure
#print axioms pressureWordReceiver_hasDerivWithinAt_Ico
#print axioms pressureWordReceiver_hasDerivAt
end Soma.Holonics.Millennium.NavierStokesPressureJetReceivers
