import ElementaryHolonics.Millennium.NavierStokesParabolicDirectionCurrent

/-!
# The normalized direction seam enters the physical Hodge modulus

**[proved-derived]** The amplitude-normalized direction law is now transported from the Euclidean
vorticity slice to the exact torus cross-difference population consumed by the dyadic Hodge
reconstruction.  The resulting modulus does not replace the source by a scalar Lipschitz bound:
it retains the receiving magnitude, the translated source magnitude, the signed orientation seam,
and the torus displacement as distinct factors.

This closes the adapter from the weight-one direction law to the existing spatial Hodge owner.  A
terminal theorem still owes a PDE-derived direction coefficient and control of the new
source-magnitude-weighted kernel moment.
-/

noncomputable section

open MeasureTheory Real Set

namespace Soma.Holonics.Millennium.NavierStokesDirectionDepletionModulus

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesParabolicDirectionCurrent

/-- The translated source magnitude paired with its addressed torus displacement. -/
def directionWeightedVorticityModulus
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) : C(SpatialTorus, ℝ) where
  toFun y := ‖torusVorticityEvolution solution t (q - y)‖ * dist y 0
  continuous_toFun := by fun_prop

theorem directionWeightedVorticityModulus_nonneg
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q y : SpatialTorus) :
    0 ≤ directionWeightedVorticityModulus solution t q y :=
  mul_nonneg (norm_nonneg _) dist_nonneg

/-- A Euclidean linear direction-coherence law returns the exact torus cross population with the
receiver magnitude outside and the translated source magnitude retained inside the modulus. -/
theorem openPeriodic_receiverCrossDifference_le_directionCoherence
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) {K : ℝ} (hK : 0 ≤ K)
    (hcoherence : HasLinearDirectionCoherence
      (fun x ↦ vorticityField velocity x t.1) K)
    (q y : SpatialTorus) :
    complexVectorL1
        (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
          (complexTorusVorticitySlice solution t (q - y))) ≤
      (9 * ‖torusVorticityEvolution solution t q‖ * K) *
        directionWeightedVorticityModulus solution t q y := by
  let x : Space := centeredEuclideanRepresentative q
  let displacement : Space := centeredEuclideanRepresentative y
  have hxProjection : euclideanToSpatialTorus x = q :=
    euclideanToSpatialTorus_centeredEuclideanRepresentative q
  have hdisplacementProjection : euclideanToSpatialTorus displacement = y :=
    euclideanToSpatialTorus_centeredEuclideanRepresentative y
  have hxsubProjection : euclideanToSpatialTorus (x - displacement) = q - y := by
    rw [euclideanToSpatialTorus_sub, hxProjection, hdisplacementProjection]
  have hreceiver :
      vorticityField velocity x t.1 = torusVorticityEvolution solution t q := by
    rw [← hxProjection, torusVorticityEvolution_projection]
  have hsource :
      vorticityField velocity (x - displacement) t.1 =
        torusVorticityEvolution solution t (q - y) := by
    rw [← hxsubProjection, torusVorticityEvolution_projection]
  have hdisplacement : ‖displacement‖ ≤ 3 * dist y 0 :=
    norm_centeredEuclideanRepresentative_le_three_mul_dist y
  have hcross :=
    complexVectorL1_receiverCrossDifference_le_of_hasLinearDirectionCoherence
      hcoherence x (x - displacement)
  have hleft : x - (x - displacement) = displacement := by abel
  rw [hleft, hreceiver, hsource] at hcross
  change
    complexVectorL1
        (receiverCrossDifference
          (complexOfRealSpace (torusVorticityEvolution solution t q))
          (complexOfRealSpace (torusVorticityEvolution solution t (q - y)))) ≤ _
  calc
    complexVectorL1
        (receiverCrossDifference
          (complexOfRealSpace (torusVorticityEvolution solution t q))
          (complexOfRealSpace (torusVorticityEvolution solution t (q - y)))) ≤
      3 * ((‖torusVorticityEvolution solution t q‖ *
          ‖torusVorticityEvolution solution t (q - y)‖) *
        (K * ‖displacement‖)) := hcross
    _ ≤ 3 * ((‖torusVorticityEvolution solution t q‖ *
          ‖torusVorticityEvolution solution t (q - y)‖) *
        (K * (3 * dist y 0))) := by
      gcongr
    _ = (9 * ‖torusVorticityEvolution solution t q‖ * K) *
        directionWeightedVorticityModulus solution t q y := by
      simp only [directionWeightedVorticityModulus, ContinuousMap.coe_mk]
      ring

/-- The physical solution occurrence now inhabits the existing general Hodge-modulus interface
whenever its normalized direction seam has the declared linear coefficient. -/
def openPeriodicDirectionDepletionModulus
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) {K : ℝ} (hK : 0 ≤ K)
    (hcoherence : HasLinearDirectionCoherence
      (fun x ↦ vorticityField velocity x t.1) K) :
    OpenPeriodicSpatialCrossModulus solution t q where
  modulus := directionWeightedVorticityModulus solution t q
  constant := 9 * ‖torusVorticityEvolution solution t q‖ * K
  constant_nonneg := mul_nonneg
    (mul_nonneg (by norm_num) (norm_nonneg _)) hK
  modulus_nonneg := directionWeightedVorticityModulus_nonneg solution t q
  cross_le := openPeriodic_receiverCrossDifference_le_directionCoherence
    solution t hK hcoherence q

/-- The direction-depleted cross population enters each exact dyadic Hodge scale.  The unresolved
quantity is now displayed without collapse: a kernel moment weighted by translated vorticity
magnitude and displacement. -/
theorem openPeriodicDyadicSpatialCrossCoherenceMass_le_directionMoment
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) {K : ℝ} (hK : 0 ≤ K)
    (hcoherence : HasLinearDirectionCoherence
      (fun x ↦ vorticityField velocity x t.1) K)
    (scale : ℕ) :
    openPeriodicDyadicSpatialCrossCoherenceMass solution t q scale ≤
      (9 * ‖torusVorticityEvolution solution t q‖ * K) *
        dyadicHodgeJacobianKernelModulusMoment
          (directionWeightedVorticityModulus solution t q) scale := by
  exact openPeriodicDyadicSpatialCrossCoherenceMass_le_modulusMoment
    solution t q
      (openPeriodicDirectionDepletionModulus solution t q hK hcoherence) scale

section Audit

#print axioms directionWeightedVorticityModulus_nonneg
#print axioms openPeriodic_receiverCrossDifference_le_directionCoherence
#print axioms openPeriodicDirectionDepletionModulus
#print axioms openPeriodicDyadicSpatialCrossCoherenceMass_le_directionMoment

end Audit

end Soma.Holonics.Millennium.NavierStokesDirectionDepletionModulus
