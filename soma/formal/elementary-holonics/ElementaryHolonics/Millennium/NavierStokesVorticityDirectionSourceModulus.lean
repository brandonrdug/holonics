import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionKernelMomentDecay
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# The physical vorticity slice supplies its distance cross modulus

**[proved-derived]** The dyadic Hodge kernel already returns a summable first spatial moment.
This file closes the source-side half of that constitutive passage on every strict-interior time
slice.  A torus displacement is lifted through its centered Euclidean representative; the actual
`C¹` vorticity slice is Lipschitz on one exact compact ball containing the receiver and every such
translated source; and the oriented cross difference is bounded by the product of the receiving
vorticity magnitude, that Lipschitz constant, and torus distance.

The result is pointwise in strict interior time and space.  It constructs the infinite-depth
spatial coherence carrier without postulating a source modulus.  It does not assert a uniform
terminal-time bound for the returned coefficient.
-/

noncomputable section

open Set
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMoment
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelMomentDecay
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionKernelScaleLimit
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

/-! ## A centered lift of the genuine three-torus -/

/-- Subtract the nearest integral lattice occurrence in every coordinate of an arbitrary lift. -/
def centeredEuclideanRepresentative (q : SpatialTorus) : Space :=
  vectorOfCoordinates fun axis =>
    euclideanRepresentative q axis - (round (euclideanRepresentative q axis) : ℝ)

@[simp]
theorem centeredEuclideanRepresentative_apply (q : SpatialTorus) (axis : Fin 3) :
    centeredEuclideanRepresentative q axis =
      euclideanRepresentative q axis - (round (euclideanRepresentative q axis) : ℝ) :=
  rfl

/-- The Euclidean quotient projection respects subtraction exactly. -/
theorem euclideanToSpatialTorus_sub (x y : Space) :
    euclideanToSpatialTorus (x - y) =
      euclideanToSpatialTorus x - euclideanToSpatialTorus y := by
  ext axis
  rfl

/-- Centering changes only the exterior Euclidean chart, not the represented torus occurrence. -/
@[simp]
theorem euclideanToSpatialTorus_centeredEuclideanRepresentative (q : SpatialTorus) :
    euclideanToSpatialTorus (centeredEuclideanRepresentative q) = q := by
  ext axis
  have hrepresentative := congrFun (euclideanToSpatialTorus_representative q) axis
  change
    ((euclideanRepresentative q axis -
        (round (euclideanRepresentative q axis) : ℝ) : ℝ) : UnitAddCircle) = q axis
  rw [← hrepresentative]
  apply AddCommGroup.modEq_iff_eq_mod_zmultiples.mp
  rw [AddCommGroup.modEq_iff_eq_add_zsmul]
  refine ⟨round (euclideanRepresentative q axis), ?_⟩
  simp

/-- Each centered coordinate is exactly the metric face of its circle occurrence. -/
theorem abs_centeredEuclideanRepresentative_apply (q : SpatialTorus) (axis : Fin 3) :
    |centeredEuclideanRepresentative q axis| = ‖q axis‖ := by
  have hrepresentative :
      ((euclideanRepresentative q axis : ℝ) : UnitAddCircle) = q axis := by
    simpa [euclideanToSpatialTorus, piToSpatialTorus] using
      congrFun (euclideanToSpatialTorus_representative q) axis
  rw [centeredEuclideanRepresentative_apply]
  calc
    |euclideanRepresentative q axis - (round (euclideanRepresentative q axis) : ℝ)| =
        ‖((euclideanRepresentative q axis : ℝ) : UnitAddCircle)‖ :=
      UnitAddCircle.norm_eq.symm
    _ = ‖q axis‖ := by rw [hrepresentative]

/-- The Euclidean `L²` norm is bounded by the exact three-coordinate `L¹` receiver. -/
theorem norm_vectorOfCoordinates_le_l1 (v : Fin 3 → ℝ) :
    ‖vectorOfCoordinates v‖ ≤ |v 0| + |v 1| + |v 2| := by
  classical
  have hdecomposition :
      vectorOfCoordinates v =
        ∑ axis : Fin 3, v axis • EuclideanSpace.single axis (1 : ℝ) := by
    ext axis
    fin_cases axis <;> simp [Fin.sum_univ_succ]
  rw [hdecomposition]
  calc
    ‖∑ axis : Fin 3, v axis • EuclideanSpace.single axis (1 : ℝ)‖ ≤
        ∑ axis : Fin 3, ‖v axis • EuclideanSpace.single axis (1 : ℝ)‖ :=
      norm_sum_le _ _
    _ = |v 0| + |v 1| + |v 2| := by
      simp [Fin.sum_univ_succ, norm_smul, Real.norm_eq_abs]
      ring

/-- The centered Euclidean lift costs at most three copies of the torus receiver distance. -/
theorem norm_centeredEuclideanRepresentative_le_three_mul_dist (q : SpatialTorus) :
    ‖centeredEuclideanRepresentative q‖ ≤ 3 * dist q 0 := by
  have hsum := Pi.sum_norm_apply_le_norm q
  norm_num [Fin.sum_univ_succ] at hsum
  calc
    ‖centeredEuclideanRepresentative q‖ ≤
        |centeredEuclideanRepresentative q 0| +
          |centeredEuclideanRepresentative q 1| +
            |centeredEuclideanRepresentative q 2| :=
      norm_vectorOfCoordinates_le_l1 _
    _ = ‖q 0‖ + ‖q 1‖ + ‖q 2‖ := by
      rw [abs_centeredEuclideanRepresentative_apply,
        abs_centeredEuclideanRepresentative_apply,
        abs_centeredEuclideanRepresentative_apply]
    _ ≤ 3 * dist q 0 := by simpa [dist_zero_right, add_assoc] using hsum

/-- Every centered lift lies in the exact radius-`3/2` Euclidean ball. -/
theorem norm_centeredEuclideanRepresentative_le_three_halves (q : SpatialTorus) :
    ‖centeredEuclideanRepresentative q‖ ≤ (3 : ℝ) / 2 := by
  have h0 := abs_sub_round (euclideanRepresentative q 0)
  have h1 := abs_sub_round (euclideanRepresentative q 1)
  have h2 := abs_sub_round (euclideanRepresentative q 2)
  calc
    ‖centeredEuclideanRepresentative q‖ ≤
        |centeredEuclideanRepresentative q 0| +
          |centeredEuclideanRepresentative q 1| +
            |centeredEuclideanRepresentative q 2| :=
      norm_vectorOfCoordinates_le_l1 _
    _ ≤ (3 : ℝ) / 2 := by
      simp only [centeredEuclideanRepresentative_apply]
      linarith

/-! ## The exact compact Lipschitz carrier of one physical slice -/

/-- Compactness returns a finite Lipschitz coefficient for the physical vorticity slice. -/
theorem openPeriodicVorticity_exists_lipschitzOnWith_closedBall
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    ∃ K : ℝ≥0, LipschitzOnWith K
      (fun x ↦ vorticityField velocity x t.1) (Metric.closedBall 0 3) := by
  have hsmoothVelocity : ContDiff ℝ 2 (fun x ↦ velocity x t.1) :=
    (openPeriodicSolutionOn_velocitySlice_contDiff solution t.2).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hsmoothVorticity : ContDiff ℝ 1 (fun x ↦ vorticityField velocity x t.1) :=
    vorticityField_contDiff_one velocity t.1 hsmoothVelocity
  have hlocal : LocallyLipschitzOn (Metric.closedBall (0 : Space) 3)
      (fun x ↦ vorticityField velocity x t.1) :=
    hsmoothVorticity.locallyLipschitz.locallyLipschitzOn
  exact hlocal.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : Space) 3)

/-- One exact, choice-independent-for-use Lipschitz coefficient returned by compactness. -/
def openPeriodicVorticityLipschitzConstant
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) : ℝ≥0 :=
  Classical.choose (openPeriodicVorticity_exists_lipschitzOnWith_closedBall solution t)

/-- The selected coefficient controls the actual vorticity field on the complete radius-three
source/receiver chart used below. -/
theorem openPeriodicVorticityLipschitzOn_closedBall
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) :
    LipschitzOnWith (openPeriodicVorticityLipschitzConstant solution t)
      (fun x ↦ vorticityField velocity x t.1) (Metric.closedBall 0 3) :=
  Classical.choose_spec (openPeriodicVorticity_exists_lipschitzOnWith_closedBall solution t)

/-- Coordinatewise complexification costs at most three copies of the Euclidean norm. -/
theorem complexVectorL1_complexOfRealSpace_le_three_norm (v : Space) :
    complexVectorL1 (complexOfRealSpace v) ≤ 3 * ‖v‖ := by
  have h0 : |v 0| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v (0 : Fin 3)
  have h1 : |v 1| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v (1 : Fin 3)
  have h2 : |v 2| ≤ ‖v‖ := by
    simpa [Real.norm_eq_abs] using PiLp.norm_apply_le v (2 : Fin 3)
  unfold complexVectorL1 complexOfRealSpace
  simp only [Complex.norm_real, Real.norm_eq_abs]
  linarith

/-- Complexification preserves subtraction coordinatewise. -/
theorem complexOfRealSpace_sub (u v : Space) :
    complexOfRealSpace (u - v) = complexOfRealSpace u - complexOfRealSpace v := by
  ext axis
  simp [complexOfRealSpace]

/-- Crossing against a receiver depends only on the source-minus-receiver difference. -/
theorem receiverCrossDifference_eq_cross_sub_self
    (receiver source : ComplexVector) :
    receiverCrossDifference receiver source =
      complexCross receiver (source - receiver) := by
  ext component
  fin_cases component <;>
    simp [receiverCrossDifference, complexCross, crossProduct] <;> ring

/-! ## The returned distance law and infinite-depth carrier -/

/-- **[proved-derived; formal-checked]** The actual source cross difference is linearly bounded by
torus distance.  The coefficient is constructed from the receiving vorticity and the compact
Lipschitz carrier of the same strict-interior physical slice. -/
theorem openPeriodic_receiverCrossDifference_le_distance
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q y : SpatialTorus) :
    complexVectorL1
        (receiverCrossDifference (openPeriodicComplexVorticityAt solution t q)
          (complexTorusVorticitySlice solution t (q - y))) ≤
      (9 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
          (openPeriodicVorticityLipschitzConstant solution t : ℝ)) * dist y 0 := by
  let x : Space := centeredEuclideanRepresentative q
  let displacement : Space := centeredEuclideanRepresentative y
  have hxnorm : ‖x‖ ≤ (3 : ℝ) / 2 :=
    norm_centeredEuclideanRepresentative_le_three_halves q
  have hdisplacementNorm : ‖displacement‖ ≤ (3 : ℝ) / 2 :=
    norm_centeredEuclideanRepresentative_le_three_halves y
  have hxmem : x ∈ Metric.closedBall (0 : Space) 3 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using hxnorm.trans (by norm_num)
  have hxsubmem : x - displacement ∈ Metric.closedBall (0 : Space) 3 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_sub_le x displacement).trans (by linarith)
  have hlipschitz :=
    (openPeriodicVorticityLipschitzOn_closedBall solution t).dist_le_mul
      (x - displacement) hxsubmem x hxmem
  have hvorticityDifference :
      ‖vorticityField velocity (x - displacement) t.1 -
          vorticityField velocity x t.1‖ ≤
        (openPeriodicVorticityLipschitzConstant solution t : ℝ) * ‖displacement‖ := by
    simpa [dist_eq_norm] using hlipschitz
  have hdisplacementDistance : ‖displacement‖ ≤ 3 * dist y 0 :=
    norm_centeredEuclideanRepresentative_le_three_mul_dist y
  have hxProjection : euclideanToSpatialTorus x = q :=
    euclideanToSpatialTorus_centeredEuclideanRepresentative q
  have hdisplacementProjection : euclideanToSpatialTorus displacement = y :=
    euclideanToSpatialTorus_centeredEuclideanRepresentative y
  have hxsubProjection : euclideanToSpatialTorus (x - displacement) = q - y := by
    rw [euclideanToSpatialTorus_sub, hxProjection, hdisplacementProjection]
  have hreceiverReal :
      torusVorticityEvolution solution t q = vorticityField velocity x t.1 := by
    rw [← hxProjection, torusVorticityEvolution_projection]
  have hsourceReal :
      torusVorticityEvolution solution t (q - y) =
        vorticityField velocity (x - displacement) t.1 := by
    rw [← hxsubProjection, torusVorticityEvolution_projection]
  have hsourceDifference :
      complexVectorL1
          (complexTorusVorticitySlice solution t (q - y) -
            openPeriodicComplexVorticityAt solution t q) ≤
        9 * (openPeriodicVorticityLipschitzConstant solution t : ℝ) * dist y 0 := by
    rw [openPeriodicComplexVorticityAt_eq_torusComplexification]
    change
      complexVectorL1
          (complexOfRealSpace (torusVorticityEvolution solution t (q - y)) -
            complexOfRealSpace (torusVorticityEvolution solution t q)) ≤ _
    rw [← complexOfRealSpace_sub, hsourceReal, hreceiverReal]
    calc
      complexVectorL1
          (complexOfRealSpace
            (vorticityField velocity (x - displacement) t.1 -
              vorticityField velocity x t.1)) ≤
          3 * ‖vorticityField velocity (x - displacement) t.1 -
            vorticityField velocity x t.1‖ :=
        complexVectorL1_complexOfRealSpace_le_three_norm _
      _ ≤ 3 *
          ((openPeriodicVorticityLipschitzConstant solution t : ℝ) *
            ‖displacement‖) :=
        mul_le_mul_of_nonneg_left hvorticityDifference (by norm_num)
      _ ≤ 3 *
          ((openPeriodicVorticityLipschitzConstant solution t : ℝ) *
            (3 * dist y 0)) := by
        gcongr
      _ = 9 * (openPeriodicVorticityLipschitzConstant solution t : ℝ) * dist y 0 := by
        ring
  rw [receiverCrossDifference_eq_cross_sub_self]
  calc
    complexVectorL1
        (complexCross (openPeriodicComplexVorticityAt solution t q)
          (complexTorusVorticitySlice solution t (q - y) -
            openPeriodicComplexVorticityAt solution t q)) ≤
      complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
        complexVectorL1
          (complexTorusVorticitySlice solution t (q - y) -
            openPeriodicComplexVorticityAt solution t q) :=
      complexVectorL1_cross_le_mul _ _
    _ ≤ complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
        (9 * (openPeriodicVorticityLipschitzConstant solution t : ℝ) * dist y 0) :=
      mul_le_mul_of_nonneg_left hsourceDifference
        (complexVectorL1_nonneg _)
    _ = (9 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
          (openPeriodicVorticityLipschitzConstant solution t : ℝ)) * dist y 0 := by
      ring

/-- The physical strict-interior slice packaged as the exact distance-modulus carrier consumed by
the dyadic Hodge moment theorem. -/
def openPeriodicVorticityDistanceCrossModulus
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    OpenPeriodicSpatialCrossModulus solution t q :=
  openPeriodicTorusDistancePowerCrossModulus solution t q
    (9 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
      (openPeriodicVorticityLipschitzConstant solution t : ℝ)) 1
    (mul_nonneg
      (mul_nonneg (by norm_num) (complexVectorL1_nonneg _))
      (NNReal.coe_nonneg _))
    (by
      intro y
      simpa only [pow_one] using
        openPeriodic_receiverCrossDifference_le_distance solution t q y)

/-- **Constructed official carrier.** Every strict-interior physical solution occurrence now
inhabits the complete infinite-depth spatial cross-coherence carrier; the source modulus and the
kernel moment summability are both derived. -/
theorem openPeriodicDyadicSpatialCrossCoherenceSummable_inhabited
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    OpenPeriodicDyadicSpatialCrossCoherenceSummable solution t q := by
  exact openPeriodicDyadicSpatialCrossCoherenceSummable_of_modulusMoments
    solution t q (openPeriodicVorticityDistanceCrossModulus solution t q)
      summableDyadicHodgeJacobianKernelDistanceMoments_inhabited

/-- The complete cross-coherence mass retains an exact finite reconstruction bound through the
constructed source coefficient and the full first-moment population of the physical Hodge kernel. -/
theorem openPeriodicFullSpatialCrossCoherenceMass_le_distanceMoments
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    openPeriodicFullSpatialCrossCoherenceMass solution t q ≤
      (9 * complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
        (openPeriodicVorticityLipschitzConstant solution t : ℝ)) *
        ∑' scale : ℕ,
          dyadicHodgeJacobianKernelModulusMoment
            (torusDistancePowerModulus 1) scale := by
  exact openPeriodicFullSpatialCrossCoherenceMass_le_modulusMoments
    solution t q (openPeriodicVorticityDistanceCrossModulus solution t q)
      summableDyadicHodgeJacobianKernelDistanceMoments_inhabited

/-- **Physical receiver closure.** The kinetic-energy-based infinite-depth vortex-stretching
estimate now has no spatial summability hypothesis: both the source modulus and the Hodge moments
are derived from the actual strict-interior solution occurrence. -/
theorem abs_openPeriodicPhysicalVortexStretchingAt_le_constructedSpatialCoherence
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    |openPeriodicPhysicalVortexStretchingAt solution t q| ≤
      ((1458 * Real.pi) *
          Real.sqrt (2 * periodicKineticEnergy velocity t.1)) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 +
        (‖(complexDot (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicComplexVorticityAt solution t q))⁻¹‖ *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) *
            openPeriodicFullSpatialCrossCoherenceMass solution t q) *
          complexVectorL1 (openPeriodicComplexVorticityAt solution t q) ^ 2 := by
  exact abs_openPeriodicPhysicalVortexStretchingAt_le_fullSpatialCrossCoherence_kineticEnergy
    solution t q
      (openPeriodicDyadicSpatialCrossCoherenceSummable_inhabited solution t q)

section Audit

#print axioms euclideanToSpatialTorus_centeredEuclideanRepresentative
#print axioms norm_centeredEuclideanRepresentative_le_three_mul_dist
#print axioms openPeriodicVorticityLipschitzOn_closedBall
#print axioms openPeriodic_receiverCrossDifference_le_distance
#print axioms openPeriodicDyadicSpatialCrossCoherenceSummable_inhabited
#print axioms openPeriodicFullSpatialCrossCoherenceMass_le_distanceMoments
#print axioms abs_openPeriodicPhysicalVortexStretchingAt_le_constructedSpatialCoherence

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
