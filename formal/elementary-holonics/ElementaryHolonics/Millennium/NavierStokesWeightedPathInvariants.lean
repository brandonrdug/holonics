import ElementaryHolonics.Millennium.NavierStokesWeightedDivergenceFree
import ElementaryHolonics.Millennium.NavierStokesWeightedReality

/-!
# Real and incompressible fibres of the native restart path

**[proved-derived]** A physical restart path is not merely a bounded complex coefficient path.
Every time face must remain in the conjugate-symmetric real fibre and in the modewise
incompressible fibre.  This owner lifts both state predicates to the complete path carrier and
proves that the linear heat path and actual Bochner Duhamel path carry the appropriate incidences.

Reality of the nonlinear return requires reality of the incoming path because convolution sees
its inputs.  Incompressibility of the nonlinear return is stronger: the Leray face imposes it for
unrestricted inputs.  No fixed-point or spatial reconstruction conclusion is asserted here.
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants

open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- Every addressed time face of a native path represents a real Fourier field. -/
def IsWeightedFourierRealPath {T : ℝ} (path : WeightedH3Path T) : Prop :=
  ∀ t, IsWeightedFourierReal 3 (path t)

/-- Every addressed time face of a native path is modewise incompressible. -/
def IsWeightedDivergenceFreePath {T : ℝ} (path : WeightedH3Path T) : Prop :=
  ∀ t, IsModewiseDivergenceFree (path t)

/-- Evaluation at one addressed time face as a bounded linear receiver on path space. -/
def weightedPathEvaluation {T : ℝ} (t : Icc (0 : ℝ) T) :
    WeightedH3Path T →L[ℂ] PeriodicVectorWeightedSobolev 3 :=
  LinearMap.mkContinuous
    { toFun := fun path ↦ path t
      map_add' := by
        intro left right
        rfl
      map_smul' := by
        intro scalar path
        rfl }
    1 (fun path ↦ by
      calc
        ‖path t‖ ≤ ‖path‖ := path.norm_coe_le_norm t
        _ = 1 * ‖path‖ := by ring)

@[simp]
theorem weightedPathEvaluation_apply
    {T : ℝ} (t : Icc (0 : ℝ) T) (path : WeightedH3Path T) :
    weightedPathEvaluation t path = path t :=
  rfl

/-- The complete population of Fourier-real paths is a closed fibre of the Banach path carrier. -/
theorem isClosed_setOf_isWeightedFourierRealPath (T : ℝ) :
    IsClosed {path : WeightedH3Path T | IsWeightedFourierRealPath path} := by
  have hclosed : IsClosed (⋂ t : Icc (0 : ℝ) T,
      (weightedPathEvaluation t) ⁻¹'
        {state : PeriodicVectorWeightedSobolev 3 |
          IsWeightedFourierReal 3 state}) := by
    apply isClosed_iInter
    intro t
    exact (isClosed_setOf_isWeightedFourierReal 3).preimage
      (weightedPathEvaluation t).continuous
  convert hclosed using 1
  ext path
  simp [IsWeightedFourierRealPath]

/-- The zero seed belongs to the Fourier-real path fibre. -/
theorem isWeightedFourierRealPath_zero (T : ℝ) :
    IsWeightedFourierRealPath (0 : WeightedH3Path T) := by
  intro t
  simpa only [ContinuousMap.zero_apply] using isWeightedFourierReal_zero 3

/-- Endpoint projection retains the real-fibre incidence of a path on the closed aperture. -/
theorem IsWeightedFourierRealPath.extension
    {T : ℝ} {path : WeightedH3Path T}
    (hpath : IsWeightedFourierRealPath path) (hT : 0 ≤ T) (t : ℝ) :
    IsWeightedFourierReal 3 (weightedPathExtension hT path t) := by
  change IsWeightedFourierReal 3 (path (Set.projIcc 0 T hT t))
  exact hpath _

/-- Endpoint projection likewise retains modewise incompressibility. -/
theorem IsWeightedDivergenceFreePath.extension
    {T : ℝ} {path : WeightedH3Path T}
    (hpath : IsWeightedDivergenceFreePath path) (hT : 0 ≤ T) (t : ℝ) :
    IsModewiseDivergenceFree (weightedPathExtension hT path t) := by
  change IsModewiseDivergenceFree (path (Set.projIcc 0 T hT t))
  exact hpath _

/-- A real initial state generates a real linear heat path. -/
theorem isWeightedFourierRealPath_weightedLinearHeatPath
    (nu : ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    {initial : PeriodicVectorWeightedSobolev 3}
    (hinitial : IsWeightedFourierReal 3 initial) :
    IsWeightedFourierRealPath (weightedLinearHeatPath nu hT initial) := by
  intro t
  exact hinitial.periodicVectorWeightedHeat nu (Real.toNNReal t.1)

/-- An incompressible initial state generates an incompressible linear heat path. -/
theorem isWeightedDivergenceFreePath_weightedLinearHeatPath
    (nu : ℝ≥0) {T : ℝ} (hT : 0 ≤ T)
    {initial : PeriodicVectorWeightedSobolev 3}
    (hinitial : IsModewiseDivergenceFree initial) :
    IsWeightedDivergenceFreePath (weightedLinearHeatPath nu hT initial) := by
  intro t
  exact Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree.IsModewiseDivergenceFree.periodicVectorWeightedHeat
    hinitial nu (Real.toNNReal t.1)

/-- The actual Duhamel return of a real path is Fourier real at every terminal face. -/
theorem weightedDuhamelReturn_isWeightedFourierReal
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    {path : WeightedH3Path T} (hpath : IsWeightedFourierRealPath path)
    {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    IsWeightedFourierReal 3 (weightedDuhamelReturn nu hnu hT path t) := by
  unfold weightedDuhamelReturn
  apply isWeightedFourierReal_intervalIntegral 3
  · exact intervalIntegrable_weightedDuhamelIntegrand_path nu hnu hT path ht
  · intro s
    exact isWeightedFourierReal_weightedDuhamelIntegrand nu hnu t
      (weightedPathExtension hT path) (hpath.extension hT) s

/-- Therefore the complete returned Duhamel path remains in the real fibre. -/
theorem isWeightedFourierRealPath_weightedDuhamelPath
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    {path : WeightedH3Path T} (hpath : IsWeightedFourierRealPath path) :
    IsWeightedFourierRealPath (weightedDuhamelPath nu hnu hT path) := by
  intro t
  rw [weightedDuhamelPath_apply]
  exact weightedDuhamelReturn_isWeightedFourierReal nu hnu hT hpath t.2

/-- The complete Duhamel path is modewise incompressible even when its incoming complex path is
not. -/
theorem isWeightedDivergenceFreePath_weightedDuhamelPath
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) {T : ℝ} (hT : 0 ≤ T)
    (path : WeightedH3Path T) :
    IsWeightedDivergenceFreePath (weightedDuhamelPath nu hnu hT path) := by
  intro t
  exact weightedDuhamelPath_divergenceFree nu hnu hT path t

section Audit

#print axioms IsWeightedFourierRealPath.extension
#print axioms isClosed_setOf_isWeightedFourierRealPath
#print axioms isWeightedFourierRealPath_zero
#print axioms isWeightedFourierRealPath_weightedLinearHeatPath
#print axioms isWeightedDivergenceFreePath_weightedLinearHeatPath
#print axioms weightedDuhamelReturn_isWeightedFourierReal
#print axioms isWeightedFourierRealPath_weightedDuhamelPath
#print axioms isWeightedDivergenceFreePath_weightedDuhamelPath

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
