import ElementaryHolonics.Millennium.NavierStokesWeightedMildRestart
import ElementaryHolonics.Millennium.NavierStokesInvariantQuadraticContraction
import ElementaryHolonics.Millennium.NavierStokesWeightedPathInvariants
import ElementaryHolonics.Millennium.NavierStokesWeightedReality
import ElementaryHolonics.Millennium.NavierStokesWeightedDivergenceFree

/-!
# The Fourier-real and incompressible weighted mild restart

**[proved-derived]** The actual unforced weighted mild map is restricted to the closed fibre of
paths whose every face has exact Fourier conjugate symmetry.  The linear heat path preserves the
real initial occurrence, and the nonlinear Bochner return preserves the real incoming path, so
the cap-selected quadratic contraction returns a Fourier-real fixed point.

Modewise incompressibility is then read directly from that fixed equation.  The linear face is
incompressible because the initial occurrence is, while every Duhamel face is incompressible by
the native Leray return, independently of its input.  Thus the same fixed path carries its norm
ball, initial-face, Fourier-reality, and divergence-free receipts without another assumption or
another fixed-point construction.
-/

noncomputable section

open Function Set
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesWeightedMildInvariantRestart

open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInvariantQuadraticContraction
open Soma.Holonics.Millennium.NavierStokesQuadraticContraction
open Soma.Holonics.Millennium.NavierStokesWeightedDivergenceFree
open Soma.Holonics.Millennium.NavierStokesWeightedDuhamelReturnContinuity
open Soma.Holonics.Millennium.NavierStokesWeightedLinearPath
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The same actual quadratic data -/

/-- The exact analytic data of the cap-selected mild map, before restricting its fixed-point
population to a constitutive fibre. -/
def weightedMildRestartQuadraticData
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (initial : PeriodicVectorWeightedSobolev 3) (hinitial : ‖initial‖ ≤ cap) :
    QuadraticContractionData
      (weightedMildRestartMap nu cap hnu hcap initial)
      (weightedLinearHeatPath (Real.toNNReal nu)
        (weightedRestartTimeFromCap_pos hnu hcap).le initial)
      (weightedDuhamelCoefficient nu (weightedRestartTimeFromCap nu cap))
      (weightedRestartRadiusFromCap cap) := by
  apply quadraticContractionDataOfWeightedRestartCap hnu hcap
  · exact (norm_weightedLinearHeatPath_le (Real.toNNReal nu)
      (weightedRestartTimeFromCap_pos hnu hcap).le initial).trans hinitial
  · intro u
    simpa only [weightedMildRestartMap, Real.coe_toNNReal _ hnu.le] using
      norm_weightedMildMap_sub_linear_le
        (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (weightedRestartTimeFromCap_pos hnu hcap).le initial u
  · intro u v
    simpa only [weightedMildRestartMap, Real.coe_toNNReal _ hnu.le] using
      norm_weightedMildMap_remainder_sub_le
        (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (weightedRestartTimeFromCap_pos hnu hcap).le initial u v

/-! ## Preservation of the closed Fourier-real path fibre -/

/-- The actual mild map carries every Fourier-real input path to another Fourier-real path when
its initial occurrence is Fourier real. -/
theorem mapsTo_weightedMildRestartMap_fourierRealPath
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    {initial : PeriodicVectorWeightedSobolev 3}
    (hinitial : IsWeightedFourierReal 3 initial) :
    MapsTo (weightedMildRestartMap nu cap hnu hcap initial)
      {path : WeightedH3Path (weightedRestartTimeFromCap nu cap) |
        IsWeightedFourierRealPath path}
      {path : WeightedH3Path (weightedRestartTimeFromCap nu cap) |
        IsWeightedFourierRealPath path} := by
  intro path hpath
  have hlinear := isWeightedFourierRealPath_weightedLinearHeatPath
    (Real.toNNReal nu) (weightedRestartTimeFromCap_pos hnu hcap).le hinitial
  have hduhamel := isWeightedFourierRealPath_weightedDuhamelPath
    (Real.toNNReal nu) (real_toNNReal_pos hnu)
      (weightedRestartTimeFromCap_pos hnu hcap).le hpath
  change IsWeightedFourierRealPath
    (weightedLinearHeatPath (Real.toNNReal nu)
      (weightedRestartTimeFromCap_pos hnu hcap).le initial -
      weightedDuhamelPath (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (weightedRestartTimeFromCap_pos hnu hcap).le path)
  intro t
  exact (hlinear t).sub (hduhamel t)

/-! ## Divergence freedom read from the actual fixed equation -/

/-- With incompressible initial data, every face emitted by the actual mild map is modewise
incompressible: this is the subtraction of the divergence-free linear and Duhamel faces. -/
theorem isWeightedDivergenceFreePath_weightedMildRestartMap
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    {initial : PeriodicVectorWeightedSobolev 3}
    (hinitial : IsModewiseDivergenceFree initial)
    (path : WeightedH3Path (weightedRestartTimeFromCap nu cap)) :
    IsWeightedDivergenceFreePath
      (weightedMildRestartMap nu cap hnu hcap initial path) := by
  have hlinear := isWeightedDivergenceFreePath_weightedLinearHeatPath
    (Real.toNNReal nu) (weightedRestartTimeFromCap_pos hnu hcap).le hinitial
  have hduhamel := isWeightedDivergenceFreePath_weightedDuhamelPath
    (Real.toNNReal nu) (real_toNNReal_pos hnu)
      (weightedRestartTimeFromCap_pos hnu hcap).le path
  intro t k
  change weightedModeDivergenceEvaluation 3 k
    (weightedLinearHeatPath (Real.toNNReal nu)
        (weightedRestartTimeFromCap_pos hnu hcap).le initial t -
      weightedDuhamelPath (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (weightedRestartTimeFromCap_pos hnu hcap).le path t) = 0
  rw [map_sub, weightedModeDivergenceEvaluation_apply,
    weightedModeDivergenceEvaluation_apply, hlinear t k, hduhamel t k, sub_self]

/-- Every fixed point of the actual mild restart map is modewise incompressible at every face,
by replacement with its emitted mild-map path. -/
theorem isWeightedDivergenceFreePath_of_fixedPoint_weightedMildRestartMap
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    {initial : PeriodicVectorWeightedSobolev 3}
    (hinitial : IsModewiseDivergenceFree initial)
    {path : WeightedH3Path (weightedRestartTimeFromCap nu cap)}
    (hfixed : IsFixedPt (weightedMildRestartMap nu cap hnu hcap initial) path) :
    IsWeightedDivergenceFreePath path := by
  rw [← hfixed]
  exact isWeightedDivergenceFreePath_weightedMildRestartMap
    hnu hcap hinitial path

/-! ## The physical-fibre fixed-point return -/

/-- **Actual invariant restart return.**  Fourier-real, modewise incompressible initial data below
the common cap return one actual mild fixed path with every analytic and physical-fibre receipt. -/
theorem exists_weightedMildInvariantRestart_fixedPoint
    {nu cap : ℝ} (hnu : 0 < nu) (hcap : 0 ≤ cap)
    (initial : PeriodicVectorWeightedSobolev 3) (hinitialNorm : ‖initial‖ ≤ cap)
    (hinitialReal : IsWeightedFourierReal 3 initial)
    (hinitialDivergenceFree : IsModewiseDivergenceFree initial) :
    ∃ path : WeightedH3Path (weightedRestartTimeFromCap nu cap),
      ‖path‖ ≤ weightedRestartRadiusFromCap cap ∧
        IsFixedPt (weightedMildRestartMap nu cap hnu hcap initial) path ∧
          path ⟨0, ⟨le_rfl, (weightedRestartTimeFromCap_pos hnu hcap).le⟩⟩ = initial ∧
            IsWeightedFourierRealPath path ∧
              IsWeightedDivergenceFreePath path := by
  let realPathFibre : Set (WeightedH3Path (weightedRestartTimeFromCap nu cap)) :=
    {path | IsWeightedFourierRealPath path}
  have hclosed : IsClosed realPathFibre := by
    exact isClosed_setOf_isWeightedFourierRealPath
      (weightedRestartTimeFromCap nu cap)
  have hzero : (0 : WeightedH3Path (weightedRestartTimeFromCap nu cap)) ∈ realPathFibre := by
    exact isWeightedFourierRealPath_zero (weightedRestartTimeFromCap nu cap)
  have hmaps : MapsTo (weightedMildRestartMap nu cap hnu hcap initial)
      realPathFibre realPathFibre := by
    exact mapsTo_weightedMildRestartMap_fourierRealPath hnu hcap hinitialReal
  obtain ⟨path, hnorm, hreal, hfixed⟩ :=
    exists_fixedPoint_mem_restartBall_and_invariant
      (weightedMildRestartQuadraticData hnu hcap initial hinitialNorm)
      hclosed hzero hmaps
  have hinitialFace :
      path ⟨0, ⟨le_rfl, (weightedRestartTimeFromCap_pos hnu hcap).le⟩⟩ = initial := by
    have hface := congrArg
      (fun candidate : WeightedH3Path (weightedRestartTimeFromCap nu cap) ↦
        candidate ⟨0, ⟨le_rfl, (weightedRestartTimeFromCap_pos hnu hcap).le⟩⟩)
      hfixed
    simpa only [weightedMildRestartMap, weightedMildMap_zero] using hface.symm
  have hdivergenceFree :=
    isWeightedDivergenceFreePath_of_fixedPoint_weightedMildRestartMap
      hnu hcap hinitialDivergenceFree hfixed
  exact ⟨path, hnorm, hfixed, hinitialFace, hreal, hdivergenceFree⟩

section Audit

#print axioms weightedMildRestartQuadraticData
#print axioms mapsTo_weightedMildRestartMap_fourierRealPath
#print axioms isWeightedDivergenceFreePath_weightedMildRestartMap
#print axioms isWeightedDivergenceFreePath_of_fixedPoint_weightedMildRestartMap
#print axioms exists_weightedMildInvariantRestart_fixedPoint

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedMildInvariantRestart
