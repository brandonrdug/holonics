import ElementaryHolonics.Millennium.NavierStokesCriticalSourceTimeJet

/-!
# Exact native bound for the nonlinear-source time jet

**[proved-derived; formal-checked]**  The oriented source jet already has the exact Leibniz
population `B(u_t,u) + B(u,u_t)`.  Applying the standing native bilinear estimate only after that
identity gives its sharpest currently owned `H3 × H3 → H2` norm bound.

This theorem introduces no terminal premise.  It identifies the precise existing norm population
whose uniform or time-integrated control would make the local Dini estimates terminal-uniform.
No such global control is claimed here.
-/

noncomputable section

open Set
open scoped ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesCriticalSourceTimeJetBound

open Soma.Holonics.Millennium.NavierStokesCriticalSourceTimeJet
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesWeightedJointSmoothnessBootstrap
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- **Exact currently-owned source-jet estimate.**  The velocity and its genuine native PDE time
jet remain separately visible.  The estimate is pointwise on the totalized restart chart and
therefore introduces no compact supremum, endpoint trace, or terminal hypothesis. -/
theorem norm_nativeSharpSourceTimeJet_le_velocity_mul_timeJet
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0)
    (t : ℝ) :
    ‖nativeSharpSourceTimeJet hT tower nu t‖ ≤
      2 * (23328 * periodicH3EmbeddingConstant) *
        ‖weightedPathExtension hT base t‖ *
        ‖weightedPathExtension hT
          (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu) t‖ := by
  let velocity := weightedPathExtension hT base t
  let timeJet := weightedPathExtension hT
    (CoherentWeightedSmoothPathTower.nativeProjectedTimeDerivativePath tower nu) t
  change
    ‖weightedLerayDivergenceConvolution timeJet velocity +
        weightedLerayDivergenceConvolution velocity timeJet‖ ≤
      2 * (23328 * periodicH3EmbeddingConstant) * ‖velocity‖ * ‖timeJet‖
  calc
    ‖weightedLerayDivergenceConvolution timeJet velocity +
        weightedLerayDivergenceConvolution velocity timeJet‖ ≤
      ‖weightedLerayDivergenceConvolution timeJet velocity‖ +
        ‖weightedLerayDivergenceConvolution velocity timeJet‖ := norm_add_le _ _
    _ ≤
      (23328 * periodicH3EmbeddingConstant) * ‖timeJet‖ * ‖velocity‖ +
        (23328 * periodicH3EmbeddingConstant) * ‖velocity‖ * ‖timeJet‖ :=
      add_le_add
        (norm_weightedLerayDivergenceConvolution_le timeJet velocity)
        (norm_weightedLerayDivergenceConvolution_le velocity timeJet)
    _ = 2 * (23328 * periodicH3EmbeddingConstant) * ‖velocity‖ * ‖timeJet‖ := by
      ring

section Audit

#print axioms norm_nativeSharpSourceTimeJet_le_velocity_mul_timeJet

end Audit

end Soma.Holonics.Millennium.NavierStokesCriticalSourceTimeJetBound
