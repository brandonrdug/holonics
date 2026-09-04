import ElementaryHolonics.Millennium.NavierStokesWeightedReconstructionContinuity
import ElementaryHolonics.Millennium.NavierStokesWeightedPathInvariants

/-!
# A native path reconstructs as one joint spacetime occurrence

**[proved-derived]** Continuity of the native `H³` path and boundedness of inverse Fourier
reconstruction compose before evaluation.  The result is joint continuity in time and torus
position, and, under the retained Fourier-reality fibre, a joint real Euclidean velocity field.
This is the spacetime receiver needed before differentiability and the modal equation may be
promoted to a classical PDE carrier.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesWeightedSpacetimeReconstruction

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedReconstructionContinuity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-- Reconstruction of one component along the complete native time path, valued in the uniform
continuous-map carrier before point evaluation. -/
def reconstructedTorusComplexComponentPath
    {T : ℝ} (path : WeightedH3Path T) (component : Fin 3) :
    C(Icc (0 : ℝ) T, C(SpatialTorus, ℂ)) where
  toFun t := reconstructedTorusComplexComponentCLM component (path t)
  continuous_toFun :=
    (reconstructedTorusComplexComponentCLM component).continuous.comp path.continuous

@[simp]
theorem reconstructedTorusComplexComponentPath_apply
    {T : ℝ} (path : WeightedH3Path T) (component : Fin 3)
    (t : Icc (0 : ℝ) T) :
    reconstructedTorusComplexComponentPath path component t =
      reconstructedTorusComplexComponent (path t) component :=
  rfl

/-- Evaluation after reconstruction is jointly continuous in the addressed time and torus faces. -/
theorem continuous_joint_reconstructedTorusComplexComponent
    {T : ℝ} (path : WeightedH3Path T) (component : Fin 3) :
    Continuous (fun z : Icc (0 : ℝ) T × SpatialTorus ↦
      reconstructedTorusComplexComponent (path z.1) component z.2) := by
  change Continuous (fun z : Icc (0 : ℝ) T × SpatialTorus ↦
    reconstructedTorusComplexComponentPath path component z.1 z.2)
  exact
    ((reconstructedTorusComplexComponentPath path component).continuous.comp
      continuous_fst).eval continuous_snd

/-- Assemble the complete complex vector path while retaining joint spacetime continuity. -/
theorem continuous_joint_reconstructedTorusComplex
    {T : ℝ} (path : WeightedH3Path T) :
    Continuous (fun z : Icc (0 : ℝ) T × SpatialTorus ↦
      reconstructedTorusComplex (path z.1) z.2) := by
  rw [continuous_pi_iff]
  intro component
  exact continuous_joint_reconstructedTorusComplexComponent path component

/-- The real-coordinate torus reconstruction is one jointly continuous spacetime field. -/
theorem continuous_joint_reconstructedTorusReal
    {T : ℝ} (path : WeightedH3Path T) :
    Continuous (fun z : Icc (0 : ℝ) T × SpatialTorus ↦
      reconstructedTorusReal (path z.1) z.2) := by
  exact (EuclideanSpace.equiv (Fin 3) ℝ).symm.continuous.comp (by
    rw [continuous_pi_iff]
    intro component
    exact Complex.continuous_re.comp
      ((continuous_apply component).comp
        (continuous_joint_reconstructedTorusComplex path)))

/-- Pulling the jointly continuous real torus field through the quotient projection returns a
jointly continuous Euclidean velocity on the declared restart aperture. -/
theorem continuous_joint_reconstructedVelocity
    {T : ℝ} (path : WeightedH3Path T) :
    Continuous (fun z : Space × Icc (0 : ℝ) T ↦
      reconstructedVelocity (path z.2) z.1) := by
  change Continuous (fun z : Space × Icc (0 : ℝ) T ↦
    reconstructedTorusReal (path z.2) (euclideanToSpatialTorus z.1))
  have hrebase : Continuous (fun z : Space × Icc (0 : ℝ) T ↦
      (z.2, euclideanToSpatialTorus z.1)) :=
    continuous_snd.prodMk
      (euclideanToSpatialTorus_isOpenQuotientMap.continuous.comp continuous_fst)
  have hcomposition :=
    (continuous_joint_reconstructedTorusReal path).comp hrebase
  change Continuous (fun z : Space × Icc (0 : ℝ) T ↦
    reconstructedTorusReal (path z.2) (euclideanToSpatialTorus z.1)) at hcomposition
  exact hcomposition

/-- On a Fourier-real native path, complexification of the joint real return recovers every
complex Fourier passage at every addressed spacetime face. -/
theorem complexifySpace_joint_reconstructedTorusReal
    {T : ℝ} {path : WeightedH3Path T}
    (hreal : IsWeightedFourierRealPath path)
    (t : Icc (0 : ℝ) T) (q : SpatialTorus) :
    complexifySpace (reconstructedTorusReal (path t) q) =
      reconstructedTorusComplex (path t) q :=
  complexifySpace_reconstructedTorusReal (hreal t) q

section Audit

#print axioms continuous_joint_reconstructedTorusComplexComponent
#print axioms continuous_joint_reconstructedTorusComplex
#print axioms continuous_joint_reconstructedTorusReal
#print axioms continuous_joint_reconstructedVelocity
#print axioms complexifySpace_joint_reconstructedTorusReal

end Audit

end Soma.Holonics.Millennium.NavierStokesWeightedSpacetimeReconstruction
