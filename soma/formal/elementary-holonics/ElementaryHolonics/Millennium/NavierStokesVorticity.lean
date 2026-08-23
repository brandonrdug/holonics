import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.ToLin
import ElementaryHolonics.Foundation.Lineage
import ElementaryHolonics.Millennium.Coupling
import ElementaryHolonics.Millennium.NavierStokes
import ElementaryHolonics.Millennium.Swing

/-!
# The local vorticity passage on the actual three-dimensional Navier–Stokes carrier

This module constructs the first differential bridge out of the official `R³` velocity object.
It keeps three objects separate:

* a continuous-linear velocity Jacobian and its standard matrix chart;
* the antisymmetric curl face of that chart;
* the addressed occurrence joining a field/point to its Jacobian and then to its vorticity.

The local Lamb identity is exact.  The kernel of the curl face is proved to be exactly the
symmetric-Jacobian population, and that zero composite is installed as the existing additive
`TransportChain`.  Consequently a pressure gradient enters this chain only after the symmetry of
its second derivative has been supplied; no scalar pressure is used as a governor.

No theorem here derives the vorticity evolution equation, a global Hodge–Leray projection, an
energy estimate, regularity, or any alternative of the official Navier–Stokes problem.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesVorticity

open Soma.Holonics
open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.NavierStokes

/-- The standard real `3 × 3` chart for a spatial derivative. -/
abbrev Matrix3 := Matrix (Fin 3) (Fin 3) ℝ

/-- Put three real coordinates back on the actual Euclidean-space carrier. -/
def vectorOfCoordinates (v : Fin 3 → ℝ) : Space :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm v

@[simp]
theorem vectorOfCoordinates_apply (v : Fin 3 → ℝ) (i : Fin 3) :
    vectorOfCoordinates v i = v i := rfl

/-- A matrix acts on the Euclidean carrier through its standard coordinate chart. -/
def matrixAction (J : Matrix3) (u : Space) : Space :=
  vectorOfCoordinates (Matrix.mulVec J fun i => u i)

@[simp]
theorem matrixAction_apply (J : Matrix3) (u : Space) (i : Fin 3) :
    matrixAction J u i = ∑ j : Fin 3, J i j * u j := by
  simp [matrixAction, Matrix.mulVec]

/-- The oriented three-dimensional cross interaction. -/
def cross (u v : Space) : Space :=
  vectorOfCoordinates ![
    u 1 * v 2 - u 2 * v 1,
    u 2 * v 0 - u 0 * v 2,
    u 0 * v 1 - u 1 * v 0]

/-- The curl face of one local Jacobian chart. -/
def curlFromJacobian (J : Matrix3) : Space :=
  vectorOfCoordinates ![
    J 2 1 - J 1 2,
    J 0 2 - J 2 0,
    J 1 0 - J 0 1]

/-- The transpose action which becomes the gradient of kinetic energy for an actual velocity jet. -/
def kineticGradientFromJacobian (J : Matrix3) (u : Space) : Space :=
  matrixAction J.transpose u

/-- Exchanging the two incoming rays reverses the cross interaction. -/
theorem cross_swap (u v : Space) : cross v u = -cross u v := by
  ext i
  fin_cases i <;> simp [cross] <;> ring

/-- The exchange of the cross interaction is exactly the frozen-board swing about zero. -/
theorem cross_swap_is_zeroAnchoredSwing (u v : Space) :
    cross v u = Swing.swing 0 (cross u v) := by
  rw [cross_swap]
  ext i
  simp [Swing.swing]

/-- **The pointwise Lamb identity in a Jacobian chart.**

The advective action is the transpose/kinetic-gradient action minus the cross interaction with
the curl face.  This is a polynomial identity in the nine entries of `J` and three entries of `u`;
it requires no regularity hypothesis. -/
theorem lambIdentity (J : Matrix3) (u : Space) :
    matrixAction J u = kineticGradientFromJacobian J u - cross u (curlFromJacobian J) := by
  ext i
  fin_cases i <;>
    simp [matrixAction, kineticGradientFromJacobian, cross, curlFromJacobian, Matrix.mulVec,
      Fin.sum_univ_succ] <;>
    ring

/-- A Jacobian chart is symmetric when its two derivative directions commute. -/
def IsSymmetricJacobian (J : Matrix3) : Prop :=
  ∀ i j, J i j = J j i

/-- Curl annihilates every symmetric Jacobian. -/
theorem curlFromJacobian_eq_zero_of_symmetric {J : Matrix3}
    (hJ : IsSymmetricJacobian J) : curlFromJacobian J = 0 := by
  ext i
  fin_cases i
  · simpa [curlFromJacobian] using sub_eq_zero.mpr (hJ 2 1)
  · simpa [curlFromJacobian] using sub_eq_zero.mpr (hJ 0 2)
  · simpa [curlFromJacobian] using sub_eq_zero.mpr (hJ 1 0)

/-- Curl loses exactly the symmetric part: a zero curl face forces the whole Jacobian to be
symmetric, not merely a selected pair of entries. -/
theorem symmetric_of_curlFromJacobian_eq_zero {J : Matrix3}
    (hJ : curlFromJacobian J = 0) : IsSymmetricJacobian J := by
  have h0 := congrArg (fun v : Space => v 0) hJ
  have h1 := congrArg (fun v : Space => v 1) hJ
  have h2 := congrArg (fun v : Space => v 2) hJ
  simp [curlFromJacobian] at h0 h1 h2
  intro i j
  fin_cases i <;> fin_cases j <;> simp <;> linarith

/-- The complete kernel theorem for the local curl receiver. -/
theorem curlFromJacobian_eq_zero_iff (J : Matrix3) :
    curlFromJacobian J = 0 ↔ IsSymmetricJacobian J :=
  ⟨symmetric_of_curlFromJacobian_eq_zero, curlFromJacobian_eq_zero_of_symmetric⟩

/-- Symmetric Jacobians as the exact incoming population of the pressure-curl chain. -/
def symmetricJacobians : AddSubgroup Matrix3 where
  carrier := {J | IsSymmetricJacobian J}
  zero_mem' := by intro i j; rfl
  add_mem' := by
    intro J K hJ hK i j
    simp only [Matrix.add_apply]
    rw [hJ i j, hK i j]
  neg_mem' := by
    intro J hJ i j
    simp only [Matrix.neg_apply]
    rw [hJ i j]

/-- Curl as an additive transport from Jacobian charts to vorticity vectors. -/
def curlAddHom : Matrix3 →+ Space where
  toFun := curlFromJacobian
  map_zero' := by ext i; fin_cases i <;> simp [curlFromJacobian]
  map_add' J K := by
    ext i
    fin_cases i <;> simp [curlFromJacobian] <;> ring

/-- The pressure-curl chain: symmetric second-derivative charts enter the full Jacobian population,
then curl carries them to zero. -/
def pressureCurlChain : Coupling.TransportChain symmetricJacobians Matrix3 Space where
  into := symmetricJacobians.subtype
  outOf := curlAddHom
  composite_zero J := curlFromJacobian_eq_zero_of_symmetric J.property

/-- Every chart retained by curl is realized by the symmetric-Jacobian inclusion. -/
theorem pressureCurlChain_retained_le_realized :
    pressureCurlChain.retained ≤ pressureCurlChain.realized := by
  intro J hJ
  change curlFromJacobian J = 0 at hJ
  exact ⟨⟨J, symmetric_of_curlFromJacobian_eq_zero hJ⟩, rfl⟩

/-- The pressure-curl chain is exact at the Jacobian population, hence its coupling obstruction
vanishes. -/
theorem pressureCurlChain_glues : pressureCurlChain.toPassage.Glues :=
  pressureCurlChain.theOntoSupplyGlues pressureCurlChain_retained_le_realized

/-- The standard-basis matrix chart of a continuous-linear spatial derivative. -/
def jacobianMatrix (D : Space →L[ℝ] Space) : Matrix3 :=
  LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis D.toLinearMap

/-- The matrix chart carries the continuous-linear action exactly. -/
theorem matrixAction_jacobianMatrix (D : Space →L[ℝ] Space) (u : Space) :
    matrixAction (jacobianMatrix D) u = D u := by
  ext i
  have h := LinearMap.toMatrix_mulVec_repr
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis D.toLinearMap u
  simpa [matrixAction, jacobianMatrix] using congrFun h i

/-- The actual spatial Jacobian of a velocity field at an addressed point. -/
def velocityJacobianAt (u : InitialVelocity) (x : Space) : Matrix3 :=
  jacobianMatrix (fderiv ℝ u x)

/-- The actual vorticity face of a velocity field at an addressed point. -/
def vorticityAt (u : InitialVelocity) (x : Space) : Space :=
  curlFromJacobian (velocityJacobianAt u x)

/-- The actual pointwise Lamb identity for the derivative used by the official Navier–Stokes
object. -/
theorem pointwiseLambIdentity (u : InitialVelocity) (x : Space) :
    fderiv ℝ u x (u x) =
      kineticGradientFromJacobian (velocityJacobianAt u x) (u x) -
        cross (u x) (vorticityAt u x) := by
  rw [← matrixAction_jacobianMatrix]
  exact lambIdentity (velocityJacobianAt u x) (u x)

/-- The derivative occurrence from an addressed velocity field and point to its Jacobian chart. -/
def velocityToJacobianPassage :
    AddressedPassage (InitialVelocity × Space) Matrix3 where
  Occurrence := InitialVelocity × Space
  source := id
  target occurrence := velocityJacobianAt occurrence.1 occurrence.2

/-- The curl occurrence from a Jacobian chart to its vorticity face. -/
def jacobianToVorticityPassage : AddressedPassage Matrix3 Space where
  Occurrence := Matrix3
  source := id
  target := curlFromJacobian

/-- The ordered velocity-to-Jacobian-to-vorticity passage.  Its occurrence population retains the
field/point occurrence, the Jacobian occurrence, and their literal joining equality. -/
def velocityToVorticityPassage :
    AddressedPassage (InitialVelocity × Space) Space :=
  AddressedPassage.comp jacobianToVorticityPassage velocityToJacobianPassage

/-- The canonical composite occurrence carried by one actual field/point event. -/
def velocityToVorticityOccurrence (u : InitialVelocity) (x : Space) :
    velocityToVorticityPassage.Occurrence :=
  ⟨(u, x), velocityJacobianAt u x, rfl⟩

/-- The composite occurrence retains its addressed predecessor exactly. -/
theorem velocityToVorticityOccurrence_source (u : InitialVelocity) (x : Space) :
    velocityToVorticityPassage.source (velocityToVorticityOccurrence u x) = (u, x) := rfl

/-- The composite occurrence returns the actual vorticity face. -/
theorem velocityToVorticityOccurrence_target (u : InitialVelocity) (x : Space) :
    velocityToVorticityPassage.target (velocityToVorticityOccurrence u x) = vorticityAt u x := rfl

/-- A pressure field enters the curl kernel exactly when the Jacobian of its actual gradient is
symmetric.  The analytic theorem supplying that symmetry from second differentiability is kept as
an explicit hypothesis rather than hidden in the word “pressure”. -/
theorem curl_gradient_eq_zero_of_symmetricDerivative (p : Space → ℝ) (x : Space)
    (hessianSymmetry : IsSymmetricJacobian (velocityJacobianAt (gradient p) x)) :
    vorticityAt (gradient p) x = 0 :=
  curlFromJacobian_eq_zero_of_symmetric hessianSymmetry

end Soma.Holonics.Millennium.NavierStokesVorticity

section Audit
open Soma.Holonics.Millennium.NavierStokesVorticity
#print axioms cross_swap_is_zeroAnchoredSwing
#print axioms lambIdentity
#print axioms curlFromJacobian_eq_zero_iff
#print axioms pressureCurlChain_glues
#print axioms matrixAction_jacobianMatrix
#print axioms pointwiseLambIdentity
#print axioms velocityToVorticityOccurrence_target
#print axioms curl_gradient_eq_zero_of_symmetricDerivative
end Audit
