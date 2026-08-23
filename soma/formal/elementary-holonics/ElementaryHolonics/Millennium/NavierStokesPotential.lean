import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.MeasureTheory.Integral.CurveIntegral.Poincare
import ElementaryHolonics.Millennium.NavierStokesKelvin
import ElementaryHolonics.Millennium.NavierStokesVorticity

/-!
# A global velocity potential on the Euclidean Navier--Stokes carrier

This module joins the repository's pointwise vorticity chart to Mathlib's Poincare lemma.  At a
fixed time, a differentiable velocity field with zero vorticity has a symmetric derivative.  The
Euclidean inner product lowers the velocity to the one-form already used by the Kelvin receiver;
its derivative is therefore symmetric.  Convexity of the full carrier `Space = R^3` then returns a
global scalar potential whose derivative is exactly that one-form.

The conclusion is confined to the zero-vorticity fibre on the contractible Euclidean carrier.  It
does not assert that a general Navier--Stokes velocity is irrotational, establish regularity, or
solve the Navier--Stokes problem.  The final loop theorem is a separate consequence of the
contractibility, hence simple connectedness, of the Euclidean carrier; it does not prove the
Poincare conjecture.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesPotential

open Set
open scoped BigOperators
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesKelvin
open Soma.Holonics.Millennium.NavierStokesVorticity

/-- Zero vorticity makes the derivative of the lowered velocity one-form symmetric at the
specified differentiable occurrence. -/
theorem velocityOneForm_fderiv_symmetric_of_vorticityAt_eq_zero
    (velocity : VelocityField) (t : ℝ) (x : Space)
    (hvelocity : DifferentiableAt ℝ (fun y ↦ velocity y t) x)
    (hvorticity : vorticityAt (fun y ↦ velocity y t) x = 0)
    (v w : Space) :
    fderiv ℝ (velocityOneForm velocity t) x v w =
      fderiv ℝ (velocityOneForm velocity t) x w v := by
  have hform :
      fderiv ℝ (velocityOneForm velocity t) x =
        (innerSL ℝ).comp (fderiv ℝ (fun y ↦ velocity y t) x) := by
    change fderiv ℝ ((innerSL ℝ) ∘ fun y ↦ velocity y t) x = _
    exact ((innerSL ℝ).hasFDerivAt.comp x hvelocity.hasFDerivAt).fderiv
  rw [hform]
  simp only [ContinuousLinearMap.comp_apply, innerSL_apply_apply, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial]
  have hsym : IsSymmetricJacobian
      (velocityJacobianAt (fun y ↦ velocity y t) x) :=
    (curlFromJacobian_eq_zero_iff _).mp hvorticity
  simp_rw [continuousLinearMap_apply_coordinate, Finset.mul_sum]
  calc
    (∑ i, ∑ j, w.ofLp i *
        (jacobianMatrix (fderiv ℝ (fun y ↦ velocity y t) x) i j * v.ofLp j)) =
        ∑ j, ∑ i, w.ofLp i *
          (jacobianMatrix (fderiv ℝ (fun y ↦ velocity y t) x) i j * v.ofLp j) :=
      Finset.sum_comm
    _ = ∑ j, ∑ i, v.ofLp j *
        (jacobianMatrix (fderiv ℝ (fun y ↦ velocity y t) x) j i * w.ofLp i) := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      have hij :
          jacobianMatrix (fderiv ℝ (fun y ↦ velocity y t) x) i j =
            jacobianMatrix (fderiv ℝ (fun y ↦ velocity y t) x) j i := by
        simpa [velocityJacobianAt] using hsym i j
      rw [hij]
      ring
    _ = ∑ i, ∑ j, v.ofLp i *
        (jacobianMatrix (fderiv ℝ (fun y ↦ velocity y t) x) i j * w.ofLp j) := rfl

/-- **Global potential on the zero-vorticity fibre.**

At a fixed time, global differentiability and pointwise zero vorticity on the actual Euclidean
Navier--Stokes carrier produce a scalar potential.  Its Frechet derivative at every point is the
Kelvin module's lowered velocity one-form. -/
theorem exists_potential_of_vorticityAt_eq_zero
    (velocity : VelocityField) (t : ℝ)
    (hvelocity : Differentiable ℝ (fun x ↦ velocity x t))
    (hvorticity : ∀ x, vorticityAt (fun y ↦ velocity y t) x = 0) :
    ∃ potential : Space → ℝ, ∀ x,
      HasFDerivAt potential (velocityOneForm velocity t x) x := by
  have hform : Differentiable ℝ (velocityOneForm velocity t) := by
    intro x
    change DifferentiableAt ℝ ((innerSL ℝ) ∘ fun y ↦ velocity y t) x
    exact (innerSL ℝ).differentiableAt.comp x (hvelocity x)
  obtain ⟨potential, hpotential⟩ :=
    convex_univ.exists_forall_hasFDerivAt_of_fderiv_symmetric isOpen_univ
      hform.differentiableOn
      (fun x _ v w ↦
        velocityOneForm_fderiv_symmetric_of_vorticityAt_eq_zero
          velocity t x (hvelocity x) (hvorticity x) v w)
  exact ⟨potential, fun x ↦ hpotential x (mem_univ x)⟩

/-- Every time-indexed based material loop on `Space` is homotopic to the constant loop.  This is a
topology consequence of the Euclidean carrier's contractibility, independent of the potential
theorem. -/
theorem materialLoop_nullhomotopic
    (base : ℝ → Space) (loop : ∀ t, Path (base t) (base t)) (t : ℝ) :
    Path.Homotopic (loop t) (Path.refl (base t)) :=
  SimplyConnectedSpace.paths_homotopic _ _

section Audit

#print axioms velocityOneForm_fderiv_symmetric_of_vorticityAt_eq_zero
#print axioms exists_potential_of_vorticityAt_eq_zero
#print axioms materialLoop_nullhomotopic

end Audit

end Soma.Holonics.Millennium.NavierStokesPotential
