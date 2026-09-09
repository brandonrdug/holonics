import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

/-!
# Exterior change, boundary evaluation and pullback naturality

The algebraic cochain differential and pullback both use the existing `LinearMap.dualMap`.
Evaluation against a chain gives the discrete Stokes pairing; a chain map gives the commuting
pullback square. A failed square has its exact signed receiver defect, rather than an implicit
claim that an arbitrary coarse map preserves differential structure.

The imported smooth owner provides `extDeriv_pullback`, `extDerivWithin_pullback` and
`extDeriv_extDeriv` with their actual regularity hypotheses. These algebraic lemmas do not replace
the analytic integration theorem on an oriented smooth manifold with boundary.
-/

namespace Soma.Holonics.Geometry.ExteriorBoundary

variable {R C₀ C₁ C₂ D₀ D₁ : Type*} [CommRing R]
  [AddCommGroup C₀] [Module R C₀] [AddCommGroup C₁] [Module R C₁]
  [AddCommGroup C₂] [Module R C₂] [AddCommGroup D₀] [Module R D₀]
  [AddCommGroup D₁] [Module R D₁]

/-- The cochain/boundary pairing. No metric or inverse reconstruction is assumed. -/
theorem stokes_pairing (boundary : C₁ →ₗ[R] C₀) (form : Module.Dual R C₀) (chain : C₁) :
    boundary.dualMap form chain = form (boundary chain) := rfl

/-- Boundary-of-boundary zero induces square-zero on the dual cochain differential. -/
theorem coboundary_squared (first : C₁ →ₗ[R] C₀) (second : C₂ →ₗ[R] C₁)
    (boundary_squared : first.comp second = 0) (form : Module.Dual R C₀) :
    second.dualMap (first.dualMap form) = 0 := by
  apply LinearMap.ext
  intro chain
  change form (first (second chain)) = 0
  have h : first (second chain) = 0 := LinearMap.congr_fun boundary_squared chain
  rw [h, map_zero]

/-- The pullback square follows from the actual chain-map square in the opposite direction. -/
theorem pullback_coboundary (boundaryC : C₁ →ₗ[R] C₀) (boundaryD : D₁ →ₗ[R] D₀)
    (map₀ : C₀ →ₗ[R] D₀) (map₁ : C₁ →ₗ[R] D₁)
    (chain_map : boundaryD.comp map₁ = map₀.comp boundaryC)
    (form : Module.Dual R D₀) :
    boundaryC.dualMap (map₀.dualMap form) =
      map₁.dualMap (boundaryD.dualMap form) := by
  apply LinearMap.ext
  intro chain
  exact congrArg form (LinearMap.congr_fun chain_map chain).symm

/-- A receiver sees exactly the failure of the proposed boundary/transport square. -/
theorem pullback_coboundary_defect (boundaryC : C₁ →ₗ[R] C₀)
    (boundaryD : D₁ →ₗ[R] D₀) (map₀ : C₀ →ₗ[R] D₀) (map₁ : C₁ →ₗ[R] D₁)
    (form : Module.Dual R D₀) (chain : C₁) :
    boundaryC.dualMap (map₀.dualMap form) chain -
        map₁.dualMap (boundaryD.dualMap form) chain =
      form ((map₀.comp boundaryC - boundaryD.comp map₁) chain) := by
  simp

#print axioms stokes_pairing
#print axioms coboundary_squared
#print axioms pullback_coboundary
#print axioms pullback_coboundary_defect

end Soma.Holonics.Geometry.ExteriorBoundary
