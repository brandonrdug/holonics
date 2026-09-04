import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.Deriv.Add
import ElementaryHolonics.Millennium.NavierStokesMaterialPolygon

/-!
# Material differentiation of Navier--Stokes circulation

This module closes the first analytic edge between the official smooth-solution owner and the
finite material-polygon receiver.  At every strictly positive time it proves the chain rule along
each carried vertex: the derivative of the velocity observed by that moving vertex is exactly the
Eulerian time derivative plus advection, hence exactly the viscous, pressure-gradient, and forcing
population returned by `SmoothSolution.momentum`.

The same occurrence is then transported through the symmetric polygonal circulation.  The moving
edge contribution cancels by the existing cyclic kinetic-energy theorem, leaving an exact sum of
material accelerations paired with the retained edge population.  This is the exact
PDE-to-finite-circulation predecessor of a Kelvin bridge: comparison with the genuine
curve-integral Kelvin receiver still requires a
quadrature-defect or polygonal-limit theorem.  No postulated two-time balance is used.
-/

noncomputable section

open scoped BigOperators Laplacian
open Set InnerProductSpace

namespace Soma.Holonics.Millennium.NavierStokesMaterialDerivative

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesMaterialPolygon

/-! ## 1. The positive-time material derivative -/

/-- The right-hand side of the momentum equation at one space-time event. -/
def momentumReturn (ν : ℝ) (force velocity : VelocityField) (pressure : PressureField)
    (x : Space) (t : ℝ) : Space :=
  ν • Δ (fun y => velocity y t) x - gradient (fun y => pressure y t) x + force x t

/-- At positive time, the nonnegative half-cylinder is a neighbourhood of the event. -/
private theorem halfCylinder_mem_nhds (x : Space) {t : ℝ} (ht : 0 < t) :
    Set.univ ×ˢ Set.Ici (0 : ℝ) ∈ nhds (x, t) := by
  apply Filter.mem_of_superset (prod_mem_nhds Filter.univ_mem (Ioi_mem_nhds ht))
  rintro z ⟨_hzspace, hztime⟩
  constructor
  · exact Set.mem_univ z.1
  · change 0 ≤ z.2
    exact le_of_lt hztime

/-- Positive time is an interior point of the oriented time half-line. -/
private theorem timeHalfLine_mem_nhds {t : ℝ} (ht : 0 < t) :
    Set.Ici (0 : ℝ) ∈ nhds t := by
  exact Filter.mem_of_superset (Ioi_mem_nhds ht) fun τ hτ =>
    (show 0 ≤ τ from le_of_lt hτ)

/-- The full space-time velocity field of an admitted solution is differentiable at every
positive-time event. -/
theorem smoothSolution_velocityUncurry_differentiableAt
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (Function.uncurry velocity) (x, t) :=
  (solution.velocitySmooth.contDiffAt (halfCylinder_mem_nhds x ht)).differentiableAt (by simp)

/-- A carried polygon vertex is ordinarily differentiable at every positive time. -/
theorem materialPolygon_vertex_differentiableAt
    {extra : ℕ} {velocity : VelocityField}
    (polygon : MaterialPolygon extra velocity) (i : PolygonIndex extra)
    {t : ℝ} (ht : 0 < t) :
    DifferentiableAt ℝ (fun τ => polygon.vertex τ i) t :=
  (polygon.differentiable i t (le_of_lt ht)).differentiableAt (timeHalfLine_mem_nhds ht)

/-- At positive time the ordinary vertex derivative is the carrying velocity. -/
theorem materialPolygon_deriv_vertex_eq_velocity_positive
    {extra : ℕ} {velocity : VelocityField}
    (polygon : MaterialPolygon extra velocity) (i : PolygonIndex extra)
    {t : ℝ} (ht : 0 < t) :
    deriv (fun τ => polygon.vertex τ i) t = velocity (polygon.vertex t i) t := by
  rw [← polygon.carried i t (le_of_lt ht), derivWithin_of_mem_nhds (timeHalfLine_mem_nhds ht)]

/-- The joint space-time derivative splits on the material direction `(u, 1)` into its spatial
directional derivative and its time derivative. -/
theorem jointVelocityDerivative_materialDirection
    {velocity : VelocityField} {x : Space} {t : ℝ}
    (hvelocity : DifferentiableAt ℝ (Function.uncurry velocity) (x, t)) (u : Space) :
    fderiv ℝ (Function.uncurry velocity) (x, t) (u, 1) =
      deriv (velocity x) t + fderiv ℝ (fun y => velocity y t) x u := by
  have hspace := hvelocity.hasFDerivAt.comp x
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  have hspaceApply := congrArg (fun L : Space →L[ℝ] Space => L u) hspace.fderiv
  have hspaceEq :
      fderiv ℝ (Function.uncurry velocity) (x, t) (u, 0) =
        fderiv ℝ (fun y => velocity y t) x u := by
    simpa [Function.comp_def] using hspaceApply.symm
  have htime := hvelocity.hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
  have htimeApply := congrArg (fun L : ℝ →L[ℝ] Space => L 1) htime.fderiv
  have htimeEq :
      fderiv ℝ (Function.uncurry velocity) (x, t) (0, 1) = deriv (velocity x) t := by
    simpa [Function.comp_def, fderiv_apply_one_eq_deriv] using htimeApply.symm
  rw [show (u, (1 : ℝ)) = (u, 0) + (0, 1) by ext <;> simp, map_add, hspaceEq, htimeEq]
  abel

/-- **Material chain rule for the official solution.**  The derivative read by one carried vertex
is the Eulerian time derivative plus advection. -/
theorem solutionMaterialPolygon_deriv_velocityAlongVertex_eq_time_add_advection
    {extra : ℕ} {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (body : SolutionMaterialPolygon extra ν u₀ force velocity pressure)
    (i : PolygonIndex extra) {t : ℝ} (ht : 0 < t) :
    deriv (fun τ => velocity (body.polygon.vertex τ i) τ) t =
      derivWithin (velocity (body.polygon.vertex t i)) (Ici 0) t +
        fderiv ℝ (fun y => velocity y t) (body.polygon.vertex t i)
          (velocity (body.polygon.vertex t i) t) := by
  let x := body.polygon.vertex t i
  have hvelocity := smoothSolution_velocityUncurry_differentiableAt body.solution x ht
  have hvertex := materialPolygon_vertex_differentiableAt body.polygon i ht
  have hvertexDerivative := materialPolygon_deriv_vertex_eq_velocity_positive body.polygon i ht
  have hpair : HasDerivAt (fun τ => (body.polygon.vertex τ i, τ))
      (velocity x t, 1) t := by
    have := (hvertex.hasFDerivAt.prodMk (hasDerivAt_id t).hasFDerivAt).hasDerivAt
    simpa [x, hvertexDerivative] using this
  have hcomposition := hvelocity.hasFDerivAt.comp_hasDerivAt_of_eq t hpair (by simp [x])
  calc
    deriv (fun τ => velocity (body.polygon.vertex τ i) τ) t =
        fderiv ℝ (Function.uncurry velocity) (x, t) (velocity x t, 1) := by
          simpa [Function.comp_def, x] using hcomposition.deriv
    _ = deriv (velocity x) t + fderiv ℝ (fun y => velocity y t) x (velocity x t) :=
      jointVelocityDerivative_materialDirection hvelocity (velocity x t)
    _ = derivWithin (velocity x) (Ici 0) t +
        fderiv ℝ (fun y => velocity y t) x (velocity x t) := by
      rw [derivWithin_of_mem_nhds (timeHalfLine_mem_nhds ht)]

/-- **Momentum along a material vertex.**  The derivative observed by the carried receiver is
exactly the viscosity-minus-pressure-gradient-plus-force return of the admitted PDE. -/
theorem solutionMaterialPolygon_deriv_velocityAlongVertex_eq_momentumReturn
    {extra : ℕ} {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (body : SolutionMaterialPolygon extra ν u₀ force velocity pressure)
    (i : PolygonIndex extra) {t : ℝ} (ht : 0 < t) :
    deriv (fun τ => velocity (body.polygon.vertex τ i) τ) t =
      momentumReturn ν force velocity pressure (body.polygon.vertex t i) t := by
  rw [solutionMaterialPolygon_deriv_velocityAlongVertex_eq_time_add_advection body i ht]
  exact body.solution.momentum (body.polygon.vertex t i) t (le_of_lt ht)

/-! ## 2. The differentiated symmetric circulation -/

/-- Pair a vector population symmetrically with every oriented edge of a polygon. -/
def symmetricEdgePairing {extra : ℕ}
    (source vertex : PolygonIndex extra → Space) : ℝ :=
  ∑ i, inner ℝ (symmetricEdgeCurrent source i) (edge vertex i)

/-- The PDE return sampled at every addressed material vertex. -/
def solutionMaterialPolygon_momentumPopulation
    {extra : ℕ} {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (body : SolutionMaterialPolygon extra ν u₀ force velocity pressure) (t : ℝ) :
    PolygonIndex extra → Space :=
  fun i => momentumReturn ν force velocity pressure (body.polygon.vertex t i) t

/-- The viscous population sampled at every addressed material vertex. -/
def solutionMaterialPolygon_viscousPopulation
    {extra : ℕ} {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (body : SolutionMaterialPolygon extra ν u₀ force velocity pressure) (t : ℝ) :
    PolygonIndex extra → Space :=
  fun i => ν • Δ (fun y => velocity y t) (body.polygon.vertex t i)

/-- The lowered pressure-gradient population sampled at every addressed material vertex. -/
def solutionMaterialPolygon_pressurePopulation
    {extra : ℕ} {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (body : SolutionMaterialPolygon extra ν u₀ force velocity pressure) (t : ℝ) :
    PolygonIndex extra → Space :=
  fun i => gradient (fun y => pressure y t) (body.polygon.vertex t i)

/-- The external forcing population sampled at every addressed material vertex. -/
def solutionMaterialPolygon_forcePopulation
    {extra : ℕ} {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (body : SolutionMaterialPolygon extra ν u₀ force velocity pressure) (t : ℝ) :
    PolygonIndex extra → Space :=
  fun i => force (body.polygon.vertex t i) t

/-- **Differentiated finite circulation.**  The positive-time derivative of symmetric polygonal
circulation is the edge pairing of the actual material acceleration.  The second Leibniz term is
the moving-edge return and cancels exactly around the closed polygon. -/
theorem solutionMaterialPolygon_deriv_symmetricVelocityCirculation
    {extra : ℕ} {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (body : SolutionMaterialPolygon extra ν u₀ force velocity pressure)
    {t : ℝ} (ht : 0 < t) :
    deriv body.polygon.symmetricVelocityCirculation t =
      symmetricEdgePairing (solutionMaterialPolygon_momentumPopulation body t)
        (body.polygon.snapshot t) := by
  let current : PolygonIndex extra → Space :=
    fun i => velocity (body.polygon.vertex t i) t
  let acceleration : PolygonIndex extra → Space :=
    solutionMaterialPolygon_momentumPopulation body t
  have hvertex : ∀ i : PolygonIndex extra,
      HasDerivAt (fun τ => body.polygon.vertex τ i) (current i) t := by
    intro i
    have h := (materialPolygon_vertex_differentiableAt body.polygon i ht).hasDerivAt
    simpa [current, materialPolygon_deriv_vertex_eq_velocity_positive body.polygon i ht] using h
  have hcurrent : ∀ i : PolygonIndex extra,
      HasDerivAt (fun τ => velocity (body.polygon.vertex τ i) τ) (acceleration i) t := by
    intro i
    have hvelocity := smoothSolution_velocityUncurry_differentiableAt body.solution
      (body.polygon.vertex t i) ht
    have hvertex := materialPolygon_vertex_differentiableAt body.polygon i ht
    have hvertexDerivative := materialPolygon_deriv_vertex_eq_velocity_positive body.polygon i ht
    have hpair : HasDerivAt (fun τ => (body.polygon.vertex τ i, τ))
        (velocity (body.polygon.vertex t i) t, 1) t := by
      have h := (hvertex.hasFDerivAt.prodMk (hasDerivAt_id t).hasFDerivAt).hasDerivAt
      simpa [hvertexDerivative] using h
    have hcomposition := hvelocity.hasFDerivAt.comp_hasDerivAt_of_eq t hpair (by simp)
    have hpath : HasDerivAt (fun τ => velocity (body.polygon.vertex τ i) τ)
        (fderiv ℝ (Function.uncurry velocity) (body.polygon.vertex t i, t)
          (velocity (body.polygon.vertex t i) t, 1)) t := by
      simpa [Function.comp_def] using hcomposition
    apply hpath.congr_deriv
    rw [← hpath.deriv,
      solutionMaterialPolygon_deriv_velocityAlongVertex_eq_momentumReturn body i ht]
    rfl
  have hspanSub (a b : Space) :
      (ContinuousLinearMap.toSpanSingleton ℝ a -
        ContinuousLinearMap.toSpanSingleton ℝ b) 1 = a - b := by
    rw [ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one,
      ContinuousLinearMap.toSpanSingleton_apply_one]
  have hspanAvg (a b : Space) :
      ((2 : ℝ)⁻¹ • (ContinuousLinearMap.toSpanSingleton ℝ a +
        ContinuousLinearMap.toSpanSingleton ℝ b)) 1 =
        (2 : ℝ)⁻¹ • a + (2 : ℝ)⁻¹ • b := by
    rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.toSpanSingleton_apply_one,
      ContinuousLinearMap.toSpanSingleton_apply_one]
    rw [smul_add]
  have hedge : ∀ i : PolygonIndex extra,
      HasDerivAt (fun τ => body.polygon.edgeAt τ i)
        (current (cyclicSuccessor extra i) - current i) t := by
    intro i
    convert (((hvertex (cyclicSuccessor extra i)).hasFDerivAt.sub
      (hvertex i).hasFDerivAt).hasDerivAt) using 1 <;> try rfl
    exact (hspanSub _ _).symm
  have hsymmetricCurrent : ∀ i : PolygonIndex extra,
      HasDerivAt
        (fun τ => symmetricEdgeCurrent
          (fun j => velocity (body.polygon.vertex τ j) τ) i)
        (symmetricEdgeCurrent acceleration i) t := by
    intro i
    convert ((((hcurrent i).hasFDerivAt.add
      (hcurrent (cyclicSuccessor extra i)).hasFDerivAt).const_smul ((2 : ℝ)⁻¹)).hasDerivAt) using 1 <;>
      try rfl
    simpa [symmetricEdgeCurrent] using (hspanAvg _ _).symm
  have hedgeTerm : ∀ i : PolygonIndex extra,
      HasDerivAt
        (fun τ => inner ℝ
          (symmetricEdgeCurrent (fun j => velocity (body.polygon.vertex τ j) τ) i)
          (body.polygon.edgeAt τ i))
        (inner ℝ (symmetricEdgeCurrent current i)
            (current (cyclicSuccessor extra i) - current i) +
          inner ℝ (symmetricEdgeCurrent acceleration i) (body.polygon.edgeAt t i)) t := by
    intro i
    simpa [current] using (hsymmetricCurrent i).inner ℝ (hedge i)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun i _hi => hedgeTerm i
  calc
    deriv body.polygon.symmetricVelocityCirculation t =
        ∑ i, (inner ℝ (symmetricEdgeCurrent current i)
              (current (cyclicSuccessor extra i) - current i) +
            inner ℝ (symmetricEdgeCurrent acceleration i) (body.polygon.edgeAt t i)) := by
      change deriv (fun y => ∑ i, inner ℝ
          (symmetricEdgeCurrent (fun j => velocity (body.polygon.vertex y j) y) i)
          (edge (body.polygon.vertex y) i)) t = _
      exact hsum.deriv
    _ = symmetricEdgeMotionReturn current +
        symmetricEdgePairing acceleration (body.polygon.snapshot t) := by
      rw [Finset.sum_add_distrib]
      rfl
    _ = symmetricEdgePairing acceleration (body.polygon.snapshot t) := by
      rw [symmetricEdgeMotionReturn_eq_zero]
      simp
    _ = symmetricEdgePairing (solutionMaterialPolygon_momentumPopulation body t)
        (body.polygon.snapshot t) := rfl

/-- **The three Navier--Stokes returns remain distinct at the finite receiver.**  Differentiated
material circulation is viscous edge transport minus sampled pressure-gradient edge quadrature
plus forcing edge transport.  The pressure term is retained: endpoint trapezoidal sampling is not
the exact curve integral and need not telescope. -/
theorem solutionMaterialPolygon_deriv_symmetricVelocityCirculation_eq_threeReturns
    {extra : ℕ} {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (body : SolutionMaterialPolygon extra ν u₀ force velocity pressure)
    {t : ℝ} (ht : 0 < t) :
    deriv body.polygon.symmetricVelocityCirculation t =
      symmetricEdgePairing (solutionMaterialPolygon_viscousPopulation body t)
          (body.polygon.snapshot t) -
        symmetricEdgePairing (solutionMaterialPolygon_pressurePopulation body t)
          (body.polygon.snapshot t) +
        symmetricEdgePairing (solutionMaterialPolygon_forcePopulation body t)
          (body.polygon.snapshot t) := by
  rw [solutionMaterialPolygon_deriv_symmetricVelocityCirculation body ht]
  simp only [symmetricEdgePairing, solutionMaterialPolygon_momentumPopulation,
    solutionMaterialPolygon_viscousPopulation, solutionMaterialPolygon_pressurePopulation,
    solutionMaterialPolygon_forcePopulation, momentumReturn, symmetricEdgeCurrent,
    smul_sub, smul_add, inner_sub_left, inner_add_left, Finset.sum_sub_distrib,
    Finset.sum_add_distrib]
  ring

section Audit

#print axioms jointVelocityDerivative_materialDirection
#print axioms solutionMaterialPolygon_deriv_velocityAlongVertex_eq_momentumReturn
#print axioms solutionMaterialPolygon_deriv_symmetricVelocityCirculation
#print axioms solutionMaterialPolygon_deriv_symmetricVelocityCirculation_eq_threeReturns

end Audit

end Soma.Holonics.Millennium.NavierStokesMaterialDerivative
