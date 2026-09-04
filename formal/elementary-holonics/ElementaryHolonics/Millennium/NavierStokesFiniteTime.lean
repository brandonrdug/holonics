import Mathlib.Tactic
import ElementaryHolonics.Millennium.NavierStokes

/-!
# Finite-time Navier--Stokes solution carriers

The official `SmoothSolution` is global on the nonnegative half-line.  A continuation or blow-up
alternative cannot use that owner without assuming the conclusion it is meant to study.  This
module introduces the bounded slab `Icc 0 T`, places the time derivative on that actual slab, and
proves that global solutions restrict to it and that slab restriction is functorial.

The endpoint derivative is retained as a within-derivative.  The restriction theorems therefore
transport derivatives through `derivWithin_subset` and the unique-differentiability of a
nondegenerate real interval; they do not silently replace an endpoint derivative by an ordinary
derivative.
-/

noncomputable section

open ContDiff Set InnerProductSpace
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesFiniteTime

open Soma.Holonics.Millennium.NavierStokes

/-- The closed time population carried by a solution of lifetime `T`. -/
def timeSlab (T : ℝ) : Set ℝ := Icc 0 T

/-- The full spatial carrier over the closed time slab. -/
def spaceTimeSlab (T : ℝ) : Set (Space × ℝ) := Set.univ ×ˢ timeSlab T

/-- A smooth Navier--Stokes solution on the nondegenerate bounded slab `Icc 0 T`.

Unlike the official global owner, the time derivative in `momentum` is taken within the actual
closed slab.  This keeps the terminal event available for a later restart or obstruction return. -/
structure SmoothSolutionOn
    (T ν : ℝ) (u₀ : InitialVelocity) (force : VelocityField)
    (velocity : VelocityField) (pressure : PressureField) : Prop where
  terminal_pos : 0 < T
  momentum : ∀ x, ∀ t ∈ timeSlab T,
    derivWithin (velocity x) (timeSlab T) t +
        fderiv ℝ (fun y => velocity y t) x (velocity x t) =
      ν • Δ (fun y => velocity y t) x -
        gradient (fun y => pressure y t) x + force x t
  incompressible : ∀ x, ∀ t ∈ timeSlab T,
    divergence (fun y => velocity y t) x = 0
  initial : ∀ x, velocity x 0 = u₀ x
  velocitySmooth :
    ContDiffOn ℝ ∞ (Function.uncurry velocity) (spaceTimeSlab T)
  pressureSmooth :
    ContDiffOn ℝ ∞ (Function.uncurry pressure) (spaceTimeSlab T)

/-- Every point of a smaller slab is a point of the larger slab. -/
theorem timeSlab_mono {S T : ℝ} (hST : S ≤ T) : timeSlab S ⊆ timeSlab T := by
  intro t ht
  exact ⟨ht.1, ht.2.trans hST⟩

/-- Spatial extension preserves inclusion of time slabs. -/
theorem spaceTimeSlab_mono {S T : ℝ} (hST : S ≤ T) :
    spaceTimeSlab S ⊆ spaceTimeSlab T := by
  rintro ⟨x, t⟩ hxt
  exact ⟨Set.mem_univ x, timeSlab_mono hST hxt.2⟩

/-- A fixed spatial receiver reads a differentiable time section from a smooth slab field. -/
theorem smoothSolutionOn_velocity_time_differentiableWithinAt
    {T ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T ν u₀ force velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ timeSlab T) :
    DifferentiableWithinAt ℝ (velocity x) (timeSlab T) t := by
  have hsection : ContDiffOn ℝ ∞ (velocity x) (timeSlab T) :=
    solution.velocitySmooth.comp (contDiff_prodMk_right x).contDiffOn (by
      intro τ hτ
      exact ⟨Set.mem_univ x, hτ⟩)
  exact hsection.differentiableOn (by simp) t ht

/-- A fixed spatial receiver reads a differentiable time section from a global smooth field. -/
theorem smoothSolution_velocity_time_differentiableWithinAt
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    (x : Space) {t : ℝ} (ht : t ∈ Ici (0 : ℝ)) :
    DifferentiableWithinAt ℝ (velocity x) (Ici 0) t := by
  have hsection : ContDiffOn ℝ ∞ (velocity x) (Ici 0) :=
    solution.velocitySmooth.comp (contDiff_prodMk_right x).contDiffOn (by
      intro τ hτ
      exact ⟨Set.mem_univ x, hτ⟩)
  exact hsection.differentiableOn (by simp) t ht

/-- **A global solution returns a genuine bounded-slab solution.** -/
def SmoothSolution.toSmoothSolutionOn
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    {T : ℝ} (hT : 0 < T) :
    SmoothSolutionOn T ν u₀ force velocity pressure where
  terminal_pos := hT
  momentum x t ht := by
    have hsubset : timeSlab T ⊆ Ici (0 : ℝ) := fun _ h => h.1
    have hdiff := smoothSolution_velocity_time_differentiableWithinAt solution x (hsubset ht)
    rw [derivWithin_subset hsubset
      ((uniqueDiffOn_Icc hT).uniqueDiffWithinAt ht) hdiff]
    exact solution.momentum x t (hsubset ht)
  incompressible x t ht := solution.incompressible x t ht.1
  initial := solution.initial
  velocitySmooth := solution.velocitySmooth.mono (by
    rintro ⟨x, t⟩ hxt
    exact ⟨Set.mem_univ x, hxt.2.1⟩)
  pressureSmooth := solution.pressureSmooth.mono (by
    rintro ⟨x, t⟩ hxt
    exact ⟨Set.mem_univ x, hxt.2.1⟩)

/-- **Slab restriction is an exact transport.**  A solution on `Icc 0 T` restricts to every
nondegenerate `Icc 0 S` with `S ≤ T`; the terminal within-derivative is transported through the
unique differential germ of the smaller interval. -/
def SmoothSolutionOn.restrict
    {T ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T ν u₀ force velocity pressure)
    {S : ℝ} (hS : 0 < S) (hST : S ≤ T) :
    SmoothSolutionOn S ν u₀ force velocity pressure where
  terminal_pos := hS
  momentum x t ht := by
    have hsubset := timeSlab_mono hST
    have hdiff := smoothSolutionOn_velocity_time_differentiableWithinAt solution x (hsubset ht)
    rw [derivWithin_subset hsubset
      ((uniqueDiffOn_Icc hS).uniqueDiffWithinAt ht) hdiff]
    exact solution.momentum x t (hsubset ht)
  incompressible x t ht := solution.incompressible x t (timeSlab_mono hST ht)
  initial := solution.initial
  velocitySmooth := solution.velocitySmooth.mono (spaceTimeSlab_mono hST)
  pressureSmooth := solution.pressureSmooth.mono (spaceTimeSlab_mono hST)

/-- Restricting a global solution directly to `S` gives the same proof-irrelevant slab occurrence
as first restricting to `T` and then to `S`. -/
theorem SmoothSolution.restrict_trans
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (hST : S ≤ T) :
    SmoothSolutionOn.restrict (SmoothSolution.toSmoothSolutionOn solution hT) hS hST =
      SmoothSolution.toSmoothSolutionOn solution hS := by
  apply Subsingleton.elim

/-! ## Extension and terminal obstruction receivers -/

/-- The bounded solution extends past its terminal face using the same velocity and pressure
world-tube.  Later local-existence work may instead glue a restarted world-tube and prove that its
restriction agrees; this definition records the exact consequence needed at the present carrier. -/
def SmoothSolutionOn.CanExtendPast
    {T ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (_solution : SmoothSolutionOn T ν u₀ force velocity pressure) : Prop :=
  ∃ S, T < S ∧ SmoothSolutionOn S ν u₀ force velocity pressure

/-- A slab obtained by restriction from a strictly longer slab retains that longer slab as an
explicit extension witness. -/
theorem SmoothSolutionOn.restriction_canExtendPast
    {S T ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn S ν u₀ force velocity pressure)
    (hT : 0 < T) (hTS : T < S) :
    (SmoothSolutionOn.restrict solution hT hTS.le).CanExtendPast := by
  exact ⟨S, hTS, solution⟩

/-- Every finite restriction of a global solution has an explicit strictly longer restriction. -/
theorem SmoothSolution.globalRestriction_canExtendPast
    {ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolution ν u₀ force velocity pressure)
    {T : ℝ} (hT : 0 < T) :
    (SmoothSolution.toSmoothSolutionOn solution hT).CanExtendPast := by
  refine ⟨T + 1, by linarith, SmoothSolution.toSmoothSolutionOn solution (by linarith)⟩

/-- The terminal obstruction fibre: the current world-tube admits no strictly longer slab carrying
the same fields.  A later maximal-lifetime construction will quantify over compatible restarted
fields modulo pressure gauge rather than only this same-field extension receiver. -/
def SmoothSolutionOn.IsTerminal
    {T ν : ℝ} {u₀ : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T ν u₀ force velocity pressure) : Prop :=
  ¬ solution.CanExtendPast

section Audit

#print axioms SmoothSolution.toSmoothSolutionOn
#print axioms SmoothSolutionOn.restrict
#print axioms SmoothSolution.restrict_trans
#print axioms SmoothSolutionOn.restriction_canExtendPast
#print axioms SmoothSolution.globalRestriction_canExtendPast

end Audit

end Soma.Holonics.Millennium.NavierStokesFiniteTime
