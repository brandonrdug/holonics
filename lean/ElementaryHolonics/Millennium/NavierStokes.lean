import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Navier–Stokes existence and smoothness — the four official alternatives

This module imports the actual three-dimensional velocity, pressure, forcing, differential,
periodicity, decay, and energy objects absent from the finite `Crossings`, `Caloric`, and
`WindingLedger` mechanisms. Its statement shape is aligned with Fefferman's Clay problem and the
Lean 4.27 `google-deepmind/formal-conjectures` interface, but open conclusions are definitions of
`Prop`, not `sorry`-backed theorems.

The official target accepts a proof of any one of four alternatives: global smooth existence on
`ℝ³`, global smooth periodic existence, breakdown on `ℝ³`, or periodic breakdown. The pressure is
periodic in the periodic alternatives, following the Clay erratum. No theorem here selects or
proves an alternative.
-/

noncomputable section

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokes

/-- Three-dimensional Euclidean space. -/
abbrev Space := EuclideanSpace ℝ (Fin 3)

/-- A spatial velocity field. -/
abbrev InitialVelocity := Space → Space

/-- A time-dependent velocity or force, with position preceding time. -/
abbrev VelocityField := Space → ℝ → Space

/-- A time-dependent pressure. -/
abbrev PressureField := Space → ℝ → ℝ

/-- The divergence of a spatial velocity field, computed as the trace of its derivative. -/
def divergence (velocity : InitialVelocity) (x : Space) : ℝ :=
  (fderiv ℝ velocity x).trace ℝ Space

/-- Spatial 1-periodicity in every coordinate. -/
def IsOnePeriodic {α : Sort*} (field : Space → α) : Prop :=
  ∀ x i, field (x + EuclideanSpace.single i 1) = field x

/-- Smooth incompressible initial data. -/
structure InitialVelocityCondition (u₀ : InitialVelocity) : Prop where
  divergenceFree : ∀ x, divergence u₀ x = 0
  smooth : ContDiff ℝ ∞ u₀

/-- Initial data on `ℝ³` satisfying Fefferman's rapid spatial decay condition. -/
structure InitialVelocityConditionDecay (u₀ : InitialVelocity) : Prop
    extends InitialVelocityCondition u₀ where
  decay : ∀ derivativeOrder : ℕ, ∀ decayOrder : ℝ,
    ∃ C : ℝ, ∀ x,
      ‖iteratedFDeriv ℝ derivativeOrder u₀ x‖ ≤ C / (1 + ‖x‖) ^ decayOrder

/-- Smooth, incompressible, spatially periodic initial data. -/
structure InitialVelocityConditionPeriodic (u₀ : InitialVelocity) : Prop
    extends InitialVelocityCondition u₀ where
  periodic : IsOnePeriodic u₀

/-- Smooth forcing on the nonnegative time half-line. -/
structure ForceCondition (force : VelocityField) : Prop where
  smooth : ContDiffOn ℝ ∞ (Function.uncurry force) (Set.univ ×ˢ Set.Ici 0)

/-- Smooth forcing on `ℝ³`, rapidly decreasing in space and time. -/
structure ForceConditionDecay (force : VelocityField) : Prop extends ForceCondition force where
  decay : ∀ derivativeOrder : ℕ, ∀ decayOrder : ℝ,
    ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
      ‖iteratedFDerivWithin ℝ derivativeOrder (Function.uncurry force)
          (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤
        C / (1 + ‖x‖ + t) ^ decayOrder

/-- Smooth spatially periodic forcing, rapidly decreasing in time. -/
structure ForceConditionPeriodic (force : VelocityField) : Prop extends ForceCondition force where
  periodic : ∀ t ≥ 0, IsOnePeriodic (fun x => force x t)
  decay : ∀ derivativeOrder : ℕ, ∀ decayOrder : ℝ,
    ∃ C : ℝ, ∀ x, ∀ t ≥ 0,
      ‖iteratedFDerivWithin ℝ derivativeOrder (Function.uncurry force)
          (Set.univ ×ˢ Set.Ici 0) (x, t)‖ ≤
        C / (1 + t) ^ decayOrder

/-- A global smooth solution of the incompressible Navier–Stokes PDE on nonnegative time. -/
structure SmoothSolution
    (ν : ℝ) (u₀ : InitialVelocity) (force : VelocityField)
    (velocity : VelocityField) (pressure : PressureField) : Prop where
  momentum : ∀ x, ∀ t ≥ 0,
    derivWithin (velocity x) (Set.Ici 0) t +
        fderiv ℝ (fun y => velocity y t) x (velocity x t) =
      ν • Δ (fun y => velocity y t) x -
        gradient (fun y => pressure y t) x + force x t
  incompressible : ∀ x, ∀ t ≥ 0, divergence (fun y => velocity y t) x = 0
  initial : ∀ x, velocity x 0 = u₀ x
  velocitySmooth :
    ContDiffOn ℝ ∞ (Function.uncurry velocity) (Set.univ ×ˢ Set.Ici 0)
  pressureSmooth :
    ContDiffOn ℝ ∞ (Function.uncurry pressure) (Set.univ ×ˢ Set.Ici 0)

/-- Uniformly bounded kinetic energy on `ℝ³`, with integrability stated separately so the
totalized Bochner integral cannot hide a divergent population. -/
def UniformlyBoundedEnergy (velocity : VelocityField) : Prop :=
  ∃ E : ℝ, ∀ t ≥ 0,
    Integrable (fun x : Space => ‖velocity x t‖ ^ 2) ∧
      (∫ x : Space, ‖velocity x t‖ ^ 2) < E

/-- A physically reasonable global solution on all of `ℝ³`. -/
structure WholeSpaceSolution
    (ν : ℝ) (u₀ : InitialVelocity) (force : VelocityField)
    (velocity : VelocityField) (pressure : PressureField) : Prop
    extends SmoothSolution ν u₀ force velocity pressure where
  boundedEnergy : UniformlyBoundedEnergy velocity

/-- A physically reasonable global solution on the three-torus chart. -/
structure PeriodicSolution
    (ν : ℝ) (u₀ : InitialVelocity) (force : VelocityField)
    (velocity : VelocityField) (pressure : PressureField) : Prop
    extends SmoothSolution ν u₀ force velocity pressure where
  velocityPeriodic : ∀ t ≥ 0, IsOnePeriodic (fun x => velocity x t)
  pressurePeriodic : ∀ t ≥ 0, IsOnePeriodic (fun x => pressure x t)

/-- Alternative A: every admitted rapidly decreasing initial current on `ℝ³` has a global smooth
zero-force solution of uniformly bounded energy. -/
def StatementA : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : InitialVelocity, InitialVelocityConditionDecay u₀ →
    ∃ velocity pressure, WholeSpaceSolution ν u₀ 0 velocity pressure

/-- Alternative B: every admitted periodic initial current has a global smooth periodic
zero-force solution. -/
def StatementB : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ u₀ : InitialVelocity, InitialVelocityConditionPeriodic u₀ →
    ∃ velocity pressure, PeriodicSolution ν u₀ 0 velocity pressure

/-- Alternative C: admitted data and forcing on `ℝ³` for which no global physically reasonable
solution exists. -/
def StatementC : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∃ (u₀ : InitialVelocity) (force : VelocityField),
      InitialVelocityConditionDecay u₀ ∧ ForceConditionDecay force ∧
        ¬ ∃ velocity pressure, WholeSpaceSolution ν u₀ force velocity pressure

/-- Alternative D: admitted periodic data and forcing for which no global periodic smooth solution
exists. -/
def StatementD : Prop :=
  ∀ ν : ℝ, 0 < ν →
    ∃ (u₀ : InitialVelocity) (force : VelocityField),
      InitialVelocityConditionPeriodic u₀ ∧ ForceConditionPeriodic force ∧
        ¬ ∃ velocity pressure, PeriodicSolution ν u₀ force velocity pressure

/-- **The official Navier–Stokes prize target:** prove at least one of A, B, C, or D. -/
def TheOfficialNavierStokesProblem : Prop :=
  StatementA ∨ StatementB ∨ StatementC ∨ StatementD

end Soma.Holonics.Millennium.NavierStokes
