import ElementaryHolonics.Millennium.NavierStokesOpenCompactWeightedPath

/-!
# One coherent weighted smooth tower on a compact open-solution interval

**[proved-derived; formal-checked]**  Let `[a,b]` lie strictly inside the lifespan of an
unforced periodic open solution, with positive viscosity.  The actual slice at `a` supplies one
compatible all-order native Sobolev tower.  The actual compact `H³` path based at that slice is
already a fixed point of the native mild map.  Finite-aperture higher-order persistence therefore
returns one coherent weighted smooth path tower over the whole relative interval `[0,b-a]`, with
the existing arbitrary-order fixed-point identities and explicit finite-aperture norm bounds.

This is a compact-interior bridge.  It uses neither a terminal bound nor a global continuation
premise, and it does not identify a compact-interior envelope with a terminally uniform one.
-/

noncomputable section

open Function Set
open scoped NNReal

namespace Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedTower

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedPath
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedTower
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteApertureHigherOrderPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFractionalVolterraPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedHigherOrderMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothSliceReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## The exact left-slice initial tower -/

/-- The actual smooth slice at the left endpoint, retained at every finite native weighted
Sobolev order. -/
def compactOpenInitialCompatibleNativeWeightedSobolevTower
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    CompatibleNativeWeightedSobolevTower :=
  smoothSliceCompatibleNativeWeightedSobolevTower
    (fun x ↦ velocity x a)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution
      ⟨ha, lt_of_le_of_lt hab hbT⟩)
    (solution.velocityPeriodic a ⟨ha.le, lt_of_le_of_lt hab hbT⟩)

/-- The base of the left-slice tower is literally the native state which bases the compact mild
path. -/
theorem compactOpenInitialCompatibleNativeWeightedSobolevTower_base
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    (compactOpenInitialCompatibleNativeWeightedSobolevTower
      solution ha hab hbT).base =
      openVelocityWeightedH3State solution
        ⟨a, ha, lt_of_le_of_lt hab hbT⟩ := by
  rfl

/-! ## Whole-compact-interval coherent persistence -/

/-- The actual compact path admits one coherent all-order native tower on its whole aperture.
Every order retains both its exact higher-order mild recurrence and its explicit finite-aperture
norm envelope. -/
theorem exists_compactOpenCoherentWeightedSmoothPathTower
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    ∃ tower : CoherentWeightedSmoothPathTower
        (compactOpenVelocityWeightedH3Path solution ha hab hbT),
      (∀ m : ℕ, IsFixedPt
        (higherOrderMildMap (m + 2) (by omega)
          (Real.toNNReal nu) (real_toNNReal_pos hnu) (sub_nonneg.mpr hab)
          ((compactOpenInitialCompatibleNativeWeightedSobolevTower
            solution ha hab hbT).lift m))
          (tower.lift m)) ∧
      (∀ m : ℕ, ‖tower.lift m‖ ≤
        higherOrderFiniteApertureBound (m + 2) nu
          ‖compactOpenVelocityWeightedH3Path solution ha hab hbT‖ (b - a)
          ((compactOpenInitialCompatibleNativeWeightedSobolevTower
            solution ha hab hbT).lift m)) := by
  let initialTower :=
    compactOpenInitialCompatibleNativeWeightedSobolevTower
      solution ha hab hbT
  have hfixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (sub_nonneg.mpr hab) initialTower.base)
      (compactOpenVelocityWeightedH3Path solution ha hab hbT) := by
    rw [show initialTower.base =
        openVelocityWeightedH3State solution
          ⟨a, ha, lt_of_le_of_lt hab hbT⟩ by
      exact compactOpenInitialCompatibleNativeWeightedSobolevTower_base
        solution ha hab hbT]
    exact compactOpenVelocityWeightedH3Path_isFixedPt
      solution hnu ha hab hbT
  simpa only [initialTower] using
    (exists_coherentWeightedSmoothPathTower_of_nativeFixed
      hnu (sub_nonneg.mpr hab) initialTower
        (compactOpenVelocityWeightedH3Path solution ha hab hbT) hfixed)

section Audit

#print axioms compactOpenInitialCompatibleNativeWeightedSobolevTower_base
#print axioms exists_compactOpenCoherentWeightedSmoothPathTower

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedTower
