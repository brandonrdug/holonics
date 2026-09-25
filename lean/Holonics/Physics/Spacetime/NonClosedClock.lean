import Holonics.Aeon.Production.HodgeTime
import Holonics.Physics.Spacetime.Boost

/-!
# Non-closed clocks: Sagnac and the gravitational redshift as production time on a cycle

[definition] Rebuild step 6, K4 (#75, the Lorentz scope of its comment); null-cone record
(2026-09-24) §1, "non-closed clocks read nonzero on cycles". A receiver's clock is a time form on
the passages of a cell complex; an inertial clock is exact, `ω = d(−U·x)`, so its reading is
state time, fixed by the aeon's boundary. A clock with `dω ≠ 0` reads its curvature flux on a cycle
that bounds a cell: that is the **production time** of the owner's Hodge split
(`Aeon/Production/HodgeTime`).

The carrier is the oriented square `0 → 1 → 2 → 3 → 0` with one face (`square`, a
`Foundation/HodgeReceiver.WeightedComplex 4 4 1` in the unit metric), whose loop bounds the face
(`squareLoop_bounds`).

[proved-derived; formal-checked]

* **The inertial clock reads nothing on the cycle** (`inertial_clock_silent`): exact forms are
  silent on cycles (`exact_iff_silent_on_cycles`).
* **Sagnac.** A clock rotating at `Ω` (with `1/c²` absorbed) desynchronizes each straight passage
  `s → t` by `Ω(x_s y_t − x_t y_s)` (`sagnacForm`). Around the loop it reads `2ΩA`, `A` the
  shoelace area (`sagnac_reading`); this is the flux of its curvature through the face
  (`sagnac_is_curvature_flux`), every Hodge split's production part reads it
  (`sagnac_is_production`), and for `ΩA ≠ 0` the clock is not closed and its production part is
  nonzero (`sagnac_not_closed`). On the rectangle `a × b`, `A = ab` (`rectangle_area`).
* **Gravitational redshift.** A static clock `ω = N dt` on the `(t, x)` rectangle, lapse `N₁` at
  `x₁` and `N₂` at `x₂`, reads `N₁Δt`, `0`, `−N₂Δt`, `0` on the four passages (`staticForm`). Around
  the loop it reads `(N₁ − N₂)Δt`, the flux of `dN ∧ dt` (`static_reading`, `static_is_production`),
  and it is not closed when `N₁ ≠ N₂` and `Δt ≠ 0` (`static_not_closed`).
* **The redshift is the owner's rate.** The static receiver at `x₁` reads the coordinate interval
  as the static form's passage `0`, the one at `x₂` as its reversed passage `2`; as clocks on the
  one passage `Boost.segment` (`staticClock`), the owner's `Reading.rate` of the two on
  `Boost.along` is the undivided pair `(N₁Δt : N₂Δt)` read from `staticForm`. For `Δt ≠ 0` and a
  nonzero lapse it is admitted (not `(0 : 0)`) and projectively the lapse ratio `(N₁ : N₂)`
  (`redshift_rate`).

[interpretation] Frame dragging would be the same law for a stationary non-static clock
`ω = N dt − A`, whose cycle reading is the flux of `dA`
(`HodgeTime.cell_boundary_reading_is_curvature_flux`); only the Sagnac case `A = Ω(x dy − y dx)`
is stated here, first order in `Ω` (the passage values are the first-order synchronization gaps).
`[open]` A frame-dragging clock of a stationary spacetime is owed (#62).
-/

noncomputable section

namespace Holonics.Physics.Spacetime.NonClosedClock

open Matrix
open Holonics.Foundation.HodgeReceiver
open Holonics.Aeon.Production.HodgeTime

/-! ## The square -/

/-- [definition] The oriented square `0 → 1 → 2 → 3 → 0`: rows are passages, `−1` at the source and
`+1` at the target. -/
def squareIncidence : Matrix (Fin 4) (Fin 4) ℚ :=
  !![-1, 1, 0, 0; 0, -1, 1, 0; 0, 0, -1, 1; 1, 0, 0, -1]

/-- [definition] The face's boundary: the loop through all four passages. -/
def squareFace : Matrix (Fin 1) (Fin 4) ℚ := !![1, 1, 1, 1]

theorem squareFace_dd : squareFace * squareIncidence = 0 := by
  ext i j; fin_cases i; fin_cases j <;>
    simp [squareFace, squareIncidence, Matrix.mul_apply, Fin.sum_univ_four]

/-- [definition] The filled square, unit metric. -/
def square : WeightedComplex 4 4 1 := unitMetric squareIncidence squareFace squareFace_dd

/-- [definition] The loop around the square, as an aeon's chain. -/
def squareLoop : Fin 4 → ℚ := ![1, 1, 1, 1]

/-- [proved-derived; formal-checked] The loop bounds the face. -/
theorem squareLoop_bounds : cellBoundary square ![1] = squareLoop := by
  ext i; fin_cases i <;> simp [cellBoundary, square, unitMetric, squareFace, squareLoop,
    Matrix.mulVec, dotProduct]

/-- [proved-derived; formal-checked] The loop is a cycle. -/
theorem squareLoop_isCycle : IsCycle square squareLoop := by
  rw [← squareLoop_bounds]; exact cellBoundary_isCycle square _

/-- [proved-derived; formal-checked] **The inertial clock reads nothing on the cycle**: an exact
clock `dφ` is silent on every cycle. -/
theorem inertial_clock_silent (φ : Fin 4 → ℚ) : reading (square.d₀ *ᵥ φ) squareLoop = 0 :=
  (exact_iff_silent_on_cycles square _).mp ⟨φ, rfl⟩ _ squareLoop_isCycle

/-! ## Sagnac -/

/-- [definition] The passages' sources and targets. -/
def src : Fin 4 → Fin 4 := ![0, 1, 2, 3]
def tgt : Fin 4 → Fin 4 := ![1, 2, 3, 0]

/-- [definition] **The rotating clock** at `Ω` on a quadrilateral with vertices `(xᵢ, yᵢ)`: each
straight passage `s → t` desynchronizes by `Ω(x_s y_t − x_t y_s)`. -/
def sagnacForm (Ω : ℚ) (x y : Fin 4 → ℚ) : Fin 4 → ℚ := fun e =>
  Ω * (x (src e) * y (tgt e) - x (tgt e) * y (src e))

/-- [definition] The shoelace area `½ Σ (xᵢ yᵢ₊₁ − xᵢ₊₁ yᵢ)`. -/
def shoelaceArea (x y : Fin 4 → ℚ) : ℚ :=
  (∑ e : Fin 4, (x (src e) * y (tgt e) - x (tgt e) * y (src e))) / 2

/-- [proved-derived; formal-checked] **Sagnac**: the rotating clock reads `2ΩA` around the loop. -/
theorem sagnac_reading (Ω : ℚ) (x y : Fin 4 → ℚ) :
    reading (sagnacForm Ω x y) squareLoop = 2 * Ω * shoelaceArea x y := by
  simp only [reading, sagnacForm, shoelaceArea, squareLoop, dotProduct, Fin.sum_univ_four]
  simp
  ring

/-- [proved-derived; formal-checked] On the rectangle `a × b` the shoelace area is `ab`. -/
theorem rectangle_area (a b : ℚ) : shoelaceArea ![0, a, a, 0] ![0, 0, b, b] = a * b := by
  simp [shoelaceArea, Fin.sum_univ_four, src, tgt]

/-- [proved-derived; formal-checked] The Sagnac reading is the flux of the clock's curvature through
the face (`cell_boundary_reading_is_curvature_flux`). -/
theorem sagnac_is_curvature_flux (Ω : ℚ) (x y : Fin 4 → ℚ) :
    (square.d₁ *ᵥ sagnacForm Ω x y) ⬝ᵥ ![1] = 2 * Ω * shoelaceArea x y := by
  rw [← cell_boundary_reading_is_curvature_flux, squareLoop_bounds, sagnac_reading]

/-- [proved-derived; formal-checked] **The Sagnac reading is production time**: every Hodge split's
production part reads the whole `2ΩA` on the loop (`cell_boundary_reads_production`). -/
theorem sagnac_is_production (Ω : ℚ) (x y : Fin 4 → ℚ) (s : TimeSplit square (sagnacForm Ω x y)) :
    reading s.production squareLoop = 2 * Ω * shoelaceArea x y := by
  rw [← squareLoop_bounds, ← cell_boundary_reads_production square s, squareLoop_bounds,
    sagnac_reading]

/-- [proved-derived; formal-checked] **A rotating clock is not a clock of the aeon**: for `ΩA ≠ 0`
it is not closed, and its production part is nonzero (`production_ne_zero_iff_not_closed`). -/
theorem sagnac_not_closed {Ω : ℚ} {x y : Fin 4 → ℚ} (h : Ω * shoelaceArea x y ≠ 0)
    (s : TimeSplit square (sagnacForm Ω x y)) :
    sagnacForm Ω x y ∉ square.cocycles ∧ s.production ≠ 0 := by
  have hnot : sagnacForm Ω x y ∉ square.cocycles := by
    intro hc
    have := closed_reading_homology_invariant square hc (z' := 0) ![1]
      (by rw [sub_zero, squareLoop_bounds])
    rw [sagnac_reading] at this
    simp [reading] at this
    rcases this with h0 | h0 <;> simp [h0] at h
  exact ⟨hnot, (production_ne_zero_iff_not_closed square s).mpr hnot⟩

/-! ## The gravitational redshift -/

/-- [definition] **A static clock** `ω = N dt` on the `(t, x)` rectangle with vertices
`(t₀, x₁), (t₁, x₁), (t₁, x₂), (t₀, x₂)`: the time passages read `N₁Δt` and `−N₂Δt`, the space
passages nothing. -/
def staticForm (N₁ N₂ Δt : ℚ) : Fin 4 → ℚ := ![N₁ * Δt, 0, -(N₂ * Δt), 0]

/-- [proved-derived; formal-checked] **The static clock reads `(N₁ − N₂)Δt` around the loop**, the
flux of `dN ∧ dt`. -/
theorem static_reading (N₁ N₂ Δt : ℚ) :
    reading (staticForm N₁ N₂ Δt) squareLoop = (N₁ - N₂) * Δt := by
  simp [reading, staticForm, squareLoop, dotProduct, Fin.sum_univ_four]
  ring

/-- [proved-derived; formal-checked] The redshift reading is production time. -/
theorem static_is_production (N₁ N₂ Δt : ℚ) (s : TimeSplit square (staticForm N₁ N₂ Δt)) :
    reading s.production squareLoop = (N₁ - N₂) * Δt := by
  rw [← squareLoop_bounds, ← cell_boundary_reads_production square s, squareLoop_bounds,
    static_reading]

/-- [proved-derived; formal-checked] A static clock with a lapse gradient is not closed. -/
theorem static_not_closed {N₁ N₂ Δt : ℚ} (hN : N₁ ≠ N₂) (ht : Δt ≠ 0)
    (s : TimeSplit square (staticForm N₁ N₂ Δt)) :
    staticForm N₁ N₂ Δt ∉ square.cocycles ∧ s.production ≠ 0 := by
  have hnot : staticForm N₁ N₂ Δt ∉ square.cocycles := by
    intro hc
    have := closed_reading_homology_invariant square hc (z' := 0) ![1]
      (by rw [sub_zero, squareLoop_bounds])
    rw [static_reading] at this
    simp [reading] at this
    rcases this with h | h
    · exact hN (sub_eq_zero.mp h)
    · exact ht h
  exact ⟨hnot, (production_ne_zero_iff_not_closed square s).mpr hnot⟩

/-- [definition] **A static receiver's clock on the one passage**: the reading `a` of the
coordinate interval (`Boost.segment` has no two-cell, so every form is a clock). -/
def staticClock (a : ℚ) : Holonics.Aeon.Clock.Reading.Clock Holonics.Physics.Spacetime.Boost.segment ℚ :=
  ⟨fun _ => a, fun f => f.elim⟩

/-- [proved-derived; formal-checked] **The redshift is the owner's rate of two static clocks.**
The receiver at `x₁` reads the interval as passage `0` of the static form, the one at `x₂` as the
reversed passage `2`; the owner's rate of the two on the passage is the undivided pair
`(N₁Δt : N₂Δt)`. For `Δt ≠ 0` and `(N₁, N₂) ≠ (0, 0)` it is admitted and projectively the lapse
ratio `(N₁ : N₂)`. -/
theorem redshift_rate {N₁ N₂ Δt : ℚ} (ht : Δt ≠ 0) (hN : N₁ ≠ 0 ∨ N₂ ≠ 0) :
    Holonics.Aeon.Clock.Reading.rate (staticClock (staticForm N₁ N₂ Δt 0))
        (staticClock (-staticForm N₁ N₂ Δt 2)) Holonics.Physics.Spacetime.Boost.along =
        ⟨N₁ * Δt, N₂ * Δt⟩ ∧
      Holonics.Aeon.Clock.Reading.Admitted (⟨N₁ * Δt, N₂ * Δt⟩ : RatioPresentation ℚ) ∧
      (⟨N₁ * Δt, N₂ * Δt⟩ : RatioPresentation ℚ).ProjectivelyEq ⟨N₁, N₂⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Holonics.Aeon.Clock.Reading.rate, Holonics.Aeon.Clock.Reading.reading,
      Holonics.Physics.Spacetime.Boost.along, Holonics.Aeon.Clock.Reading.wordReading,
      Holonics.Aeon.Clock.Reading.stepReading, staticClock, staticForm]
  · rcases hN with h | h
    · exact Or.inl (mul_ne_zero h ht)
    · exact Or.inr (mul_ne_zero h ht)
  · unfold RatioPresentation.ProjectivelyEq
    ring

section Audit

#print axioms squareLoop_bounds
#print axioms inertial_clock_silent
#print axioms sagnac_reading
#print axioms rectangle_area
#print axioms sagnac_is_curvature_flux
#print axioms sagnac_is_production
#print axioms sagnac_not_closed
#print axioms static_reading
#print axioms static_is_production
#print axioms static_not_closed
#print axioms redshift_rate

end Audit

end Holonics.Physics.Spacetime.NonClosedClock
