import Holonics.Aeon.Clock.Winding
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!
# The carried release: a stream released onto a grid keeps its residue

[proved-derived] October 22
([record](../../../research/records/2026-10-22_ORDER_IS_TORSION_AND_SUBGRAIN_INFORMATION_DISSOLVES_INTO_THE_CARRIED_RESIDUE.md)).
A stream of readings `x₁, x₂, …` released onto a grid (the unit grid here; a grid `g > 0` is the
unit grid of `x / g`) either rounds each reading alone or carries the residue:

```text
y_k = windings (r_(k−1) + x_k) ,   r_k = openPhase (r_(k−1) + x_k) = r_(k−1) + x_k − y_k
```

The HNN deposit's own release is `HNN/LatticeDeposit` (nearest point, a remainder carried on a
grain that refines with the locus's clock, and a Kraft-budgeted release). This module is the
release-free floor chart of the same accounting, joined to the clock owner's split.

What is proved.

1. **The carried release conserves** (`release_conserves`): `Σ y + r_n = r_0 + Σ x` exactly, for
   every stream.
2. **The residue stays inside one grid step** (`release_residue_bounds`), so the released sum
   tracks the stream within one step at every length (`release_tracks`).
3. **The release is the winding of the running sum** (`release_is_winding_of_running_sum`): with
   `0 ≤ r_0 < 1`, the released total is `windings (r_0 + Σ x)` and the residue is its open phase
   (`Aeon/Clock/Winding.split_unique`).
4. **The step error is a coboundary** (`release_step_error`): `y_k − x_k = r_(k−1) − r_k`, which
   telescopes on every closed window.
5. **Plain rounding annihilates, the carry dissolves** (`plain_rounding_silences`,
   `release_keeps_constant_rate`): a constant reading `0 ≤ x < 1/2` rounds to nothing at every
   step, while the carried release of `n` copies releases more than `n x − 1`. Information below
   the grid is held in the residue and reappears as a rate.
6. **A bound is released outward** (`outward_release`): `⌊l⌋ ≤ x ≤ ⌈u⌉` whenever `l ≤ x ≤ u`, and
   the outward pair widens the band by less than two grid steps.

No `sorry`, no `axiom`.
-/

noncomputable section

namespace Holonics.Aeon.Clock.Winding

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [FloorRing R]

/-- [definition] **The carried release** of a stream from the residue `r`: the released whole
steps and the final residue. -/
def releaseRun : R → List R → List ℤ × R
  | r, [] => ([], r)
  | r, x :: xs =>
      (windings (r + x) :: (releaseRun (openPhase (r + x)) xs).1,
        (releaseRun (openPhase (r + x)) xs).2)

/-- [proved-derived] **The step error is a coboundary:** `y − x = r − r'`. -/
theorem release_step_error (r x : R) :
    (windings (r + x) : R) - x = r - openPhase (r + x) := by
  have h := (reading_split (r + x)).1
  linarith

/-- [proved-derived] **The carried release conserves:** `Σ y + r_n = r_0 + Σ x`. -/
theorem release_conserves (r : R) (xs : List R) :
    (((releaseRun r xs).1.sum : ℤ) : R) + (releaseRun r xs).2 = r + xs.sum := by
  induction xs generalizing r with
  | nil => simp [releaseRun]
  | cons x xs ih =>
    have h := ih (openPhase (r + x))
    have hs := (reading_split (r + x)).1
    simp only [releaseRun, List.sum_cons, Int.cast_add]
    linarith

/-- [proved-derived] **The residue stays inside one grid step.** -/
theorem release_residue_bounds (r : R) (h0 : 0 ≤ r) (h1 : r < 1) (xs : List R) :
    0 ≤ (releaseRun r xs).2 ∧ (releaseRun r xs).2 < 1 := by
  induction xs generalizing r with
  | nil => simpa only [releaseRun] using And.intro h0 h1
  | cons x xs ih =>
    simp only [releaseRun]
    exact ih (openPhase (r + x)) (reading_split (r + x)).2.1 (reading_split (r + x)).2.2

/-- [proved-derived] **The released sum tracks the stream within one grid step.** -/
theorem release_tracks (r : R) (h0 : 0 ≤ r) (h1 : r < 1) (xs : List R) :
    |(((releaseRun r xs).1.sum : ℤ) : R) - xs.sum| < 1 := by
  have hc := release_conserves r xs
  have hb := release_residue_bounds r h0 h1 xs
  rw [abs_lt]
  constructor <;> linarith [hb.1, hb.2]

/-- [proved-derived] **The release is the winding of the running sum**, and the residue is its
open phase. -/
theorem release_is_winding_of_running_sum (r : R) (h0 : 0 ≤ r) (h1 : r < 1) (xs : List R) :
    (releaseRun r xs).1.sum = windings (r + xs.sum) ∧
      (releaseRun r xs).2 = openPhase (r + xs.sum) :=
  split_unique _ _ (release_conserves r xs) (release_residue_bounds r h0 h1 xs).1
    (release_residue_bounds r h0 h1 xs).2

/-- [counterexample] **Plain rounding annihilates a constant reading below half a grid step.** -/
theorem plain_rounding_silences {x : R} (h0 : 0 ≤ x) (h1 : x < 1 / 2) (n : ℕ) :
    ((List.replicate n x).map round).sum = 0 := by
  have hz : round x = (0 : ℤ) := by
    rw [round_eq, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  simp [hz]

/-- [proved-derived] **The carried release keeps the rate** of the same constant reading. -/
theorem release_keeps_constant_rate (x : R) (n : ℕ) :
    (n : R) * x - 1 < (((releaseRun 0 (List.replicate n x)).1.sum : ℤ) : R) := by
  have hc := release_conserves (0 : R) (List.replicate n x)
  have hb := release_residue_bounds (0 : R) le_rfl zero_lt_one (List.replicate n x)
  rw [List.sum_replicate, nsmul_eq_mul, zero_add] at hc
  linarith [hb.2]

/-- [proved-derived] **A bound is released outward,** and the outward pair widens the band by less
than two grid steps. -/
theorem outward_release {l x u : R} (hl : l ≤ x) (hu : x ≤ u) :
    ((⌊l⌋ : ℤ) : R) ≤ x ∧ x ≤ ((⌈u⌉ : ℤ) : R) ∧
      ((⌈u⌉ : ℤ) : R) - ((⌊l⌋ : ℤ) : R) < u - l + 2 := by
  refine ⟨(Int.floor_le l).trans hl, hu.trans (Int.le_ceil u), ?_⟩
  have h1 := Int.ceil_lt_add_one u
  have h2 := Int.lt_floor_add_one l
  linarith

end Holonics.Aeon.Clock.Winding
