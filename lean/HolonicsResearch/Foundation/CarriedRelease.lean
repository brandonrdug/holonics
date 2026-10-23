import Holonics.Aeon.Clock.Winding
import Mathlib.Algebra.Order.Round
import Mathlib.Tactic

/-!
# The carried release: a stream released onto a grid keeps its residue

[proved-derived; formal-checked] October 22
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
7. **The transported release keeps the exact orbit** (`transportedRelease_conserves`,
   `transportedRelease_residue`, `transportedRelease_tracks`): a state moved by any transport `T`
   and driven by `δ`, released each step with its residue carried (`e' = T(q + e) + δ − q'`, codec
   error feedback), has lattice part plus residue equal to the exact orbit, the residue inside one
   step, so the lattice part tracks the orbit within one step at every length.
   [counterexample] Plain rounding of a transported state holds a drive below half a step at zero
   forever (`plainTransported_silences`), while the damped exact orbit reaches `x (1 − ρᵗ)/(1 − ρ)`
   (`exactOrbit_damped`).
8. **The transported residue in any module** (`residueRun_conserves`): for a linear transport `A`
   and any release rule, the lattice part `A q + q_rel` and the residue `e' = A e + Δ − q_rel`
   sum to the exact orbit at every length.

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

/-- [proved-derived; formal-checked] **The step error is a coboundary:** `y − x = r − r'`. -/
theorem release_step_error (r x : R) :
    (windings (r + x) : R) - x = r - openPhase (r + x) := by
  have h := (reading_split (r + x)).1
  linarith

/-- [proved-derived; formal-checked] **The carried release conserves:** `Σ y + r_n = r_0 + Σ x`. -/
theorem release_conserves (r : R) (xs : List R) :
    (((releaseRun r xs).1.sum : ℤ) : R) + (releaseRun r xs).2 = r + xs.sum := by
  induction xs generalizing r with
  | nil => simp [releaseRun]
  | cons x xs ih =>
    have h := ih (openPhase (r + x))
    have hs := (reading_split (r + x)).1
    simp only [releaseRun, List.sum_cons, Int.cast_add]
    linarith

/-- [proved-derived; formal-checked] **The residue stays inside one grid step.** -/
theorem release_residue_bounds (r : R) (h0 : 0 ≤ r) (h1 : r < 1) (xs : List R) :
    0 ≤ (releaseRun r xs).2 ∧ (releaseRun r xs).2 < 1 := by
  induction xs generalizing r with
  | nil => simpa only [releaseRun] using And.intro h0 h1
  | cons x xs ih =>
    simp only [releaseRun]
    exact ih (openPhase (r + x)) (reading_split (r + x)).2.1 (reading_split (r + x)).2.2

/-- [proved-derived; formal-checked] **The released sum tracks the stream within one grid step.** -/
theorem release_tracks (r : R) (h0 : 0 ≤ r) (h1 : r < 1) (xs : List R) :
    |(((releaseRun r xs).1.sum : ℤ) : R) - xs.sum| < 1 := by
  have hc := release_conserves r xs
  have hb := release_residue_bounds r h0 h1 xs
  rw [abs_lt]
  constructor <;> linarith [hb.1, hb.2]

/-- [proved-derived; formal-checked] **The release is the winding of the running sum**, and the residue is its
open phase. -/
theorem release_is_winding_of_running_sum (r : R) (h0 : 0 ≤ r) (h1 : r < 1) (xs : List R) :
    (releaseRun r xs).1.sum = windings (r + xs.sum) ∧
      (releaseRun r xs).2 = openPhase (r + xs.sum) :=
  split_unique _ _ (release_conserves r xs) (release_residue_bounds r h0 h1 xs).1
    (release_residue_bounds r h0 h1 xs).2

/-- [counterexample; formal-checked] **Plain rounding annihilates a constant reading below half a grid step.** -/
theorem plain_rounding_silences {x : R} (h0 : 0 ≤ x) (h1 : x < 1 / 2) (n : ℕ) :
    ((List.replicate n x).map round).sum = 0 := by
  have hz : round x = (0 : ℤ) := by
    rw [round_eq, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith
  simp [hz]

/-- [proved-derived; formal-checked] **The carried release keeps the rate** of the same constant reading. -/
theorem release_keeps_constant_rate (x : R) (n : ℕ) :
    (n : R) * x - 1 < (((releaseRun 0 (List.replicate n x)).1.sum : ℤ) : R) := by
  have hc := release_conserves (0 : R) (List.replicate n x)
  have hb := release_residue_bounds (0 : R) le_rfl zero_lt_one (List.replicate n x)
  rw [List.sum_replicate, nsmul_eq_mul, zero_add] at hc
  linarith [hb.2]

/-- [proved-derived; formal-checked] **A bound is released outward,** and the outward pair widens the band by less
than two grid steps. -/
theorem outward_release {l x u : R} (hl : l ≤ x) (hu : x ≤ u) :
    ((⌊l⌋ : ℤ) : R) ≤ x ∧ x ≤ ((⌈u⌉ : ℤ) : R) ∧
      ((⌈u⌉ : ℤ) : R) - ((⌊l⌋ : ℤ) : R) < u - l + 2 := by
  refine ⟨(Int.floor_le l).trans hl, hu.trans (Int.le_ceil u), ?_⟩
  have h1 := Int.ceil_lt_add_one u
  have h2 := Int.lt_floor_add_one l
  linarith

/-! ## The transported release

A state moved by a transport `T` each step and driven by `δ t`, released onto the grid with its
residue carried, keeps the exact orbit: the released lattice part plus the residue is the orbit,
for every transport. Plain rounding of a damped state instead holds a drive below half a step at
zero forever, while the exact orbit grows toward `x / (1 − ρ)`. This is codec error feedback
`e' = A e + Δ − q` read as the carried release. -/

/-- [definition] One step of the transported release: move the whole state, add the drive, and
release onto the grid with the residue carried. -/
def releaseStep (T : R → R) (δ : R) (p : ℤ × R) : ℤ × R :=
  (windings (T ((p.1 : R) + p.2) + δ), openPhase (T ((p.1 : R) + p.2) + δ))

/-- [definition] **The transported carried release** from rest: lattice part and residue. -/
def transportedRelease (T : R → R) (δ : ℕ → R) : ℕ → ℤ × R
  | 0 => (0, 0)
  | t + 1 => releaseStep T (δ t) (transportedRelease T δ t)

/-- [definition] The exact orbit of the same transport and drive. -/
def exactOrbit (T : R → R) (δ : ℕ → R) : ℕ → R
  | 0 => 0
  | t + 1 => T (exactOrbit T δ t) + δ t

/-- [proved-derived; formal-checked] One step conserves: lattice part plus residue is the moved
state plus the drive. -/
theorem releaseStep_conserves (T : R → R) (δ : R) (p : ℤ × R) :
    ((releaseStep T δ p).1 : R) + (releaseStep T δ p).2 = T ((p.1 : R) + p.2) + δ :=
  (reading_split _).1

/-- [proved-derived; formal-checked] **The transported release conserves:** lattice part plus
residue is the exact orbit, for every transport `T`. -/
theorem transportedRelease_conserves (T : R → R) (δ : ℕ → R) (t : ℕ) :
    ((transportedRelease T δ t).1 : R) + (transportedRelease T δ t).2 = exactOrbit T δ t := by
  induction t with
  | zero => simp [transportedRelease, exactOrbit]
  | succ t ih =>
    simp only [transportedRelease, exactOrbit]
    rw [releaseStep_conserves, ih]

/-- [proved-derived; formal-checked] **The residue stays inside one grid step.** -/
theorem transportedRelease_residue (T : R → R) (δ : ℕ → R) (t : ℕ) :
    0 ≤ (transportedRelease T δ t).2 ∧ (transportedRelease T δ t).2 < 1 := by
  cases t with
  | zero => simp [transportedRelease]
  | succ t =>
    simp only [transportedRelease, releaseStep]
    exact ⟨(reading_split _).2.1, (reading_split _).2.2⟩

/-- [proved-derived; formal-checked] **The released lattice part tracks the exact orbit within one
grid step**, at every length and for every transport. -/
theorem transportedRelease_tracks (T : R → R) (δ : ℕ → R) (t : ℕ) :
    |((transportedRelease T δ t).1 : R) - exactOrbit T δ t| < 1 := by
  have hc := transportedRelease_conserves T δ t
  have hb := transportedRelease_residue T δ t
  rw [abs_lt]
  constructor <;> linarith [hb.1, hb.2]

/-- [definition] Plain rounding of a transported state, with no residue carried. -/
def plainTransported (T : R → R) (δ : ℕ → R) : ℕ → ℤ
  | 0 => 0
  | t + 1 => round (T (plainTransported T δ t : R) + δ t)

/-- [counterexample; formal-checked] **Plain rounding of a transported state silences a drive below
half a step**, for every transport fixing zero. -/
theorem plainTransported_silences {T : R → R} (hT : T 0 = 0) {x : R} (h0 : 0 ≤ x)
    (h1 : x < 1 / 2) (t : ℕ) : plainTransported T (fun _ => x) t = 0 := by
  induction t with
  | zero => simp [plainTransported]
  | succ t ih =>
    simp only [plainTransported, ih, Int.cast_zero, hT, zero_add]
    rw [round_eq, Int.floor_eq_iff]
    constructor <;> push_cast <;> linarith

/-- [proved-derived; formal-checked] **The damped exact orbit of the same drive grows:**
`(1 − ρ) x_t = x (1 − ρᵗ)`, so for `0 ≤ ρ < 1` it approaches `x / (1 − ρ)`, which is five grid
steps at `ρ = 9/10` and `x` just below half a step. -/
omit [FloorRing R] in
theorem exactOrbit_damped (ρ x : R) (t : ℕ) :
    (1 - ρ) * exactOrbit (fun z => ρ * z) (fun _ => x) t = x * (1 - ρ ^ t) := by
  induction t with
  | zero => simp [exactOrbit]
  | succ t ih =>
    simp only [exactOrbit]
    linear_combination ρ * ih

/-! ### The transported residue in any module -/

section TransportedResidue

variable {M : Type*} [AddCommGroup M]

/-- [definition] **The transported residue** `e' = A e + Δ − q`: the lattice part moves by `A` and
takes the released quantum `q = rel (A e + Δ)`, and the residue keeps the rest. Every release rule
`rel` is admitted; with the floor rule on a line the residue stays inside one step
(`transportedRelease_residue`). -/
def residueRun (A : M →+ M) (Δ : ℕ → M) (rel : M → M) : ℕ → M × M
  | 0 => (0, 0)
  | t + 1 => (A (residueRun A Δ rel t).1 + rel (A (residueRun A Δ rel t).2 + Δ t),
      A (residueRun A Δ rel t).2 + Δ t - rel (A (residueRun A Δ rel t).2 + Δ t))

/-- [definition] The exact orbit of a linear transport `A` driven by `Δ`, from rest. -/
def linearOrbit (A : M →+ M) (Δ : ℕ → M) : ℕ → M
  | 0 => 0
  | t + 1 => A (linearOrbit A Δ t) + Δ t

/-- [proved-derived; formal-checked] **The transported residue conserves:** lattice part plus
residue is the exact orbit, whatever the release rule. -/
theorem residueRun_conserves (A : M →+ M) (Δ : ℕ → M) (rel : M → M) (t : ℕ) :
    (residueRun A Δ rel t).1 + (residueRun A Δ rel t).2 = linearOrbit A Δ t := by
  induction t with
  | zero => simp [residueRun, linearOrbit]
  | succ t ih =>
    simp only [residueRun, linearOrbit]
    rw [← ih, map_add]
    abel

end TransportedResidue

end Holonics.Aeon.Clock.Winding
