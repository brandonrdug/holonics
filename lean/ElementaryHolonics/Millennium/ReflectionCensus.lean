import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Tactic

/-!
# ReflectionCensus: the reflection integrates the frame census, and the sighted frames read
# the Gaussian winding

The analytic side of the Birch–Swinnerton-Dyer question enters the tree.  Its atoms are the
frame counts `#E(𝔽_p)`, and for the curves this route lives on — `y² = x³ + ax`, the odd
cubics, carrying the quarter-turn `(x, y) ↦ (−x, iy)` — the counts are **phase readings**:

* **A half-turn prime (`p ≡ 3 mod 4`) is a blind frame**: its field cannot represent the
  quarter-turn (`theQuarterTurnIsInvisible`), so the frame is an intensity receiver and the
  count's deviation vanishes.  `theReflectionIntegratesTheCensus`: the affine census is
  exactly `p` — for **every** odd cubic at once, every half-turn prime at once.  The whole
  proof is one reflection: the ordinate-fiber count is `1 + χ(x³ + ax)` by the quadratic
  character, the cubic is odd, `χ(−1) = −1`, so the summand is an odd function on the frame
  and the sum over the loop vanishes.  This is integration by reflection enacted on the exact
  object the L-function is assembled from: the trapezoid-on-the-loop mechanism — a census at
  equal spacing over a closed frame, exact because reflection deletes the deviation — read on
  arithmetic material.
* **A sighted prime (`p ≡ 1 mod 4`) splits in the Gaussian lattice**
  (`theSightedPrimeSplitsInTheGaussianLattice`, `p = a² + b²`), and its count deviation is
  the winding readout `a_p = ±2a` — verified here as exact kernel computations at the
  controls `p = 13, 17, 29` (`theSightedFrameReadsTheWinding`,
  `theWindingAgreesAtTheControls`), with the quadratic twist by five flipping the sign
  exactly where five is a non-residue (`theTwistFlipsTheSign`).  The sign law (which of
  `±2a`, by the quartic residue of `a` — Gauss) is classical and cited, not proved.
* The blind-frame controls at `7, 11, 19` (`theBlindFrameControls`) are instances of the
  general theorem recomputed by brute kernel enumeration — the theorem and the enumeration
  agree.

The census here counts the affine equation over the frame; at a prime dividing the
discriminant (five, for `a = −25`) the count is still `p`, but the curve is singular there
and the reading is not a supersingular trace — the boundary is carried, not blurred.

Every `theorem` is discharged and none depends on `sorryAx`.  **Boundary**: nothing about
the L-function as an analytic object, nothing about modularity, and nothing about the
Birch–Swinnerton-Dyer conjecture; these are its atoms, exact.
-/

namespace Soma.Holonics.Millennium.ReflectionCensus

open Finset

variable (p : ℕ) [Fact p.Prime]

/-- **The quarter-turn is invisible to a half-turn prime's frame**: no square root of minus
one exists there.  The frame is an intensity receiver for the curve's complex multiplication
phase. -/
theorem theQuarterTurnIsInvisible (hp : p % 4 = 3) : ¬ IsSquare (-1 : ZMod p) := by
  rw [FiniteField.isSquare_neg_one_iff, ZMod.card]
  omega

private lemma ringChar_ne_two (hp : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

private lemma chi_neg_one (hp : p % 4 = 3) : quadraticChar (ZMod p) (-1) = -1 :=
  quadraticChar_neg_one_iff_not_isSquare.mpr (theQuarterTurnIsInvisible p hp)

/-- The ordinate fiber over an abscissa is counted by the quadratic character:
`#{y : y² = c} = 1 + χ(c)`. -/
private lemma fiber_count (hp : p % 4 = 3) (c : ZMod p) :
    ((univ.filter fun y : ZMod p => y ^ 2 = c).card : ℤ)
      = quadraticChar (ZMod p) c + 1 := by
  have h := quadraticChar_card_sqrts (ringChar_ne_two p hp) c
  have hset : ({x : ZMod p | x ^ 2 = c} : Set (ZMod p)).toFinset
      = univ.filter fun y : ZMod p => y ^ 2 = c := Set.toFinset_setOf _
  rw [← hset]
  exact_mod_cast h

/-- An odd function on the frame sums to zero: the reflection `x ↦ −x` integrates it. -/
private lemma sum_odd_vanishes (g : ZMod p → ℤ) (hodd : ∀ x, g (-x) = -g x) :
    ∑ x : ZMod p, g x = 0 := by
  have h1 : ∑ x : ZMod p, g x = ∑ x : ZMod p, g (-x) :=
    Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun x => by
      rw [Equiv.neg_apply, neg_neg]
  have h2 : ∑ x : ZMod p, g (-x) = -∑ x : ZMod p, g x := by
    simp_rw [hodd]
    rw [Finset.sum_neg_distrib]
  omega

/-- **THE REFLECTION INTEGRATES THE CENSUS**: over a half-turn prime's frame, the affine
census of every odd cubic `y² = x³ + ax` is exactly `p` — the trace vanishes, for the whole
twist family at once.  The proof is the reflection: the fiber count is `1 + χ(x³ + ax)`, the
cubic is odd, the quarter-turn is invisible (`χ(−1) = −1`), and the odd summand integrates
to zero over the closed frame. -/
theorem theReflectionIntegratesTheCensus (hp : p % 4 = 3) (a : ZMod p) :
    ∑ x : ZMod p, ((univ.filter fun y : ZMod p => y ^ 2 = x ^ 3 + a * x).card : ℤ) = p := by
  have hstep : ∀ x : ZMod p,
      ((univ.filter fun y : ZMod p => y ^ 2 = x ^ 3 + a * x).card : ℤ)
        = quadraticChar (ZMod p) (x ^ 3 + a * x) + 1 :=
    fun x => fiber_count p hp _
  simp_rw [hstep]
  rw [Finset.sum_add_distrib]
  have hodd : ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 + a * x) = 0 := by
    apply sum_odd_vanishes
    intro x
    have hfx : (-x) ^ 3 + a * -x = -1 * (x ^ 3 + a * x) := by ring
    rw [hfx, map_mul, chi_neg_one p hp, neg_one_mul]
  rw [hodd, zero_add, Finset.sum_const, card_univ, ZMod.card]
  simp

/-- **The two chosen curves inherit the vanishing**: at every half-turn prime, the frames of
`y² = x³ − x` and `y² = x³ − 25x` both count exactly `p` affine points. -/
theorem theBlindFrameIsBalancedOnBothCurves (hp : p % 4 = 3) :
    (∑ x : ZMod p, ((univ.filter fun y : ZMod p => y ^ 2 = x ^ 3 - x).card : ℤ)) = p ∧
    (∑ x : ZMod p, ((univ.filter fun y : ZMod p => y ^ 2 = x ^ 3 - 25 * x).card : ℤ)) = p := by
  constructor
  · have h := theReflectionIntegratesTheCensus p hp (-1)
    simpa [sub_eq_add_neg, neg_mul, mul_comm] using h
  · have h := theReflectionIntegratesTheCensus p hp (-25)
    have heq : ∀ x : ZMod p, x ^ 3 + (-25) * x = x ^ 3 - 25 * x := fun x => by ring
    simp_rw [heq] at h
    exact h

/-! ## The controls: the theorem against brute kernel enumeration -/

/-- **The blind-frame controls**: the frames at 7, 11, 19 recount their primes by brute
enumeration — the general theorem's instances, recomputed. -/
theorem theBlindFrameControls :
    (∑ x : ZMod 7, (univ.filter fun y : ZMod 7 => y ^ 2 = x ^ 3 - x).card) = 7 ∧
    (∑ x : ZMod 11, (univ.filter fun y : ZMod 11 => y ^ 2 = x ^ 3 - x).card) = 11 ∧
    (∑ x : ZMod 19, (univ.filter fun y : ZMod 19 => y ^ 2 = x ^ 3 - 25 * x).card) = 19 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-! ## The sighted frames: the Gaussian winding readout -/

/-- **A sighted prime splits in the Gaussian lattice**: `p ≡ 1 mod 4` is a sum of two
squares. -/
theorem theSightedPrimeSplitsInTheGaussianLattice {q : ℕ} [Fact q.Prime] (hq : q % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = q :=
  Nat.Prime.sq_add_sq (by omega)

/-- **The sighted frames read the winding**: exact censuses at 13, 17, 29 for
`y² = x³ − x`, by kernel enumeration. -/
theorem theSightedFrameReadsTheWinding :
    (∑ x : ZMod 13, (univ.filter fun y : ZMod 13 => y ^ 2 = x ^ 3 - x).card) = 7 ∧
    (∑ x : ZMod 17, (univ.filter fun y : ZMod 17 => y ^ 2 = x ^ 3 - x).card) = 15 ∧
    (∑ x : ZMod 29, (univ.filter fun y : ZMod 29 => y ^ 2 = x ^ 3 - x).card) = 39 := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

/-- **The winding agreement**: at each sighted control the trace squares to four times the
odd square of the Gaussian split — `a_p² = 4a²` with `p = a² + b²`, `a` odd. -/
theorem theWindingAgreesAtTheControls :
    ((13 : ℤ) - 7) ^ 2 = 4 * 3 ^ 2 ∧ (3 : ℤ) ^ 2 + 2 ^ 2 = 13 ∧
    ((17 : ℤ) - 15) ^ 2 = 4 * 1 ^ 2 ∧ (1 : ℤ) ^ 2 + 4 ^ 2 = 17 ∧
    ((29 : ℤ) - 39) ^ 2 = 4 * 5 ^ 2 ∧ (5 : ℤ) ^ 2 + 2 ^ 2 = 29 := by
  norm_num

/-- **The twist flips the sign where five is a non-residue**: at 13 the twisted curve
`y² = x³ − 25x` counts 19 affine points against the untwisted 7 — traces `−6` against `+6`,
five being a non-square mod 13 (also verified by enumeration). -/
theorem theTwistFlipsTheSign :
    (∑ x : ZMod 13, (univ.filter fun y : ZMod 13 => y ^ 2 = x ^ 3 - 25 * x).card) = 19 ∧
    ¬ IsSquare (5 : ZMod 13) := by
  refine ⟨?_, ?_⟩ <;> decide

end Soma.Holonics.Millennium.ReflectionCensus
