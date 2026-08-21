import ElementaryHolonics.Millennium.TraceSequence
import ElementaryHolonics.Millennium.PartitionFunction

/-!
# LocalFactor: the Euler factor is a transfer determinant, and its trace is the sequence

The first deed of the BSD route chart (D1).  An elliptic curve's local `L`-factor at a good place
is `1 − a_p T + p T²`.  This file proves, exactly and with nothing imported beyond what the
development already carries, that this factor **is** the determinant face of a two-by-two
transfer matrix whose trace face **is** the trace sequence — so the arithmetic local factor and
the statistical-mechanical partition function are one object read through two receivers of one
matrix:

* the **companion matrix** `!![a, −q; 1, 0]` has trace `a` and determinant `q`;
* `det(1 − T·M) = 1 − aT + qT²` — **the local factor is the transfer determinant**, over any
  commutative ring;
* `trace(Mⁿ) = t_n` — **the powers' traces are exactly the trace sequence** of
  `TraceSequence.lean`, by the two-step induction whose step is
  `PartitionFunction.theFiniteTransferTraceObeysItsRecurrence` — Cayley–Hamilton doing the work;
* over `ℂ`, under the level-one bound `a² ≤ 4q`, **the factor splits through the Weil root**:
  `1 − aT + qT² = (1 − αT)(1 − ᾱT)` with `|α|² = q` — the placement statement of the factor,
  riding on `theRootHasSquaredModulusQ`.

So `L(E, s)` — the product of these factors over the places — is a product of transfer
determinants: **an arithmetic partition function**, which is the BSD route's spine sentence made
kernel-checked at the local level.  The global product, its analytic continuation, and everything
at bad places are not touched here.

Every `theorem` is discharged and none depends on `sorryAx`.  Nothing here claims movement on
the Birch–Swinnerton-Dyer conjecture.
-/

namespace Soma.Holonics.Millennium.LocalFactor

open Soma.Holonics.Millennium

/-- The Frobenius companion over a commutative ring: trace `a`, determinant `q`. -/
def companion {R : Type*} [CommRing R] (a q : R) : Matrix (Fin 2) (Fin 2) R :=
  !![a, -q; 1, 0]

/-- The companion's two faces: trace `a` and determinant `q`. -/
theorem theCompanionHasTraceAndDeterminant {R : Type*} [CommRing R] (a q : R) :
    (companion a q).trace = a ∧ (companion a q).det = q := by
  constructor
  · simp [companion, Matrix.trace_fin_two_of]
  · simp [companion, Matrix.det_fin_two_of]

/-- The shifted companion `1 − T·M`, written out. -/
theorem theShiftedCompanionIsTheFactorMatrix {R : Type*} [CommRing R] (a q T : R) :
    (1 : Matrix (Fin 2) (Fin 2) R) - T • companion a q = !![1 - T*a, T*q; -T, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [companion]

/-- **The local factor is the transfer determinant**: `det(1 − T·M) = 1 − aT + qT²`, over any
commutative ring.  The Euler factor of an elliptic curve at a good place is this determinant at
`a = a_p`, `q = p`. -/
theorem theLocalFactorIsTheTransferDeterminant {R : Type*} [CommRing R] (a q T : R) :
    ((1 : Matrix (Fin 2) (Fin 2) R) - T • companion a q).det = 1 - a*T + q*T^2 := by
  rw [theShiftedCompanionIsTheFactorMatrix, Matrix.det_fin_two_of]
  ring

/-- **The companion's power traces are the trace sequence.**  The step is the transfer-trace
recurrence (Cayley–Hamilton, already proved in `PartitionFunction`); the bases are `trace 1 = 2`
and `trace M = a`.  So the sequence `TraceSequence.trace` — whose level-one bound gives every
level — is the trace face of the same matrix whose determinant face is the local factor. -/
theorem theCompanionPowersCarryTheSequence (a q : ℤ) (n : ℕ) :
    (companion a q ^ n).trace = TraceSequence.trace a q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pow_zero, Matrix.trace_one]
  | one => simp [pow_one, companion, Matrix.trace_fin_two_of]
  | more n ih1 ih2 =>
      have h := PartitionFunction.theFiniteTransferTraceObeysItsRecurrence (companion a q) n
      obtain ⟨htr, hdet⟩ := theCompanionHasTraceAndDeterminant (a : ℤ) q
      rw [h, htr, hdet, ih1, ih2, TraceSequence.trace_succ_succ]

/-- **The factor splits through the Weil root.**  Under the level-one bound the local factor
factors as `(1 − αT)(1 − ᾱT)` with `α` the characteristic root of squared modulus `q` — the
placement face of the determinant, riding on the realizer the recurrence already carries. -/
theorem theFactorSplitsThroughTheWeilRoot (a q : ℤ) (h : (a : ℝ) ^ 2 ≤ 4 * (q : ℝ)) (T : ℂ) :
    1 - (a : ℂ) * T + (q : ℂ) * T ^ 2
      = (1 - TraceSequence.alpha a q * T) * (1 - (starRingEnd ℂ) (TraceSequence.alpha a q) * T) := by
  set α := TraceSequence.alpha a q with hα
  have hre : α.re = (a : ℝ) / 2 := rfl
  have hsum : α + (starRingEnd ℂ) α = (a : ℂ) := by
    rw [Complex.add_conj, hre]
    push_cast
    ring
  have hprod : α * (starRingEnd ℂ) α = (q : ℂ) := by
    rw [Complex.mul_conj, hα, TraceSequence.theRootHasSquaredModulusQ a q h]
    push_cast
    ring
  have expand : (1 - α * T) * (1 - (starRingEnd ℂ) α * T)
      = 1 - (α + (starRingEnd ℂ) α) * T + (α * (starRingEnd ℂ) α) * T ^ 2 := by ring
  rw [expand, hsum, hprod]

end Soma.Holonics.Millennium.LocalFactor
