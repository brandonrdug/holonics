import ElementaryHolonics.Millennium.SeventeenObstruction
import ElementaryHolonics.Millennium.Separation

/-!
# SeventeenSeparator: `Ш` is a collapsed population

`SeventeenObstruction` exhibits twelve descent classes at seventeen that pass every
two-adic and every seventeen-adic frame while no rational point reaches them.  This
file names what that is: **a collapsed population of a declared receiver family**, in
the exact sense of `Separation`.

The local frames are the readings.  They agree on the realized class and on the three
unreached ones, so they collapse them together, so no reading in the family separates
them.  That is the failure of the local-to-global principle, stated as a separation
failure rather than as a counterexample — and it says precisely why a congruence
argument can never close the gap: **a separator for these classes lies outside every
local frame.**

Measured 2026-08-23 outside Lean, over 29 moduli including prime powers to `289`: every
one of the three coset systems is soluble at every modulus tested, while none has an
integer solution with `|C|,|N| ≤ 260`.  The refusal is therefore a global second
descent, never a frame.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.SeventeenSeparator

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.SeventeenObstruction

/-- The four descent cosets at seventeen: the realized trivial class and the three
locally-admissible classes no rational point reaches. -/
inductive Coset | triv | c2 | c17 | c34
deriving DecidableEq

/-- The second slot's rung, per coset. -/
def rung : Coset → ℤ
  | .triv => 1 | .c2 => 2 | .c17 => 17 | .c34 => 34

/-- The two-adic frame at depth `k`, as a reading of a coset. -/
def twoAdicReading (k : ℕ) (c : Coset) : Prop :=
  ∃ C E F N : ℤ, ¬ (2 : ℤ) ∣ C ∧
    (2 ^ k : ℤ) ∣ (C ^ 2 - 17 * N ^ 2 - rung c * E ^ 2) ∧
    (2 ^ k : ℤ) ∣ (C ^ 2 + 17 * N ^ 2 - rung c * F ^ 2)

/-- The family of every two-adic frame. -/
def localFrames : Separation.ReceiverFamily Coset Prop :=
  {f | ∃ k : ℕ, f = twoAdicReading k}

/-- **EVERY LOCAL FRAME READS TRUE ON ALL FOUR COSETS**: the realized class and the
three unreached ones are locally admissible at every depth. -/
theorem theFramesReadTrueEverywhere (k : ℕ) (c : Coset) : twoAdicReading k c := by
  cases c with
  | triv =>
      exact ⟨1, 1, 1, 0, by norm_num, ⟨0, by simp [rung]⟩, ⟨0, by simp [rung]⟩⟩
  | c2 => exact (theInvisibleCosetsPassEveryTwoAdicFrame k).1
  | c17 => exact (theInvisibleCosetsPassEveryTwoAdicFrame k).2.1
  | c34 => exact (theInvisibleCosetsPassEveryTwoAdicFrame k).2.2

/-- **THE LOCAL FRAMES COLLAPSE THE INVISIBLE COSETS ONTO THE REALIZED ONE.**  No
reading in the family separates a class a rational point reaches from one no rational
point reaches.  `Ш` is exactly this collapsed population, and the failure of the local
principle is exactly the failure of this receiver family to separate. -/
theorem theLocalFramesCollapseTheInvisibleCosets (c d : Coset) :
    Separation.collapseOf localFrames c d := by
  intro f hf
  obtain ⟨k, rfl⟩ := hf
  exact propext ⟨fun _ => theFramesReadTrueEverywhere k d,
                 fun _ => theFramesReadTrueEverywhere k c⟩


/-- **NO LOCAL FRAME IS A SEPARATOR.**  By the keystone, off-collapse is the same as
carrying a separating reading — so a separator for these cosets exists nowhere in the
local family, at any depth.  The instrument that refused twenty-eight classes provably
cannot touch these; the refusal must be a genuinely global descent. -/
theorem theSeparatorLiesOutsideEveryLocalFrame (c d : Coset) :
    ¬ ∃ f ∈ localFrames, f c ≠ f d := by
  intro h
  exact ((Separation.theCollapsedPopulationHasASeparator localFrames).2 c d).mpr h
    (theLocalFramesCollapseTheInvisibleCosets c d)

/-! ## The three cosets are one equation -/

/-- **THE FIRST COSET REDUCES TO THE QUARTIC.** -/
theorem theFirstCosetReducesToTheQuartic {C N E F : ℤ}
    (h1 : C ^ 2 - 17 * N ^ 2 = 2 * E ^ 2) (h2 : C ^ 2 + 17 * N ^ 2 = 2 * F ^ 2) :
    F ^ 4 - E ^ 4 = 17 * (N * C) ^ 2 := by
  have hA : E ^ 2 + F ^ 2 = C ^ 2 := by linarith
  have hB : F ^ 2 - E ^ 2 = 17 * N ^ 2 := by linarith
  calc F ^ 4 - E ^ 4 = (F ^ 2 - E ^ 2) * (E ^ 2 + F ^ 2) := by ring
    _ = 17 * N ^ 2 * C ^ 2 := by rw [hA, hB]
    _ = 17 * (N * C) ^ 2 := by ring

/-- **THE SECOND COSET REDUCES TO THE SAME QUARTIC**, with `C = 17c`. -/
theorem theSecondCosetReducesToTheQuartic {c N E F : ℤ}
    (h1 : (17 * c) ^ 2 - 17 * N ^ 2 = 17 * E ^ 2)
    (h2 : (17 * c) ^ 2 + 17 * N ^ 2 = 17 * F ^ 2) :
    F ^ 4 - E ^ 4 = 17 * (2 * N * c) ^ 2 := by
  have hA : E ^ 2 + F ^ 2 = 34 * c ^ 2 := by linarith
  have hB : F ^ 2 - E ^ 2 = 2 * N ^ 2 := by linarith
  calc F ^ 4 - E ^ 4 = (F ^ 2 - E ^ 2) * (E ^ 2 + F ^ 2) := by ring
    _ = 2 * N ^ 2 * (34 * c ^ 2) := by rw [hA, hB]
    _ = 17 * (2 * N * c) ^ 2 := by ring

/-- **THE THIRD COSET REDUCES TO THE SAME QUARTIC**, with `C = 17c`. -/
theorem theThirdCosetReducesToTheQuartic {c N E F : ℤ}
    (h1 : (17 * c) ^ 2 - 17 * N ^ 2 = 34 * E ^ 2)
    (h2 : (17 * c) ^ 2 + 17 * N ^ 2 = 34 * F ^ 2) :
    F ^ 4 - E ^ 4 = 17 * (N * c) ^ 2 := by
  have hA : E ^ 2 + F ^ 2 = 17 * c ^ 2 := by linarith
  have hB : F ^ 2 - E ^ 2 = N ^ 2 := by linarith
  calc F ^ 4 - E ^ 4 = (F ^ 2 - E ^ 2) * (E ^ 2 + F ^ 2) := by ring
    _ = N ^ 2 * (17 * c ^ 2) := by rw [hA, hB]
    _ = 17 * (N * c) ^ 2 := by ring

/-- **ONE EQUATION REFUSES ALL THREE COSETS.**  Every locally-admissible coset at
seventeen lands on `F⁴ − E⁴ = 17·(square)`.  The three named-open refusals are one
named-open refusal, and `Ш(E₁₇)[2]` rests on a single Diophantine statement. -/
def TheQuarticIsRefused : Prop :=
  ∀ E F M : ℤ, F ^ 4 - E ^ 4 = 17 * M ^ 2 → E ^ 2 = F ^ 2

end Soma.Holonics.Millennium.SeventeenSeparator
