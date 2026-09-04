import ElementaryHolonics.Millennium.GeneralCollision

/-!
# GeneralQuotientCardinality: the explicit weak Mordell–Weil bound

`GeneralCollision` proves finiteness of `E(ℚ)/2E(ℚ)` and carries the exact
pigeonhole threshold.  This file returns that threshold as the cardinal inequality
its prose advertises, for the integral split model `y² = x(x-a)(x-b)`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralQuotientCardinality

open Soma.Holonics.Millennium.GeneralFace
open Soma.Holonics.Millennium.GeneralCollision

variable {a b : ℤ}

/-- **THE EXPLICIT WEAK MORDELL–WEIL BOUND**: the quotient by doubles has at most
`(2·τ(|ab(a-b)|))²` elements. -/
theorem theWeakMordellWeilCardBoundOnEveryIntegralSplitFullTwoTorsionCurve
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a - b ≠ 0) :
    Nat.card ((E ((a : ℚ)) ((b : ℚ))).Point ⧸ twoE ((a : ℚ)) ((b : ℚ)))
      ≤ 4 * (a * b * (a - b)).natAbs.divisors.card
        * (a * b * (a - b)).natAbs.divisors.card := by
  let G := (E ((a : ℚ)) ((b : ℚ))).Point
  let H : AddSubgroup G := twoE ((a : ℚ)) ((b : ℚ))
  let Q := G ⧸ H
  let N : ℕ := 4 * (a * b * (a - b)).natAbs.divisors.card
    * (a * b * (a - b)).natAbs.divisors.card
  letI : Finite Q :=
    theWeakMordellWeilTheoremOnEveryFullTwoTorsionCurve ha hb hab
  letI : Fintype Q := Fintype.ofFinite Q
  change Nat.card Q ≤ N
  by_contra hle
  have hcard : N < Fintype.card Q := by
    rw [← Nat.card_eq_fintype_card]
    omega
  obtain ⟨p, q, hpq, W, hW⟩ :=
    theClassesCollideOnEveryFullTwoTorsionCurve ha hb hab
      (hcard := by simpa [N, Q, G, H] using hcard)
      (fun c : Q => Quotient.out c)
  apply hpq
  have hmem : Quotient.out p - Quotient.out q ∈ H := by
    change ∃ W, W + W = Quotient.out p - Quotient.out q
    exact ⟨W, hW.symm⟩
  have heq : (Quotient.mk'' (Quotient.out p) : Q) = Quotient.mk'' (Quotient.out q) :=
    (QuotientAddGroup.eq).mpr (by
      rw [neg_add_eq_sub]
      have hneg : Quotient.out q - Quotient.out p = -(Quotient.out p - Quotient.out q) := by
        abel
      rw [hneg]
      exact H.neg_mem hmem)
  calc
    p = Quotient.mk'' (Quotient.out p) := (Quotient.out_eq' p).symm
    _ = Quotient.mk'' (Quotient.out q) := heq
    _ = q := Quotient.out_eq' q

end Soma.Holonics.Millennium.GeneralQuotientCardinality
