import ElementaryHolonics.Millennium.GeneralTwoAdic

/-!
# GeneralOddPlace: the receivers at the odd bad primes

The last places of the family, and they are elementary too — the condition is a
**valuation parity**, not a `ℚ_p`-point computation.

At an odd prime dividing one root and missing the other, the two slot valuations move
together:

* **`theOddBadPlaceCouplesTheSlotParities`** — for `p` with `p ∣ a` and `p ∤ b`,
  every affine point off the two-torsion has `v_p(x) + v_p(x − a)` **even**.

The three cases are exhaustive and each is forced: below zero all three slot
valuations agree, so the sum of the first two is twice one of them; at zero the second
slot is a unit because `p` divides `a`; above zero the third slot is a unit because
`p` misses `b`, so the first two absorb the whole even total.

The consequence on classes is that `p ∣ d₁ ⟺ p ∣ d₂` — the receiver at `p` couples
the two components of the class pair, which is exactly the kind of cut that shrinks a
Selmer group.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralOddPlace

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralFace

/-- **THE ODD BAD PLACE COUPLES THE SLOT PARITIES**: at a prime dividing `a` and
missing `b`, the two slot valuations have even sum. -/
theorem theOddBadPlaceCouplesTheSlotParities {a b : ℤ} {p : ℕ} [Fact p.Prime]
    (ha0 : a ≠ 0) (hpa : (p : ℤ) ∣ a) (hpb : ¬ (p : ℤ) ∣ b) {x y : ℚ}
    (hcurve : y ^ 2 = x * (x - (a : ℚ)) * (x - (b : ℚ))) (hy : y ≠ 0)
    (hx0 : x ≠ 0) (hxa : x - (a : ℚ) ≠ 0) (hxb : x - (b : ℚ) ≠ 0) :
    Even (padicValRat p x + padicValRat p (x - (a : ℚ))) := by
  have hp : p.Prime := Fact.out
  have hvb : padicValRat p ((b : ℚ)) = 0 := by
    have := FamilyGenocchi.int_val_zero (p := p) hpb
    push_cast at this ⊢
    exact this
  have hbq : ((b : ℚ)) ≠ 0 := by
    intro hc
    refine hpb ?_
    have hz : (b : ℤ) = 0 := by exact_mod_cast hc
    rw [hz]
    exact dvd_zero _
  have haq : ((a : ℚ)) ≠ 0 := by exact_mod_cast ha0
  have hva : 0 < padicValRat p ((a : ℚ)) := by
    have hval : padicValRat p ((a : ℚ)) = (padicValInt p a : ℤ) := by
      simpa using (padicValRat.of_int (p := p) (z := a))
    rw [hval]
    have hpos : 1 ≤ padicValInt p a := by
      rcases (padicValInt_dvd_iff (p := p) 1 a).mp (by simpa using hpa) with hz | hle
      · exact absurd hz ha0
      · exact hle
    exact_mod_cast hpos
  have hsum : padicValRat p x + padicValRat p (x - (a : ℚ))
      + padicValRat p (x - (b : ℚ)) = 2 * padicValRat p y := by
    have h1 : padicValRat p (y ^ 2) = 2 * padicValRat p y := by
      rw [pow_two, padicValRat.mul hy hy]
      ring
    rw [← h1, hcurve, padicValRat.mul (mul_ne_zero hx0 hxa) hxb,
      padicValRat.mul hx0 hxa]
  rcases lt_trichotomy (padicValRat p x) 0 with hneg | hzero | hpos
  · have h1 : padicValRat p (x - (a : ℚ)) = padicValRat p x := by
      have he : x - (a : ℚ) = x + (-(a : ℚ)) := by ring
      rw [he]
      refine FamilySupport.val_add_left hx0 (by rw [← he]; exact hxa) ?_
      rw [padicValRat.neg]
      omega
    have h2' : padicValRat p (x - (b : ℚ)) = padicValRat p x := by
      have he : x - (b : ℚ) = x + (-(b : ℚ)) := by ring
      rw [he]
      refine FamilySupport.val_add_left hx0 (by rw [← he]; exact hxb) ?_
      rw [padicValRat.neg, hvb]
      omega
    rw [h1]
    exact ⟨padicValRat p x, by ring⟩
  · have h1 : padicValRat p (x - (a : ℚ)) = 0 := by
      have he : x - (a : ℚ) = x + (-(a : ℚ)) := by ring
      rw [he, FamilySupport.val_add_left hx0 (by rw [← he]; exact hxa)
        (by rw [padicValRat.neg]; omega)]
      exact hzero
    rw [h1, hzero]
    exact ⟨0, by ring⟩
  · have h2 : padicValRat p (x - (b : ℚ)) = 0 := by
      have he : x - (b : ℚ) = -(b : ℚ) + x := by ring
      rw [he, FamilySupport.val_add_left (neg_ne_zero.mpr hbq)
        (by rw [← he]; exact hxb) (by rw [padicValRat.neg, hvb]; omega),
        padicValRat.neg, hvb]
    rw [h2] at hsum
    exact ⟨padicValRat p y, by omega⟩

end Soma.Holonics.Millennium.GeneralOddPlace
