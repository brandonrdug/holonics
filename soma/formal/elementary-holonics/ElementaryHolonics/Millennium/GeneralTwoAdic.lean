import ElementaryHolonics.Millennium.GeneralRealPlace

/-!
# GeneralTwoAdic: the receiver at two

The first **bad** place, and the one that needs no `ℚ_2`: everything is a congruence
on rationals through the two-adic valuation.

The mechanism is that odd squares agree modulo eight, so the difference of two
two-adic-unit squares is divisible by eight.  Applied to the descent that says:

* **`theTwoAdicReceiverSeparatesEqualClasses`** — if the two slot values of a point
  carry the **same** class and both are two-adic units, then `8 ∣ a` two-adically.
* **`theTwoAdicReceiverRefusesTheDiagonal`** — contrapositive, and this is the
  receiver: when `v₂(a) < 3`, a point whose slots are both two-adic units has
  **distinct** slot classes.  The diagonal of the class square is cut.

That is a genuine local condition at two, and it is the two-parameter form of the
refusal the congruent-number engine uses to empty its coset.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.GeneralTwoAdic

open Soma.Holonics.Millennium
open Soma.Holonics.Millennium.GeneralFace

/-- **THE RECEIVER AT TWO SEPARATES EQUAL CLASSES**: if `x` and `x − a` carry the same
square class and both are two-adic units, then `a` is divisible by eight two-adically.

Writing `x = d·c²` and `x − a = d·c'²`, the ratio `t = c/c'` is a two-adic unit
because the two slots have equal valuation, and `a = d·c'²·(t² − 1)` with
`v₂(t² − 1) ≥ 3` since odd squares agree modulo eight. -/
theorem theTwoAdicReceiverSeparatesEqualClasses {a x d : ℚ}
    (hd0 : d ≠ 0) (ha0 : a ≠ 0)
    (h1 : Descent.SqCls x d) (h2 : Descent.SqCls (x - a) d)
    (hvx : padicValRat 2 x = 0) (hvxa : padicValRat 2 (x - a) = 0) :
    3 ≤ padicValRat 2 a := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c, hc, hxv⟩ := h1
  obtain ⟨c', hc', hxav⟩ := h2
  set t : ℚ := c / c' with ht
  have ht0 : t ≠ 0 := div_ne_zero hc hc'
  -- the two slots have equal valuation, so the ratio is a unit
  have hvc : padicValRat 2 c = padicValRat 2 c' := by
    have e1 : (0 : ℤ) = 2 * padicValRat 2 c + padicValRat 2 d := by
      rw [← hvx, hxv, padicValRat.mul (pow_ne_zero 2 hc) hd0, padicValRat.pow hc]
      ring
    have e2 : (0 : ℤ) = 2 * padicValRat 2 c' + padicValRat 2 d := by
      rw [← hvxa, hxav, padicValRat.mul (pow_ne_zero 2 hc') hd0, padicValRat.pow hc']
      ring
    omega
  have hvt : padicValRat 2 t = 0 := by
    rw [ht, padicValRat.div hc hc', hvc]
    ring
  -- the difference of the two slots is `a`
  have hdiff : d * c' ^ 2 * (t ^ 2 - 1) = a := by
    have hexp : d * c' ^ 2 * (t ^ 2 - 1) = c ^ 2 * d - c' ^ 2 * d := by
      rw [ht]
      field_simp
    rw [hexp, ← hxv, ← hxav]
    ring
  have hne : t ^ 2 - 1 ≠ 0 := by
    intro hcz
    refine ha0 ?_
    rw [← hdiff, hcz, mul_zero]
  -- odd squares agree modulo eight
  have hunit := FamilyGenocchi.unit_sq_diff_val ht0 one_ne_zero hvt
    (by simp [padicValRat.one]) (by simpa using hne)
  have hone : (1 : ℚ) ^ 2 = 1 := one_pow 2
  rw [hone] at hunit
  -- assemble the valuation of `a`
  have hva : padicValRat 2 a
      = padicValRat 2 (d * c' ^ 2) + padicValRat 2 (t ^ 2 - 1) := by
    rw [← hdiff, padicValRat.mul (mul_ne_zero hd0 (pow_ne_zero 2 hc')) hne]
  have hdc : padicValRat 2 (d * c' ^ 2) = 0 := by
    have he : d * c' ^ 2 = x - a := by rw [hxav]; ring
    rw [he]
    exact hvxa
  rw [hva, hdc, zero_add]
  exact hunit

/-- **THE RECEIVER AT TWO REFUSES THE DIAGONAL**: when `v₂(a) < 3`, no point with
both slots two-adic units carries equal slot classes.  The diagonal of the class
square is cut by the place at two alone. -/
theorem theTwoAdicReceiverRefusesTheDiagonal {a x d : ℚ}
    (hd0 : d ≠ 0) (ha0 : a ≠ 0) (hva : padicValRat 2 a < 3)
    (hvx : padicValRat 2 x = 0) (hvxa : padicValRat 2 (x - a) = 0)
    (h1 : Descent.SqCls x d) : ¬ Descent.SqCls (x - a) d := by
  intro h2
  have := theTwoAdicReceiverSeparatesEqualClasses hd0 ha0 h1 h2 hvx hvxa
  omega

end Soma.Holonics.Millennium.GeneralTwoAdic
