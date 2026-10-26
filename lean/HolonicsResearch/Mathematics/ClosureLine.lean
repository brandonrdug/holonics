import Mathlib.Tactic

/-!
# The closure line: an operation is a line in the homogeneous lift of three faces

The record `research/records/2026-10-26_THE_OPERATION_IS_A_LINE_IN_THE_LIFT_AND_THE_RELEASE_READS_THE_RADIX_ITINERARY.md`
(§3) locates the transformation between three faces `a`, `b`, `c` without authoring it. Each
meeting of three faces is lifted to the row `(1, a) ⊗ (1, b) ⊗ (1, c)`, with coordinates
`[1, a, b, c, ab, ac, bc, abc]`. A coefficient vector `p` closes on a row when its pairing with the
row is zero, and the operation the rows carry is the line of vectors that close on all of them: a
kernel, located by which closures hold. This file proves what that line is and when it is one
line.

[proved-standard; formal-checked] What is proved.

1. **Closure is linear in the coefficients** (`pairing_add`, `pairing_smul`): the vectors closing
   on a family of rows form a submodule, the kernel of the rows.
2. **Every closure is a bi-Möbius relation** (`pairing_eq`): the pairing is `N(a, b) + D(a, b) c`,
   with `N` and `D` affine in each of `a` and `b`.
3. **A unit denominator gives one consequence** (`closes_unique_of_unit`): when `D(a, b)` is a
   unit, exactly one `c` closes, `c = −N/D`.
4. **A nonunit denominator is the fibre** (`closes_of_denom_zero`): when `D(a, b) = 0`, every `c`
   closes if `N(a, b) = 0` (a plural fibre) and none closes otherwise (a refusal).
5. **The four operations are four lines of one lift** (`sum_closes`, `difference_closes`,
   `product_closes`, `quotient_closes`): `(0,1,1,−1,0,0,0,0)` closes exactly on `c = a + b`,
   `(0,1,−1,−1,0,0,0,0)` on `c = a − b`, `(0,0,0,−1,1,0,0,0)` on `c = ab`, and
   `(0,1,0,0,0,0,−1,0)` on `a = bc`.
6. **Seven rows locate the sum, and seven the product** (`sum_line_located`,
   `product_line_located`): on any commutative ring in which `2` is a unit (every odd ring
   `ℤ/q`, every field not of characteristic two), a vector closing on the sum's rows at
   `a, b ∈ {0, 1, −1}` is a multiple of the sum's line, and one closing on the product's rows there
   is a multiple of the product's line.
7. **Ring two needs a deeper lift** (`ring_two_not_located`): over `ℤ/2`, where `a² = a`, the vector
   `(0,1,0,0,1,1,0,0)` closes on every row of the sum without being a multiple of the sum's line.

The computational object is the helical pair interaction: the row is the tensor of three ring
phases, and the closing vector is the pair contact's coefficient that cancels their slip. Of the
winding guide's six general objects this touches the pair (the bilinear block `W(x̄ ⊗ y)` read on
three faces) and faces and placement (the faces `a`, `b`, `c` as ring residues); the helix, the cell
holonomy, the tube and the tower thread stay attached.

Consumers: the atlas row `arith.closure-line` and the record's §3.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.ClosureLine

variable {R : Type*} [CommRing R]

/-- [definition] The homogeneous lift of three faces, `(1, a) ⊗ (1, b) ⊗ (1, c)`, in the
coordinates `[1, a, b, c, ab, ac, bc, abc]`. -/
def lift (a b c : R) : Fin 8 → R := ![1, a, b, c, a * b, a * c, b * c, a * b * c]

/-- [definition] The pairing of a coefficient vector with one lifted row; the vector closes on the
row when this is zero. -/
def pairing (p : Fin 8 → R) (a b c : R) : R :=
  p 0 + p 1 * a + p 2 * b + p 3 * c + p 4 * (a * b) + p 5 * (a * c) + p 6 * (b * c) +
    p 7 * (a * b * c)

/-- [proved-standard; formal-checked] The pairing is the dot product with the lift. -/
theorem pairing_eq_dot (p : Fin 8 → R) (a b c : R) :
    pairing p a b c = ∑ i, p i * lift a b c i := by
  simp [pairing, lift, Fin.sum_univ_eight] <;> ring

/-- [proved-standard; formal-checked] Closure is additive in the coefficients. -/
theorem pairing_add (p p' : Fin 8 → R) (a b c : R) :
    pairing (p + p') a b c = pairing p a b c + pairing p' a b c := by
  simp only [pairing, Pi.add_apply]
  ring

/-- [proved-standard; formal-checked] Closure is homogeneous in the coefficients. -/
theorem pairing_smul (s : R) (p : Fin 8 → R) (a b c : R) :
    pairing (s • p) a b c = s * pairing p a b c := by
  simp only [pairing, Pi.smul_apply, smul_eq_mul]
  ring

/-- [definition] The numerator of the closure, affine in each of `a` and `b`. -/
def numer (p : Fin 8 → R) (a b : R) : R := p 0 + p 1 * a + p 2 * b + p 4 * (a * b)

/-- [definition] The denominator of the closure, affine in each of `a` and `b`. -/
def denom (p : Fin 8 → R) (a b : R) : R := p 3 + p 5 * a + p 6 * b + p 7 * (a * b)

/-- [proved-standard; formal-checked] **Every closure is bi-Möbius:** the pairing is
`N(a, b) + D(a, b) c`. -/
theorem pairing_eq (p : Fin 8 → R) (a b c : R) :
    pairing p a b c = numer p a b + denom p a b * c := by
  simp only [pairing, numer, denom]
  ring

/-- [proved-standard; formal-checked] **A unit denominator gives one consequence:** exactly one `c`
closes, `c = −D⁻¹ N`. -/
theorem closes_unique_of_unit {p : Fin 8 → R} {a b : R} (hD : IsUnit (denom p a b)) :
    ∃! c, pairing p a b c = 0 := by
  obtain ⟨u, hu⟩ := hD
  refine ⟨-(↑u⁻¹ * numer p a b), ?_, ?_⟩
  · rw [pairing_eq, ← hu]
    have h := u.mul_inv
    linear_combination (-(numer p a b)) * h
  · intro c hc
    rw [pairing_eq, ← hu] at hc
    have h1 : (u : R) * (c + ↑u⁻¹ * numer p a b) = 0 := by
      have h := u.mul_inv
      linear_combination hc + numer p a b * h
    have h2 := (u.mul_right_eq_zero).mp h1
    linear_combination h2

/-- [proved-standard; formal-checked] **A vanishing denominator is the fibre:** every `c` closes when
the numerator vanishes, and none closes when it does not. -/
theorem closes_of_denom_zero {p : Fin 8 → R} {a b : R} (hD : denom p a b = 0) (c : R) :
    pairing p a b c = 0 ↔ numer p a b = 0 := by
  rw [pairing_eq, hD, zero_mul, add_zero]

/-- [definition] The sum's line, `c = a + b`. -/
def sumLine : Fin 8 → R := ![0, 1, 1, -1, 0, 0, 0, 0]

/-- [definition] The difference's line, `c = a − b`. -/
def differenceLine : Fin 8 → R := ![0, 1, -1, -1, 0, 0, 0, 0]

/-- [definition] The product's line, `c = ab`. -/
def productLine : Fin 8 → R := ![0, 0, 0, -1, 1, 0, 0, 0]

/-- [definition] The quotient's line, `a = bc`. -/
def quotientLine : Fin 8 → R := ![0, 1, 0, 0, 0, 0, -1, 0]

/-- [proved-standard; formal-checked] The sum's line closes exactly on `c = a + b`. -/
theorem sum_closes (a b c : R) : pairing sumLine a b c = 0 ↔ c = a + b := by
  have h : pairing sumLine a b c = a + b - c := by
    simp [pairing, sumLine] <;> ring
  rw [h, sub_eq_zero, eq_comm]

/-- [proved-standard; formal-checked] The difference's line closes exactly on `c = a − b`. -/
theorem difference_closes (a b c : R) : pairing differenceLine a b c = 0 ↔ c = a - b := by
  have h : pairing differenceLine a b c = a - b - c := by
    simp [pairing, differenceLine] <;> ring
  rw [h, sub_eq_zero, eq_comm]

/-- [proved-standard; formal-checked] The product's line closes exactly on `c = ab`. -/
theorem product_closes (a b c : R) : pairing productLine a b c = 0 ↔ c = a * b := by
  have h : pairing productLine a b c = a * b - c := by
    simp [pairing, productLine] <;> ring
  rw [h, sub_eq_zero, eq_comm]

/-- [proved-standard; formal-checked] The quotient's line closes exactly on `a = bc`; its
denominator is `−b`, so the consequence is unique where `b` is a unit and is the fibre of `b`
otherwise. -/
theorem quotient_closes (a b c : R) : pairing quotientLine a b c = 0 ↔ a = b * c := by
  have h : pairing quotientLine a b c = a - b * c := by
    simp [pairing, quotientLine] <;> ring
  rw [h, sub_eq_zero]

/-- [proved-standard; formal-checked] **Seven rows locate the sum.** If `2` is a unit and `p`
closes on the sum's rows at `a, b ∈ {0, 1, −1}`, then `p` is the sum's line scaled by `−p₃`:
`p₀ = p₄ = p₅ = p₆ = p₇ = 0` and `p₁ = p₂ = −p₃`. -/
theorem sum_line_located (h2 : IsUnit (2 : R)) (p : Fin 8 → R)
    (h : ∀ a b : R, (a = 0 ∨ a = 1 ∨ a = -1) → (b = 0 ∨ b = 1 ∨ b = -1) →
      pairing p a b (a + b) = 0) :
    p 0 = 0 ∧ p 1 = -p 3 ∧ p 2 = -p 3 ∧ p 4 = 0 ∧ p 5 = 0 ∧ p 6 = 0 ∧ p 7 = 0 := by
  have r00 := h 0 0 (Or.inl rfl) (Or.inl rfl)
  have r10 := h 1 0 (Or.inr (Or.inl rfl)) (Or.inl rfl)
  have rm0 := h (-1) 0 (Or.inr (Or.inr rfl)) (Or.inl rfl)
  have r01 := h 0 1 (Or.inl rfl) (Or.inr (Or.inl rfl))
  have r0m := h 0 (-1) (Or.inl rfl) (Or.inr (Or.inr rfl))
  have r11 := h 1 1 (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
  have r1m := h 1 (-1) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  simp only [pairing] at r00 r10 rm0 r01 r0m r11 r1m
  have cancel : ∀ x : R, 2 * x = 0 → x = 0 := fun x hx => (h2.mul_right_eq_zero).mp hx
  have hp0 : p 0 = 0 := by linear_combination r00
  have hp5 : p 5 = 0 := cancel _ (by linear_combination r10 + rm0 - 2 * r00)
  have hp6 : p 6 = 0 := cancel _ (by linear_combination r01 + r0m - 2 * r00)
  have hp13 : p 1 + p 3 = 0 := cancel _ (by linear_combination r10 - rm0)
  have hp23 : p 2 + p 3 = 0 := cancel _ (by linear_combination r01 - r0m)
  have hp1 : p 1 = -p 3 := by linear_combination hp13
  have hp2 : p 2 = -p 3 := by linear_combination hp23
  have hp4 : p 4 = 0 := by linear_combination -r1m + r00 + hp13 - hp23
  have hp7 : p 7 = 0 :=
    cancel _ (by linear_combination r11 - r00 - hp13 - hp23 - hp4 - 2 * hp5 - 2 * hp6)
  exact ⟨hp0, hp1, hp2, hp4, hp5, hp6, hp7⟩

/-- [proved-standard; formal-checked] **Seven rows locate the product.** If `2` is a unit and `p`
closes on the product's rows at `a, b ∈ {0, 1, −1}`, then `p` is the product's line scaled by
`−p₃`: `p₀ = p₁ = p₂ = p₅ = p₆ = p₇ = 0` and `p₄ = −p₃`. -/
theorem product_line_located (h2 : IsUnit (2 : R)) (p : Fin 8 → R)
    (h : ∀ a b : R, (a = 0 ∨ a = 1 ∨ a = -1) → (b = 0 ∨ b = 1 ∨ b = -1) →
      pairing p a b (a * b) = 0) :
    p 0 = 0 ∧ p 1 = 0 ∧ p 2 = 0 ∧ p 4 = -p 3 ∧ p 5 = 0 ∧ p 6 = 0 ∧ p 7 = 0 := by
  have r00 := h 0 0 (Or.inl rfl) (Or.inl rfl)
  have r10 := h 1 0 (Or.inr (Or.inl rfl)) (Or.inl rfl)
  have r01 := h 0 1 (Or.inl rfl) (Or.inr (Or.inl rfl))
  have r11 := h 1 1 (Or.inr (Or.inl rfl)) (Or.inr (Or.inl rfl))
  have r1m := h 1 (-1) (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
  have rm1 := h (-1) 1 (Or.inr (Or.inr rfl)) (Or.inr (Or.inl rfl))
  have rmm := h (-1) (-1) (Or.inr (Or.inr rfl)) (Or.inr (Or.inr rfl))
  simp only [pairing] at r00 r10 r01 r11 r1m rm1 rmm
  have cancel : ∀ x : R, 2 * x = 0 → x = 0 := fun x hx => (h2.mul_right_eq_zero).mp hx
  have hp0 : p 0 = 0 := by linear_combination r00
  have hp1 : p 1 = 0 := by linear_combination r10 - r00
  have hp2 : p 2 = 0 := by linear_combination r01 - r00
  have hp7 : p 7 = 0 :=
    cancel _ (cancel _ (by linear_combination r11 + r1m + rm1 + rmm - 4 * r00))
  have hp6 : p 6 = 0 := cancel _ (by linear_combination r11 + r1m - 2 * r10 - 2 * hp7)
  have hp5 : p 5 = 0 := cancel _ (by linear_combination r11 + rm1 - 2 * r01 - 2 * hp7)
  have hp34 : p 3 + p 4 = 0 := cancel _ (by linear_combination r11 + rmm - 2 * r00 - 2 * hp7)
  have hp4 : p 4 = -p 3 := by linear_combination hp34
  exact ⟨hp0, hp1, hp2, hp4, hp5, hp6, hp7⟩

/-- [proved-standard; formal-checked] **Ring two needs a deeper lift.** Over `ℤ/2`, where every
face is its own square, `(0,1,0,0,1,1,0,0)` closes on every row of the sum, yet it is not a
multiple of the sum's line (its `c` coordinate is `0` while its `a` coordinate is `1`). -/
theorem ring_two_not_located :
    (∀ a b : ZMod 2, pairing ![0, 1, 0, 0, 1, 1, 0, 0] a b (a + b) = 0) ∧
      (![0, 1, 0, 0, 1, 1, 0, 0] : Fin 8 → ZMod 2) 3 = 0 ∧
      (![0, 1, 0, 0, 1, 1, 0, 0] : Fin 8 → ZMod 2) 1 = 1 := by
  refine ⟨?_, rfl, rfl⟩
  decide

end Holonics.Mathematics.ClosureLine
