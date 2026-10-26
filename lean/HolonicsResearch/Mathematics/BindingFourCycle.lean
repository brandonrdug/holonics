import Holonics.Holon.Restriction
import Mathlib.Tactic

/-!
# A face needs a pair contact exactly where its four-cycle does not vanish

The record `research/records/2026-10-23_A_NEAR_MISS_IS_A_DRAW_FROM_THE_FACES_IT_KEPT_AND_THE_BASES_CHEAP_RINGS_CLOSE_THE_REST.md`
(§7; atlas `arith.binding-four-cycle`, `tower.square-defect-composition`) reads the binding of a
two-operand face `G(a, b)` as its four-cycle `□G = G(i, j) − G(i, l) − G(k, j) + G(k, l)`, and the
carry of a passage as the composition of the scale square's defect. #410 owes these; this file
proves them.

[proved-derived; formal-checked] What is proved.

1. **The binding** (`fourCycle`, `fourCycle_eq_zero_iff`): `□G` vanishes on every rectangle
   exactly when `G(a, b) = f(a) + g(b)`. Then each operand's own face composes the result by one
   crossing and no pair contact is needed; a nonzero four-cycle is what neither operand shows alone.
2. **Unit squares decide** (`fourCycle_glue_rows`, `fourCycle_glue_cols`, `unit_squares_decide`):
   rectangles glue along a shared side, so on `ℕ × ℕ` a face whose unit squares all vanish has every
   rectangle vanish.
3. **A sum binds nowhere, a product's ring face everywhere by one constant, and the index chart
   unbinds it** (`fourCycle_add`, `fourCycle_mul`, `fourCycle_mul_div`, `unit_square_mul_div`,
   `fourCycle_of_hom`): `□(a + b) = 0`; `□(ab) = (i − k)(j − l)`, so `□(ab/q) = (i − k)(j − l)/q`
   and every unit square reads `1/q`, the ring's pairing; a face read through a chart that turns
   the product into a sum (`ind(ab) = ind a + ind b`, the index of a primitive root on the units)
   has zero four-cycle.
4. **The carry composes along a passage** (`squareDefect_comp`, `squareDefect_comp_eq_zero`):
   `squareDefect π (B_f A_f) (B_c A_c) =
   squareDefect π B_f B_c · A_f + B_c · squareDefect π A_f A_c`
   (`Holon/Restriction.squareDefect`): the outer defect read at the inner's output plus the inner
   defect carried by the outer coarse map. Its additive instance is
   `Geometry/PhaseCarry.carry_cocycle`.

The computational object is the helical pair interaction: a pair contact carries exactly the
four-cycle that neither operand's face carries. Of the winding guide's six general objects this
touches the pair (the binding) and the tower thread (the scale square's defect); the helix, faces
and placement, the cell holonomy and the tube stay attached.

Consumers: the atlas rows `arith.binding-four-cycle` and `tower.square-defect-composition`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.BindingFourCycle

section FourCycle

variable {α β A : Type*} [AddCommGroup A]

/-- [definition] The four-cycle of a two-operand face on the rectangle `{i, k} × {j, l}`. -/
def fourCycle (G : α → β → A) (i k : α) (j l : β) : A := G i j - G i l - G k j + G k l

/-- [proved-standard; formal-checked] **The binding:** the four-cycle vanishes on every rectangle
exactly when the face is a sum of the operands' own faces. -/
theorem fourCycle_eq_zero_iff (G : α → β → A) :
    (∀ i k j l, fourCycle G i k j l = 0) ↔
      ∃ (f : α → A) (g : β → A), ∀ a b, G a b = f a + g b := by
  constructor
  · intro h
    rcases isEmpty_or_nonempty α with hα | ⟨⟨a₀⟩⟩
    · exact ⟨0, 0, fun a _ => hα.elim a⟩
    rcases isEmpty_or_nonempty β with hβ | ⟨⟨b₀⟩⟩
    · exact ⟨0, 0, fun _ b => hβ.elim b⟩
    refine ⟨fun a => G a b₀, fun b => G a₀ b - G a₀ b₀, fun a b => ?_⟩
    have h' : G a b - G a b₀ - G a₀ b + G a₀ b₀ = 0 := h a a₀ b b₀
    have e : G a b = (G a b - G a b₀ - G a₀ b + G a₀ b₀) + (G a b₀ + (G a₀ b - G a₀ b₀)) := by
      abel
    rw [e, h', zero_add]
  · rintro ⟨f, g, hfg⟩ i k j l
    simp only [fourCycle, hfg]
    abel

/-- [proved-standard; formal-checked] Rectangles glue along a shared row side. -/
theorem fourCycle_glue_rows (G : α → β → A) (i k k' : α) (j l : β) :
    fourCycle G i k j l + fourCycle G k k' j l = fourCycle G i k' j l := by
  simp only [fourCycle]
  abel

/-- [proved-standard; formal-checked] Rectangles glue along a shared column side. -/
theorem fourCycle_glue_cols (G : α → β → A) (i k : α) (j l l' : β) :
    fourCycle G i k j l + fourCycle G i k l l' = fourCycle G i k j l' := by
  simp only [fourCycle]
  abel

/-- [proved-standard; formal-checked] **Unit squares decide:** on `ℕ × ℕ`, if every unit square
has zero four-cycle then every rectangle does. -/
theorem unit_squares_decide (G : ℕ → ℕ → A) (h : ∀ i j, fourCycle G i (i + 1) j (j + 1) = 0)
    (i m j n : ℕ) : fourCycle G i (i + m) j (j + n) = 0 := by
  have hcol : ∀ i j n, fourCycle G i (i + 1) j (j + n) = 0 := by
    intro i j n
    induction n with
    | zero =>
      simp only [fourCycle, add_zero]
      abel
    | succ n ih =>
      rw [← fourCycle_glue_cols G i (i + 1) j (j + n) (j + (n + 1)), ih, zero_add]
      exact h i (j + n)
  induction m with
  | zero =>
    simp only [fourCycle, add_zero]
    abel
  | succ m ih =>
    rw [← fourCycle_glue_rows G i (i + m) (i + (m + 1)) j (j + n), ih, zero_add]
    exact hcol (i + m) j n

/-- [proved-standard; formal-checked] **A face composed by one crossing has zero four-cycle**
through any chart `ind` that turns the operation into a sum, `ind(a b) = ind a + ind b`: the index
of a primitive root on the units of `ℤ/q`. -/
theorem fourCycle_of_hom {M : Type*} [Mul M] (ind : M → A)
    (hind : ∀ a b, ind (a * b) = ind a + ind b) (i k j l : M) :
    fourCycle (fun a b => ind (a * b)) i k j l = 0 :=
  (fourCycle_eq_zero_iff _).2 ⟨ind, ind, hind⟩ i k j l

end FourCycle

/-- [proved-standard; formal-checked] **A sum binds nowhere.** -/
theorem fourCycle_add {K : Type*} [AddCommGroup K] (i k j l : K) :
    fourCycle (fun a b : K => a + b) i k j l = 0 :=
  (fourCycle_eq_zero_iff _).2 ⟨id, id, fun _ _ => rfl⟩ i k j l

/-- [proved-standard; formal-checked] **A product's four-cycle is `(i − k)(j − l)`.** -/
theorem fourCycle_mul {K : Type*} [CommRing K] (i k j l : K) :
    fourCycle (fun a b : K => a * b) i k j l = (i - k) * (j - l) := by
  simp only [fourCycle]
  ring

/-- [proved-standard; formal-checked] **A product's ring face binds by one constant:**
`□(ab/q) = (i − k)(j − l)/q`. -/
theorem fourCycle_mul_div {K : Type*} [Field K] (q i k j l : K) :
    fourCycle (fun a b : K => a * b / q) i k j l = (i - k) * (j - l) / q := by
  simp only [fourCycle]
  ring

/-- [proved-standard; formal-checked] **Every unit square of the product's ring face reads
`1/q`**, the ring's pairing. -/
theorem unit_square_mul_div {K : Type*} [Field K] (q i j : K) :
    fourCycle (fun a b : K => a * b / q) i (i + 1) j (j + 1) = 1 / q := by
  rw [fourCycle_mul_div]
  ring

section Defect

open Holonics.HolonCore

variable {𝕜 : Type*} [Field 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
/-- [proved-derived; formal-checked] **The carry composes along a passage:** the defect of a
composite coarse reading is the outer defect read at the inner's output plus the inner defect
carried by the outer coarse map. -/
theorem squareDefect_comp (π : Matrix κ ι 𝕜) (Af Bf : Matrix ι ι 𝕜) (Ac Bc : Matrix κ κ 𝕜) :
    squareDefect π (Bf * Af) (Bc * Ac) =
      squareDefect π Bf Bc * Af + Bc * squareDefect π Af Ac := by
  simp only [squareDefect, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
  abel

omit [DecidableEq ι] [DecidableEq κ] in
/-- [proved-derived; formal-checked] Two steps that each close their scale square compose into one
that closes it. -/
theorem squareDefect_comp_eq_zero (π : Matrix κ ι 𝕜) (Af Bf : Matrix ι ι 𝕜)
    (Ac Bc : Matrix κ κ 𝕜) (hA : squareDefect π Af Ac = 0) (hB : squareDefect π Bf Bc = 0) :
    squareDefect π (Bf * Af) (Bc * Ac) = 0 := by
  rw [squareDefect_comp, hA, hB, Matrix.zero_mul, Matrix.mul_zero, add_zero]

end Defect

end Holonics.Mathematics.BindingFourCycle
