import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Holon.AffineContact: the unit-admittance contact is a lossless exchange

[definition] The resident constitutive relation returns an affine family `F = a + V` over a source
(a plural or unique fibre of the relation). An actual current `h` meets it through the declared
unit-admittance metric. With `P` the orthogonal projection onto the directions `V` (an idempotent
self-adjoint map), the contact returns

```text
h' = P h + (a − P a)     the successor (the realized reaction; never a point cast of F)
n_in = a − P a           the incoming normal (the family's normal face)
n_ret = h − P h          the returned normal (the normal face the current gives back)
```

Rust: `native_ecology::constitutive_fibre::ResidentContactReaction` (the one reaction section of
`ResidentConditionContact`, `ResidentAffineContact` and the wave source contact) and
`AffineContactReading::is_lossless_exchange`; the wave relation rest checks the same law on the
retained words.

[proved-derived; formal-checked]

1. `contact_difference`: `h' − h = n_in − n_ret`.
2. `contact_lossless`: `‖h‖² + ‖n_in‖² = ‖h'‖² + ‖n_ret‖²` — the exchange at the contact does no
   work; the normal part of the current is returned and replaced by the family's.
3. `contact_normal`: the successor's normal part is the family's, `h' − P h' = n_in`, so the
   successor lies in `F` (`contact_mem_family`); `contact_fixes_family`: a current already in `F`
   is unchanged, so a second contact with the same family returns zero difference
   (`contact_idempotent`).

Namespace `Soma.Holonics.HolonCore`. No axioms are added.
-/

namespace Soma.Holonics.HolonCore

section AffineContact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- [definition] An orthogonal projection, given as an idempotent self-adjoint linear map. -/
structure IsOrthoProjection (P : E →ₗ[ℝ] E) : Prop where
  idem : ∀ x, P (P x) = P x
  symm : ∀ x y, inner ℝ (P x) y = inner ℝ x (P y)

/-- [definition] The contact successor `P h + (a − P a)`. -/
def contactSuccessor (P : E →ₗ[ℝ] E) (h a : E) : E := P h + (a - P a)

/-- [definition] The incoming normal `a − P a`. -/
def incomingNormal (P : E →ₗ[ℝ] E) (a : E) : E := a - P a

/-- [definition] The returned normal `h − P h`. -/
def returnedNormal (P : E →ₗ[ℝ] E) (h : E) : E := h - P h

/-- [definition] Membership of the affine family `a + range P`, read by its normal part. -/
def InContactFamily (P : E →ₗ[ℝ] E) (a x : E) : Prop := x - P x = a - P a

/-- [proved-derived; formal-checked] **The difference.** `h' − h = n_in − n_ret`. -/
theorem contact_difference (P : E →ₗ[ℝ] E) (h a : E) :
    contactSuccessor P h a - h = incomingNormal P a - returnedNormal P h := by
  simp only [contactSuccessor, incomingNormal, returnedNormal]
  abel

/-- [proved-derived; formal-checked] A projected vector is orthogonal to every normal part. -/
theorem inner_proj_normal {P : E →ₗ[ℝ] E} (hP : IsOrthoProjection P) (x y : E) :
    inner ℝ (P x) (y - P y) = 0 := by
  rw [inner_sub_right, hP.symm x y, hP.symm x (P y), hP.idem y, sub_self]

/-- [proved-derived; formal-checked] **Pythagoras for the projection.**
`‖x‖² = ‖P x‖² + ‖x − P x‖²`. -/
theorem norm_sq_proj_add_normal {P : E →ₗ[ℝ] E} (hP : IsOrthoProjection P) (x : E) :
    ‖x‖ ^ 2 = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by
  have split : x = P x + (x - P x) := by abel
  calc ‖x‖ ^ 2 = ‖P x + (x - P x)‖ ^ 2 := by rw [← split]
    _ = ‖P x‖ ^ 2 + 2 * inner ℝ (P x) (x - P x) + ‖x - P x‖ ^ 2 := norm_add_sq_real _ _
    _ = ‖P x‖ ^ 2 + ‖x - P x‖ ^ 2 := by rw [inner_proj_normal hP]; ring

/-- [proved-derived; formal-checked] **The contact is lossless.**
`‖h‖² + ‖n_in‖² = ‖h'‖² + ‖n_ret‖²`. -/
theorem contact_lossless {P : E →ₗ[ℝ] E} (hP : IsOrthoProjection P) (h a : E) :
    ‖h‖ ^ 2 + ‖incomingNormal P a‖ ^ 2
      = ‖contactSuccessor P h a‖ ^ 2 + ‖returnedNormal P h‖ ^ 2 := by
  have successor :
      ‖contactSuccessor P h a‖ ^ 2 = ‖P h‖ ^ 2 + ‖a - P a‖ ^ 2 := by
    simp only [contactSuccessor]
    rw [norm_add_sq_real, inner_proj_normal hP]
    ring
  rw [successor, norm_sq_proj_add_normal hP h]
  simp only [incomingNormal, returnedNormal]
  ring

/-- [proved-derived; formal-checked] **The successor's normal part is the family's.** -/
theorem contact_normal {P : E →ₗ[ℝ] E} (hP : IsOrthoProjection P) (h a : E) :
    contactSuccessor P h a - P (contactSuccessor P h a) = incomingNormal P a := by
  simp only [contactSuccessor, incomingNormal, map_add, map_sub, hP.idem]
  abel

/-- [proved-derived; formal-checked] The successor lies in the family `a + range P`. -/
theorem contact_mem_family {P : E →ₗ[ℝ] E} (hP : IsOrthoProjection P) (h a : E) :
    InContactFamily P a (contactSuccessor P h a) :=
  contact_normal hP h a

/-- [proved-derived; formal-checked] **A current already in the family is unchanged.** -/
theorem contact_fixes_family (P : E →ₗ[ℝ] E) {h a : E} (hin : InContactFamily P a h) :
    contactSuccessor P h a = h := by
  simp only [contactSuccessor]
  rw [← hin]
  abel

/-- [proved-derived; formal-checked] **A second contact with the same family returns nothing.** -/
theorem contact_idempotent {P : E →ₗ[ℝ] E} (hP : IsOrthoProjection P) (h a : E) :
    contactSuccessor P (contactSuccessor P h a) a = contactSuccessor P h a :=
  contact_fixes_family P (contact_mem_family hP h a)

/-- [proved-derived; formal-checked] **The rational witness** of the resident test
`oblique_family_preserves_tangent_and_returns_normal_current`: `h = (7, 4)` against
`c₁ + c₂ = 2` returns `h' = (5/2, −1/2)`, `n_in = (1, 1)`, `n_ret = (11/2, 11/2)`, and both
sides of the exchange carry `67`. -/
theorem oblique_contact_witness :
    ((7 : ℚ) ^ 2 + 4 ^ 2) + (1 ^ 2 + 1 ^ 2) = ((5 / 2) ^ 2 + (-1 / 2) ^ 2) + ((11 / 2) ^ 2 + (11 / 2) ^ 2)
      ∧ ((7 : ℚ) ^ 2 + 4 ^ 2) + (1 ^ 2 + 1 ^ 2) = 67 := by
  norm_num

end AffineContact

end Soma.Holonics.HolonCore

