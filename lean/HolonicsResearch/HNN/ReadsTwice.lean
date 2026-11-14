import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic

/-!
# The field that reads twice: the marked opening, its return, and both reads compared

The ring record of November 13 (`research/records/2026-11-13_THE_FIELD_RINGS_UNDER_ITS_OWN_RELEASE_…`, §4 and §5; atlas
`tower.field-mark`, `tower.field-carried-founding`) builds the field that reads twice (`hnn::tower::field`,
`FieldDeclaration::mark`). The first read gives each silent site a face; its shares `w_c` mark the site in the second read's
opening, which opens the site on `x = E(∗) + α (Σ_c w_c E(c) − E(∗))`, `E(∗)` the open row, `E(c)` the class rows, `α` the
mark's strength in that encoding, founded at zero. Since November 14 both reads are compared: each read returns into the one
covector and the section's sum is released by one bit once (`Field::both_reads_mean`). #410 owes three statements for it;
this file proves them on a real vector space, with the marks held (the shares are the first read's, read as given).

[proved-standard; formal-checked] What is proved.

1. **At zero strength the second read is the first** (`opening_zero`, `second_read_eq_first`): whatever reads the opening
   returns the first read's reading.
2. **The strength's covector at the founding is the carried slope** (`founding_covector`): with `L` the second read's code as
   a function of the opening and `L′` its covector at `E(∗)`, `d/dα L(x(α))` at `α = 0` is `L′(Σ_c w_c E(c) − E(∗))`, the
   pairing of the code's covector with the opening's change toward the first read's faces; off the founding the same pairing
   at `x(α)` (`strength_covector`).
3. **The marked opening's return is the adjoint of its forward** (`opening_expansion`, `return_is_adjoint`): the change of
   the opening under a change `(dE(∗), dE, dα)` of the open row, the class rows and the strength is its tangent
   `(1 − α) dE(∗) + α Σ_c w_c dE(c) + dα (Σ_c w_c E(c) − E(∗))` plus the product `dα (Σ_c w_c dE(c) − dE(∗))`, second
   order; and a covector `λ` paired with the tangent splits into the open row's `λ − αλ`, each class row's `α w_c λ` and the
   strength's `λ(Σ_c w_c E(c) − E(∗))`, the three terms `Field::opening_return` adds.
4. **Both reads compared** (`both_reads_covector`, `founding_mean`, `founding_strength_half`): the covector of the mean of
   the two reads' codes is the mean of their covectors; at the founding the two codes agree as functions of every other
   entry, so the mean's covector there is the one read's; and the first read does not see the strength, so the mean's
   strength covector is half the second read's (the host's test doubles the strength's sum against the carried slope).

Limits: stated over `ℝ` on a vector space; the realization's integer widths and its releases (`release(α dx, 24)`,
`release(w release(α dx, 24), 16)`, the section's one-bit release) are not modelled, and their remainders are the host's
tests' tolerance. The shares are held: the first read's dependence on the constitution is not differentiated, which is the
law's choice (the mark is the field's own placement as it was read), not a theorem. The Rust `Field::opening_return` and
`Field::both_reads_mean` are not tied to these statements.

The computational object is the helical pair interaction: the opening is the site's row at the pair contact's face, the
mark the first read's placement carried back into it. Of the winding guide's six general objects this touches the faces and
placement (the mark is a face read into the opening) and the tube (two reads of one region as a clocked span); the helix,
pair, cell holonomy and tower thread stay attached.

Consumers: the atlas rows `tower.field-mark` and `tower.field-carried-founding`; #410's box for the field that reads twice.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.ReadsTwice

open scoped BigOperators

variable {V : Type*} {ι : Type*} [Fintype ι]

/-! ## 1. The marked opening -/

section Algebra

variable [AddCommGroup V] [Module ℝ V]

/-- [definition] **The mark**: the class rows superposed by the first read's shares, `Σ_c w_c E(c)`. -/
def mark (E : ι → V) (w : ι → ℝ) : V := ∑ c, w c • E c

/-- [definition] **The marked opening** of a silent site, `E(∗) + α (Σ_c w_c E(c) − E(∗))`. -/
def opening (α : ℝ) (e : V) (E : ι → V) (w : ι → ℝ) : V := e + α • (mark E w - e)

/-- [proved-standard; formal-checked] At zero strength the opening is the open row. -/
theorem opening_zero (e : V) (E : ι → V) (w : ι → ℝ) : opening 0 e E w = e := by
  simp [opening]

/-- [proved-standard; formal-checked] **At zero strength the second read is the first**, whatever reads the opening. -/
theorem second_read_eq_first {F : Type*} (read : V → F) (e : V) (E : ι → V) (w : ι → ℝ) :
    read (opening 0 e E w) = read e := by
  rw [opening_zero]

/-- [proved-standard; formal-checked] The mark is linear in the class rows. -/
theorem mark_add (E dE : ι → V) (w : ι → ℝ) : mark (E + dE) w = mark E w + mark dE w := by
  simp [mark, Finset.sum_add_distrib, smul_add]

/-- [definition] **The opening's tangent** at `(α, E(∗), E)` in the direction `(dα, dE(∗), dE)`. -/
def tangent (α : ℝ) (e : V) (E : ι → V) (w : ι → ℝ) (de : V) (dE : ι → V) (dα : ℝ) : V :=
  (1 - α) • de + α • mark dE w + dα • (mark E w - e)

/-- [proved-standard; formal-checked] **The opening's expansion**: its change is the tangent plus the product of the
strength's change with the rows' change, `dα (Σ_c w_c dE(c) − dE(∗))`, which is second order. -/
theorem opening_expansion (α : ℝ) (e : V) (E : ι → V) (w : ι → ℝ) (de : V) (dE : ι → V) (dα : ℝ) :
    opening (α + dα) (e + de) (E + dE) w - opening α e E w =
      tangent α e E w de dE dα + dα • (mark dE w - de) := by
  simp only [opening, tangent, mark_add]
  module

/-- [proved-standard; formal-checked] **The return is the adjoint of the forward with the marks held**: a covector `l`
paired with the tangent splits into the open row's `l − α l`, each class row's `α w_c l` and the strength's
`l(Σ_c w_c E(c) − E(∗))`. -/
theorem return_is_adjoint (l : V →ₗ[ℝ] ℝ) (α : ℝ) (e : V) (E : ι → V) (w : ι → ℝ) (de : V) (dE : ι → V)
    (dα : ℝ) :
    l (tangent α e E w de dE dα) =
      (l de - α * l de) + ∑ c, (α * w c) * l (dE c) + dα * l (mark E w - e) := by
  simp only [tangent, mark, map_add, map_smul, map_sum, smul_eq_mul, Finset.mul_sum]
  have h : ∀ c, α * (w c * l (dE c)) = α * w c * l (dE c) := fun c => by ring
  simp only [h]
  ring

end Algebra

/-! ## 2. The strength's covector -/

section Calculus

variable [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- [proved-standard; formal-checked] The opening moves along the mark's difference as the strength moves. -/
theorem hasDerivAt_opening (α : ℝ) (e : V) (E : ι → V) (w : ι → ℝ) :
    HasDerivAt (fun a : ℝ => opening a e E w) (mark E w - e) α := by
  have h : HasDerivAt (fun a : ℝ => a • (mark E w - e)) ((1 : ℝ) • (mark E w - e)) α :=
    HasDerivAt.smul_const (hasDerivAt_id α) (mark E w - e)
  simpa [opening] using (hasDerivAt_const_add_iff e).2 h

/-- [proved-standard; formal-checked] **The strength's covector**: with `L′` the code's covector at the opening, the code's
derivative in the strength is `L′(Σ_c w_c E(c) − E(∗))`. -/
theorem strength_covector (L : V → ℝ) (L' : V →L[ℝ] ℝ) (α : ℝ) (e : V) (E : ι → V) (w : ι → ℝ)
    (hL : HasFDerivAt L L' (opening α e E w)) :
    HasDerivAt (fun a : ℝ => L (opening a e E w)) (L' (mark E w - e)) α :=
  hL.comp_hasDerivAt α (hasDerivAt_opening α e E w)

/-- [proved-standard; formal-checked] **The strength's covector at the founding is the carried slope**: at `α = 0` it is the
code's covector at the open row paired with the opening's change toward the first read's faces. -/
theorem founding_covector (L : V → ℝ) (L' : V →L[ℝ] ℝ) (e : V) (E : ι → V) (w : ι → ℝ)
    (hL : HasFDerivAt L L' e) :
    HasDerivAt (fun a : ℝ => L (opening a e E w)) (L' (mark E w - e)) 0 :=
  strength_covector L L' 0 e E w (by rwa [opening_zero])

end Calculus

/-! ## 3. Both reads compared -/

section Both

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- [proved-standard; formal-checked] **Both reads compared**: the covector of the mean of the two reads' codes is the
mean of their covectors. -/
theorem both_reads_covector (L₁ L₂ : P → ℝ) (g₁ g₂ : P →L[ℝ] ℝ) (θ : P) (h₁ : HasFDerivAt L₁ g₁ θ)
    (h₂ : HasFDerivAt L₂ g₂ θ) :
    HasFDerivAt (fun p => (L₁ p + L₂ p) / 2) ((1 / 2 : ℝ) • (g₁ + g₂)) θ := by
  have h := HasFDerivAt.const_mul (HasFDerivAt.add h₁ h₂) (1 / 2 : ℝ)
  have e : (fun p => (L₁ p + L₂ p) / 2) = fun y => 1 / 2 * (L₁ y + L₂ y) := by
    funext p
    ring
  rw [e]
  exact h

/-- [proved-standard; formal-checked] **At the founding the mean is the one read**: where the second read's code at zero
strength equals the first's for every other entry, the mean's covector there is the first read's. -/
theorem founding_mean (L₁ : P → ℝ) (L₂ : P → ℝ → ℝ) (g : P →L[ℝ] ℝ) (θ : P) (hfound : ∀ p, L₂ p 0 = L₁ p)
    (h : HasFDerivAt L₁ g θ) :
    HasFDerivAt (fun p => (L₁ p + L₂ p 0) / 2) g θ := by
  have e : (fun p => (L₁ p + L₂ p 0) / 2) = L₁ := by
    funext p
    rw [hfound]
    ring
  rw [e]
  exact h

/-- [proved-standard; formal-checked] **The mean's strength covector is half the second read's**: the first read does not
see the strength. -/
theorem founding_strength_half (ℓ : ℝ) (L₂ : ℝ → ℝ) (d α : ℝ) (h : HasDerivAt L₂ d α) :
    HasDerivAt (fun a => (ℓ + L₂ a) / 2) (d / 2) α := by
  exact HasDerivAt.div_const ((hasDerivAt_const_add_iff ℓ).2 h) 2

end Both

end Holonics.HNN.ReadsTwice
