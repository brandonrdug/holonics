import Mathlib.NumberTheory.GaussSum
import Mathlib.Tactic

/-!
# Fourier exchanges the shift and the clock

The record `research/records/2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`
(§5 and §13(d)) owes to #410 the Heisenberg pair on `ℤ/n`: the shift `X` (the generator of
translation) and the clock `Z` (multiplication by a character, the modulator) are exchanged by the
Fourier chart, and do not commute by a pure phase. It checked them for `n = 2, …, 40`.

The character is a general additive character `ψ : ℤ/n → R` into a commutative ring, so the
statements are exact in every ring that holds one: `ψ(k) = ωᵏ` for `ω` an `n`-th root of unity, and
for `n = 4` the Gaussian integers with `ω = i`.

[proved-standard; formal-checked] What is proved.

1. **The Fourier chart exchanges them** (`fourier_shift`, `fourier_clock`): with
   `(X f)(j) = f(j − 1)`, `(Z f)(j) = ψ(j) f(j)` and `(F f)(j) = Σ_k ψ(j k) f(k)`,
   `F X = Z F` and `F Z = X⁻¹ F`.
2. **The defect is a pure phase** (`clock_shift`): `Z X = ψ(1)·X Z`, so `ω = ψ(1)`.
3. **The chart inverts over `n`** (`fourierBar_fourier`): for a primitive `ψ` into a domain, with
   `(F̄ f)(j) = Σ_k ψ(−j k) f(k)`, `F̄ F = n`. Over `ℤ[i]` at `n = 4` this is the chart "exact in
   Gaussian integers over 4".
4. **Stepping a ring is a turn in its dual chart** (`fourier_shift_iterate`, `clock_iterate`,
   `dual_turn`): `F Xˢ = Zˢ F` with `(Zˢ f)(j) = ψ(j)ˢ f(j)`, so `n·Xˢ = F̄ Zˢ F`. At `n = 4`,
   `ψ(j) = iʲ`, this is `F⁻¹ diag(i^(js)) F = Xˢ`.

Mathlib's `gaussSum_sq` carries the record's Gauss-sum line, `τ(χ)² = χ(−1)·q` for the quadratic
character of a finite field of `q` elements.

Consumers: the atlas row `motion.fourier-exchanges-shift-and-clock`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Geometry.ShiftClock

variable {n : ℕ} [NeZero n] {R : Type*} [CommRing R]

/-- [definition] The shift `(X f)(j) = f(j − 1)`. -/
def shift (f : ZMod n → R) : ZMod n → R := fun j => f (j - 1)

/-- [definition] The inverse shift `(X⁻¹ f)(j) = f(j + 1)`. -/
def unshift (f : ZMod n → R) : ZMod n → R := fun j => f (j + 1)

/-- [definition] The clock `(Z f)(j) = ψ(j) f(j)`. -/
def clock (ψ : AddChar (ZMod n) R) (f : ZMod n → R) : ZMod n → R := fun j => ψ j * f j

/-- [definition] The Fourier chart `(F f)(j) = Σ_k ψ(j k) f(k)`. -/
def fourier (ψ : AddChar (ZMod n) R) (f : ZMod n → R) : ZMod n → R :=
  fun j => ∑ k, ψ (j * k) * f k

/-- [definition] The conjugate chart `(F̄ f)(j) = Σ_k ψ(−j k) f(k)`. -/
def fourierBar (ψ : AddChar (ZMod n) R) (f : ZMod n → R) : ZMod n → R :=
  fun j => ∑ k, ψ (-(j * k)) * f k

theorem shift_unshift (f : ZMod n → R) : shift (unshift f) = f := by
  funext j
  simp [shift, unshift]

/-- [proved-standard; formal-checked] **`F X = Z F`.** -/
theorem fourier_shift (ψ : AddChar (ZMod n) R) (f : ZMod n → R) :
    fourier ψ (shift f) = clock ψ (fourier ψ f) := by
  funext j
  simp only [fourier, shift, clock, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.subRight 1) _ _ fun k => ?_
  simp only [Equiv.subRight_apply]
  rw [show j * k = j * (k - 1) + j by ring, AddChar.map_add_eq_mul]
  ring

/-- [proved-standard; formal-checked] **`F Z = X⁻¹ F`.** -/
theorem fourier_clock (ψ : AddChar (ZMod n) R) (f : ZMod n → R) :
    fourier ψ (clock ψ f) = unshift (fourier ψ f) := by
  funext j
  simp only [fourier, clock, unshift]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_mul, one_mul]

/-- [proved-standard; formal-checked] **`Z X = ω X Z` with `ω = ψ(1)`.** -/
theorem clock_shift (ψ : AddChar (ZMod n) R) (f : ZMod n → R) :
    clock ψ (shift f) = fun j => ψ 1 * shift (clock ψ f) j := by
  funext j
  have h : ψ j = ψ 1 * ψ (j - 1) := by
    rw [← AddChar.map_add_eq_mul]
    congr 1
    ring
  simp only [clock, shift]
  rw [h]
  ring

/-- [proved-standard; formal-checked] **The chart inverts over `n`:** `F̄ F = n` for a primitive
character into a domain. -/
theorem fourierBar_fourier [IsDomain R] (ψ : AddChar (ZMod n) R) (hψ : ψ.IsPrimitive)
    (f : ZMod n → R) :
    fourierBar ψ (fourier ψ f) = fun j => (n : R) * f j := by
  funext j
  simp only [fourierBar, fourier, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ l, ∑ k, ψ (-(j * k)) * (ψ (k * l) * f l) = (∑ k, ψ (k * (l - j))) * f l := by
    intro l
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp only [hterm, AddChar.sum_mulShift _ hψ, ZMod.card]
  rw [Finset.sum_eq_single j]
  · simp
  · intro l _ hl
    simp [sub_ne_zero.2 hl]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- [proved-standard; formal-checked] `F Xˢ = Zˢ F`. -/
theorem fourier_shift_iterate (ψ : AddChar (ZMod n) R) (s : ℕ) (f : ZMod n → R) :
    fourier ψ (shift^[s] f) = (clock ψ)^[s] (fourier ψ f) := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', fourier_shift, ih]

/-- [proved-standard; formal-checked] `(Zˢ f)(j) = ψ(j)ˢ f(j)`. -/
theorem clock_iterate (ψ : AddChar (ZMod n) R) (s : ℕ) (f : ZMod n → R) :
    (clock ψ)^[s] f = fun j => ψ j ^ s * f j := by
  induction s with
  | zero => funext j; simp
  | succ s ih =>
    rw [Function.iterate_succ_apply', ih]
    funext j
    simp only [clock]
    ring

/-- [proved-standard; formal-checked] **Stepping a ring is a turn in its dual chart:**
`n·Xˢ = F̄ Zˢ F`. -/
theorem dual_turn [IsDomain R] (ψ : AddChar (ZMod n) R) (hψ : ψ.IsPrimitive) (s : ℕ)
    (f : ZMod n → R) :
    (fun j => (n : R) * (shift^[s] f) j) =
      fourierBar ψ (fun j => ψ j ^ s * fourier ψ f j) := by
  rw [← clock_iterate, ← fourier_shift_iterate, fourierBar_fourier ψ hψ]

end Holonics.Geometry.ShiftClock
