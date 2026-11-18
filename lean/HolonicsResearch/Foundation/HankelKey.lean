import Mathlib

/-!
# A finite key for an unending census: a recurrence closes every larger Hankel determinant, and a curve's census is four exponentials

The record of November 15 (`research/records/2026-11-15_A_PROOF_REACHES_AN_UNENDING_FAMILY_AS_THE_ORBIT_OF_A_FINITE_MAP_…`,
§5; atlas `key.finite-hankel-rank`) reads an unending census held by finitely many modes as a finite key: the counts are the
traces of one map on a space of finite dimension, and the Hankel matrix `H i j = N (i + j + 1)` of the census has the rank of
the number of exponentials it sums (Kronecker 1881). Its ruler is a curve's census, `N_n = qⁿ + 1 − αⁿ − ᾱⁿ`, counted for
`y² = x³ + x² + 1` over `𝔽_3, …, 𝔽_(3^10)`. This file proves the direction a reader uses, from the finite key to the census,
and the ruler's arithmetic.

[proved-standard; formal-checked] What is proved.

1. **A recurrence closes every larger Hankel determinant** (`hankel_det_eq_zero`, `hankel_det_eq_zero_of_order_lt`): if a
   sequence over a commutative ring satisfies a linear recurrence of order `r` (Mathlib's `LinearRecurrence`), every Hankel
   determinant of order above `r`, at every shift, is zero. The recurrence's coefficients with `−1` are a vector the Hankel
   matrix annihilates (`hankel_mulVec_keyVector`): the finite key, read as a relation among the census's columns.
2. **A sum of `r` exponentials is held by `r` modes** (`sum_of_modes_isSolution`, `hankel_det_sum_of_modes_eq_zero`):
   `u n = Σ_k a_k λ_kⁿ` satisfies the recurrence whose characteristic polynomial is `∏_k (X − λ_k)`
   (`modesRecurrence_charPoly`), so its Hankel determinants of order above `r` vanish.
3. **A curve's census is four exponentials** (`modeSum_eq_pow_add_pow`, `census_eq_four_exponentials`): with
   `s₀ = 2, s₁ = a, s_(n+2) = a s_(n+1) − q s_n` and `N_n = qⁿ + 1 − s_n`, any `α, β` with `α + β = a`, `αβ = q` give
   `N_n = qⁿ + 1 − αⁿ − βⁿ`. The census satisfies the recurrence of order four (`census_isSolution`) whose characteristic
   polynomial is `(X − 1)(X − q)(X² − aX + q)` (`censusRecurrence_charPoly`), so its Hankel determinants of order five and
   above vanish at every shift (`census_hankel_det_eq_zero`).
4. **The modes stand at the half** (`hasse_places_modes`, `hasse_modes_at_half`): for real `a, q` with `a² < 4q`, every
   complex root of `X² − aX + q` has `‖α‖² = q`.
5. **The ruler** `q = 3, a = −2` (`ruler_census`, `ruler_hasse`, `ruler_hankel_dets`, `ruler_hankel_det_five`,
   `ruler_modes_at_half`): the ten counts `6, 12, 18, 96, 246, 684, 2274, 6528, 19494, 59532`; `a² = 4 ≤ 12 = 4q`; the
   Hankel determinants of orders 1 to 4 are `2·3`, `−2²·3²`, `−2⁵·3⁴·11`, `−2⁹·3⁸`, and of order 5 zero; the two modes have
   `‖α‖² = 3`.

Limits. Kronecker's converse (finite Hankel rank gives a rational generating function, and the rank is the number of
exponentials) is not stated; statement 1 is the direction from the key to the census, and the ruler's nonzero determinant of
order four with its zero determinant of order five is the finite reading of "rank four", and with it no recurrence of
order under four holds the ruler's census (`ruler_no_recurrence_of_order_under_four`). The counts themselves are taken from
the recurrence: that they count the points of `y² = x³ + x² + 1` over `𝔽_(3ⁿ)` is the record's point-by-point ruler and
Weil's theorem, neither proved here. Statement 4 is the algebra of a negative discriminant, the placement Hasse's bound gives;
the bound `a² ≤ 4q` for a curve's own `a` is Hasse's theorem and is used here only as the ruler's arithmetic. The integers'
census is not treated: this file holds the finite-rank case alone.

The computational object is the helical pair interaction: a mode `λⁿ` is a navigator's winding read at the census's clock, the
recurrence is the closure of `r` such windings, and the two modes of the curve are a pair exchanged by the reversal `α ↦ q/α`.
Of the winding guide's six general objects this touches the helix (the modes' powers), the pair (the two conjugate modes) and
faces and placement (the modes' placement at `√q`; the Hankel matrix as the faces of the census at lags `i + j`); cell
holonomy, the tube and the tower thread stay attached.

Consumers: the atlas row `key.finite-hankel-rank`; `birth.founded-against-hankel` reads a founding as a Hankel realization;
`FiniteKey` beside this file holds the half forced by a reversal and a pairing (`scaled_form_places_mode`).

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.HankelKey

open Matrix

/-! ## 1. A recurrence closes every larger Hankel determinant -/

section Hankel

variable {R : Type*} [CommRing R]

/-- [definition] **The Hankel matrix of a census** of order `m` at shift `s`: `H i j = u (i + j + s)`, the census read at
the lags `i + j`. -/
def hankel (u : ℕ → R) (s m : ℕ) : Matrix (Fin m) (Fin m) R := fun i j => u (i + j + s)

/-- [definition] **The finite key as a vector**: a recurrence's coefficients followed by `−1`. -/
def keyVector (E : LinearRecurrence R) : Fin (E.order + 1) → R :=
  Fin.snoc (α := fun _ => R) E.coeffs (-1)

/-- [proved-standard; formal-checked] **The Hankel matrix annihilates the key**: the last column of the Hankel matrix of
order `r + 1` is the recurrence's combination of the columns before it. -/
theorem hankel_mulVec_keyVector (E : LinearRecurrence R) (u : ℕ → R) (h : E.IsSolution u) (s : ℕ) :
    hankel u s (E.order + 1) *ᵥ keyVector E = 0 := by
  funext i
  simp only [mulVec, dotProduct, hankel, keyVector, Pi.zero_apply]
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, Fin.val_castSucc, Fin.val_last]
  have hrec := h (i + s)
  have e1 : (i : ℕ) + E.order + s = i + s + E.order := Nat.add_right_comm _ _ _
  have e2 : ∀ k : Fin E.order, (i : ℕ) + k + s = i + s + k := fun k => Nat.add_right_comm _ _ _
  simp only [e1, e2, hrec]
  rw [mul_neg_one, ← sub_eq_add_neg, sub_eq_zero]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

/-- [proved-standard; formal-checked] **A recurrence of order `r` closes the Hankel determinant of order `r + 1`**, at
every shift, over any commutative ring. -/
theorem hankel_det_eq_zero (E : LinearRecurrence R) (u : ℕ → R) (h : E.IsSolution u) (s : ℕ) :
    (hankel u s (E.order + 1)).det = 0 := by
  have hk := hankel_mulVec_keyVector E u h s
  have h2 : (hankel u s (E.order + 1)).det • keyVector E = 0 := by
    have h3 : ((hankel u s (E.order + 1)).adjugate * hankel u s (E.order + 1)) *ᵥ keyVector E
        = (hankel u s (E.order + 1)).det • keyVector E := by
      rw [adjugate_mul, smul_mulVec, one_mulVec]
    rw [← h3, ← mulVec_mulVec, hk, mulVec_zero]
  have h4 := congrFun h2 (Fin.last _)
  simpa [keyVector] using h4

/-- [definition] **A recurrence read one step later**: the same law with one more leading place, of coefficient zero. -/
def lift (E : LinearRecurrence R) : LinearRecurrence R :=
  ⟨E.order + 1, Fin.cons (α := fun _ => R) 0 E.coeffs⟩

/-- [proved-standard; formal-checked] **A census that satisfies a recurrence satisfies its lift.** -/
theorem lift_isSolution (E : LinearRecurrence R) (u : ℕ → R) (h : E.IsSolution u) :
    (lift E).IsSolution u := by
  intro n
  show u (n + (E.order + 1))
    = ∑ i : Fin (E.order + 1), (Fin.cons (α := fun _ => R) 0 E.coeffs : Fin (E.order + 1) → R) i * u (n + i)
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, zero_mul, zero_add, Fin.val_succ]
  have hrec := h (n + 1)
  have e1 : n + (E.order + 1) = n + 1 + E.order := by omega
  rw [e1, hrec]
  exact Finset.sum_congr rfl fun k _ => by rw [show n + 1 + (k : ℕ) = n + ((k : ℕ) + 1) by omega]

/-- [proved-standard; formal-checked] **A recurrence of order `r` gives one of every larger order.** -/
theorem exists_recurrence_of_order_add (E : LinearRecurrence R) (u : ℕ → R) (h : E.IsSolution u)
    (t : ℕ) : ∃ E' : LinearRecurrence R, E'.order = E.order + t ∧ E'.IsSolution u := by
  induction t with
  | zero => exact ⟨E, rfl, h⟩
  | succ t ih =>
    obtain ⟨E', hE', hsol⟩ := ih
    refine ⟨lift E', ?_, lift_isSolution E' u hsol⟩
    show E'.order + 1 = E.order + (t + 1)
    omega

/-- [proved-standard; formal-checked] **A finite key closes every larger Hankel determinant**: a census that satisfies
a recurrence of order `r` has every Hankel determinant of order above `r` equal to zero, at every shift. -/
theorem hankel_det_eq_zero_of_order_lt (E : LinearRecurrence R) (u : ℕ → R) (h : E.IsSolution u)
    (s : ℕ) {m : ℕ} (hm : E.order < m) : (hankel u s m).det = 0 := by
  obtain ⟨t, rfl⟩ : ∃ t, m = E.order + t + 1 := ⟨m - E.order - 1, by omega⟩
  obtain ⟨E', hE', hsol⟩ := exists_recurrence_of_order_add E u h t
  rw [← hE']
  exact hankel_det_eq_zero E' u hsol s

end Hankel

/-! ## 2. A sum of `r` exponentials is held by `r` modes -/

section Modes

variable {R : Type*} [CommRing R]

/-- [definition] **The modes' polynomial** `∏_k (X − λ_k)`. -/
noncomputable def modesPoly {r : ℕ} (lam : Fin r → R) : Polynomial R :=
  ∏ k, (Polynomial.X - Polynomial.C (lam k))

/-- [definition] **The recurrence of `r` modes**: its coefficients are the negated lower coefficients of the modes'
polynomial. -/
noncomputable def modesRecurrence {r : ℕ} (lam : Fin r → R) : LinearRecurrence R :=
  ⟨r, fun i => -(modesPoly lam).coeff i⟩

/-- [proved-standard; formal-checked] **The modes' recurrence has the modes' polynomial as its characteristic
polynomial.** -/
theorem modesRecurrence_charPoly [Nontrivial R] {r : ℕ} (lam : Fin r → R) :
    (modesRecurrence lam).charPoly = modesPoly lam := by
  have hmonic : (modesPoly lam).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun k _ => Polynomial.monic_X_sub_C _
  have hdeg : (modesPoly lam).natDegree = r := by
    simp [modesPoly, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  have hsum := hmonic.as_sum
  rw [hdeg] at hsum
  show Polynomial.monomial r 1 - ∑ i : Fin r, Polynomial.monomial (i : ℕ) (-(modesPoly lam).coeff i)
    = modesPoly lam
  refine Eq.trans ?_ hsum.symm
  rw [← Fin.sum_univ_eq_sum_range (fun i => Polynomial.C ((modesPoly lam).coeff i) * Polynomial.X ^ i) r]
  simp only [map_neg, Finset.sum_neg_distrib, sub_neg_eq_add, ← Polynomial.C_mul_X_pow_eq_monomial,
    Polynomial.C_1, one_mul]

/-- [proved-standard; formal-checked] **Each mode's powers satisfy the modes' recurrence.** -/
theorem mode_isSolution [Nontrivial R] {r : ℕ} (lam : Fin r → R) (k : Fin r) :
    (modesRecurrence lam).IsSolution fun n => lam k ^ n := by
  rw [LinearRecurrence.geom_sol_iff_root_charPoly, modesRecurrence_charPoly]
  simp only [Polynomial.IsRoot, modesPoly, Polynomial.eval_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp)

/-- [proved-standard; formal-checked] **A sum of `r` exponentials satisfies a recurrence of order `r`.** -/
theorem sum_of_modes_isSolution [Nontrivial R] {r : ℕ} (lam a : Fin r → R) :
    (modesRecurrence lam).IsSolution fun n => ∑ k, a k * lam k ^ n := by
  rw [LinearRecurrence.is_sol_iff_mem_solSpace]
  have h : (fun n => ∑ k, a k * lam k ^ n) = ∑ k, a k • (fun n : ℕ => lam k ^ n) := by
    funext n
    simp [Finset.sum_apply]
  rw [h]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _
    ((LinearRecurrence.is_sol_iff_mem_solSpace _ _).mp (mode_isSolution lam k))

/-- [proved-standard; formal-checked] **A census of `r` exponentials has no Hankel determinant of order above `r`**:
for `u n = Σ_k a_k λ_kⁿ`, every Hankel determinant of order `m > r`, at every shift, is zero. -/
theorem hankel_det_sum_of_modes_eq_zero {r : ℕ} (lam a : Fin r → R) (s : ℕ) {m : ℕ} (hm : r < m) :
    (hankel (fun n => ∑ k, a k * lam k ^ n) s m).det = 0 := by
  rcases subsingleton_or_nontrivial R with hR | hR
  · exact Subsingleton.elim _ _
  · exact hankel_det_eq_zero_of_order_lt (modesRecurrence lam) _ (sum_of_modes_isSolution lam a) s hm

end Modes

/-! ## 3. A curve's census is four exponentials -/

section Census

variable {R : Type*} [CommRing R]

/-- [definition] **The power sums of a curve's two modes**, from their sum `a` and product `q`:
`s₀ = 2`, `s₁ = a`, `s_(n+2) = a s_(n+1) − q s_n`. -/
def modeSum (a q : R) : ℕ → R
  | 0 => 2
  | 1 => a
  | n + 2 => a * modeSum a q (n + 1) - q * modeSum a q n

/-- [definition] **A curve's census** over the extension of degree `n`: `N_n = qⁿ + 1 − s_n`. -/
def census (a q : R) (n : ℕ) : R := q ^ n + 1 - modeSum a q n

/-- [proved-standard; formal-checked] **The power sums are the two modes' powers**: `s_n = αⁿ + βⁿ` for any `α, β`
with sum `a` and product `q`. -/
theorem modeSum_eq_pow_add_pow (α β : R) (n : ℕ) :
    modeSum (α + β) (α * β) n = α ^ n + β ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num [modeSum]
  | one => simp [modeSum]
  | more n ih0 ih1 =>
    rw [show modeSum (α + β) (α * β) (n + 2)
      = (α + β) * modeSum (α + β) (α * β) (n + 1) - α * β * modeSum (α + β) (α * β) n from rfl, ih1, ih0]
    ring

/-- [proved-standard; formal-checked] **The census is four exponentials**: `N_n = qⁿ + 1ⁿ − αⁿ − βⁿ` with `q = αβ`. -/
theorem census_eq_four_exponentials (α β : R) (n : ℕ) :
    census (α + β) (α * β) n = (α * β) ^ n + 1 ^ n - α ^ n - β ^ n := by
  rw [census, modeSum_eq_pow_add_pow, one_pow]
  ring

/-- [definition] **The census's recurrence of order four**, the coefficients of `(X − 1)(X − q)(X² − aX + q)`. -/
def censusRecurrence (a q : R) : LinearRecurrence R :=
  ⟨4, ![-(q ^ 2), q + q ^ 2 + a * q, -(2 * q + a + a * q), a + 1 + q]⟩

/-- [proved-standard; formal-checked] **The census satisfies its recurrence of order four**:
`N_(n+4) = (a + 1 + q) N_(n+3) − (2q + a + aq) N_(n+2) + (q + q² + aq) N_(n+1) − q² N_n`. -/
theorem census_isSolution (a q : R) : (censusRecurrence a q).IsSolution (census a q) := by
  intro n
  have h2 : modeSum a q (n + 2) = a * modeSum a q (n + 1) - q * modeSum a q n := rfl
  have h3 : modeSum a q (n + 3) = a * modeSum a q (n + 2) - q * modeSum a q (n + 1) := rfl
  have h4 : modeSum a q (n + 4) = a * modeSum a q (n + 3) - q * modeSum a q (n + 2) := rfl
  show census a q (n + 4) = ∑ i : Fin 4,
    (![-(q ^ 2), q + q ^ 2 + a * q, -(2 * q + a + a * q), a + 1 + q] : Fin 4 → R) i * census a q (n + i)
  simp [Fin.sum_univ_four, census, h4, h3, h2, pow_add]
  ring

/-- [proved-standard; formal-checked] **The recurrence's characteristic polynomial is
`(X − 1)(X − q)(X² − aX + q)`**: the four modes `1`, `q` and the two roots of `X² − aX + q`. -/
theorem censusRecurrence_charPoly (a q : R) :
    (censusRecurrence a q).charPoly
      = (Polynomial.X - 1) * (Polynomial.X - Polynomial.C q)
        * (Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + Polynomial.C q) := by
  show Polynomial.monomial 4 1 - ∑ i : Fin 4, Polynomial.monomial (i : ℕ)
    ((![-(q ^ 2), q + q ^ 2 + a * q, -(2 * q + a + a * q), a + 1 + q] : Fin 4 → R) i) = _
  have h2 : (Polynomial.C (2 : R)) = 2 := map_ofNat Polynomial.C 2
  simp only [Fin.sum_univ_four, ← Polynomial.C_mul_X_pow_eq_monomial]
  simp
  rw [h2]
  ring

/-- [proved-standard; formal-checked] **The census's Hankel determinants of order five and above vanish**, at every
shift: four numbers hold the unending family of counts. -/
theorem census_hankel_det_eq_zero (a q : R) (s : ℕ) {m : ℕ} (hm : 4 < m) :
    (hankel (census a q) s m).det = 0 :=
  hankel_det_eq_zero_of_order_lt (censusRecurrence a q) _ (census_isSolution a q) s hm

end Census

/-! ## 4. The modes stand at the half -/

/-- [proved-standard; formal-checked] **A negative discriminant places both modes at `‖α‖² = q`**: for real `a, q`
with `a² < 4q`, every complex root of `X² − aX + q` has squared modulus `q`. For a curve's own `a` the hypothesis is
Hasse's bound, strict. -/
theorem hasse_places_modes (a q : ℝ) (h : a ^ 2 < 4 * q) (α : ℂ)
    (hα : α ^ 2 - (a : ℂ) * α + (q : ℂ) = 0) : ‖α‖ ^ 2 = q := by
  have hre := congrArg Complex.re hα
  have him := congrArg Complex.im hα
  simp only [pow_two, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.zero_re, Complex.zero_im, zero_mul, sub_zero,
    add_zero] at hre him
  rw [Complex.sq_norm, Complex.normSq_apply]
  have hy : α.im * (2 * α.re - a) = 0 := by linarith
  rcases mul_eq_zero.mp hy with h0 | h0
  · exfalso
    rw [h0] at hre
    nlinarith [sq_nonneg (2 * α.re - a)]
  · have ha : a = 2 * α.re := by linarith
    rw [ha] at hre
    linarith

/-- [proved-standard; formal-checked] **The half**: under the same hypothesis, `‖α‖ = √q`. -/
theorem hasse_modes_at_half (a q : ℝ) (h : a ^ 2 < 4 * q) (α : ℂ)
    (hα : α ^ 2 - (a : ℂ) * α + (q : ℂ) = 0) : ‖α‖ = Real.sqrt q := by
  rw [← hasse_places_modes a q h α hα, Real.sqrt_sq (norm_nonneg α)]

/-! ## 5. The ruler: `y² = x³ + x² + 1` over `𝔽_(3ⁿ)`, `q = 3`, `a = −2` -/

/-- [proved-standard; formal-checked] **The ruler's ten counts**, `N_1, …, N_10` from `α + ᾱ = −2`, `αᾱ = 3`:
`2·3, 2²·3, 2·3², 2⁵·3, 2·3·41, 2²·3²·19, 2·3·379, 2⁷·3·17, 2·3³·19², 2²·3·11²·41`. -/
theorem ruler_census :
    census (-2 : ℤ) 3 1 = 6 ∧ census (-2 : ℤ) 3 2 = 12 ∧ census (-2 : ℤ) 3 3 = 18 ∧
    census (-2 : ℤ) 3 4 = 96 ∧ census (-2 : ℤ) 3 5 = 246 ∧ census (-2 : ℤ) 3 6 = 684 ∧
    census (-2 : ℤ) 3 7 = 2274 ∧ census (-2 : ℤ) 3 8 = 6528 ∧ census (-2 : ℤ) 3 9 = 19494 ∧
    census (-2 : ℤ) 3 10 = 59532 := by
  decide

/-- [proved-standard; formal-checked] **The counts' factorizations.** -/
theorem ruler_census_factored :
    (6 : ℤ) = 2 * 3 ∧ (12 : ℤ) = 2 ^ 2 * 3 ∧ (18 : ℤ) = 2 * 3 ^ 2 ∧ (96 : ℤ) = 2 ^ 5 * 3 ∧
    (246 : ℤ) = 2 * 3 * 41 ∧ (684 : ℤ) = 2 ^ 2 * 3 ^ 2 * 19 ∧ (2274 : ℤ) = 2 * 3 * 379 ∧
    (6528 : ℤ) = 2 ^ 7 * 3 * 17 ∧ (19494 : ℤ) = 2 * 3 ^ 3 * 19 ^ 2 ∧
    (59532 : ℤ) = 2 ^ 2 * 3 * 11 ^ 2 * 41 := by
  norm_num

/-- [proved-standard; formal-checked] **Hasse's bound on the ruler**: `a² = 4 ≤ 12 = 4q`, strictly. -/
theorem ruler_hasse : ((-2 : ℤ)) ^ 2 < 4 * 3 := by norm_num

/-- [proved-standard; formal-checked] **The ruler's two modes stand at the half**: every root of `X² + 2X + 3` has
`‖α‖² = 3`. -/
theorem ruler_modes_at_half (α : ℂ) (hα : α ^ 2 + 2 * α + 3 = 0) : ‖α‖ ^ 2 = 3 := by
  have h := hasse_places_modes (-2) 3 (by norm_num) α (by push_cast; linear_combination hα)
  exact h

/-- [proved-standard; formal-checked] The ruler's Hankel matrix of order two. -/
theorem ruler_hankel_two :
    hankel (census (-2 : ℤ) 3) 1 2 = !![6, 12; 12, 18] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- [proved-standard; formal-checked] The ruler's Hankel matrix of order three. -/
theorem ruler_hankel_three :
    hankel (census (-2 : ℤ) 3) 1 3 = !![6, 12, 18; 12, 18, 96; 18, 96, 246] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- [proved-standard; formal-checked] The ruler's Hankel matrix of order four. -/
theorem ruler_hankel_four :
    hankel (census (-2 : ℤ) 3) 1 4
      = !![6, 12, 18, 96; 12, 18, 96, 246; 18, 96, 246, 684; 96, 246, 684, 2274] := by
  ext i j; fin_cases i <;> fin_cases j <;> decide

/-- [proved-standard; formal-checked] **The ruler's Hankel determinants of orders 1 to 4** (`H i j = N_(i+j+1)`):
`2·3`, `−2²·3²`, `−2⁵·3⁴·11`, `−2⁹·3⁸`. None is zero, so no recurrence of order under four holds the census. -/
theorem ruler_hankel_dets :
    (hankel (census (-2 : ℤ) 3) 1 1).det = 2 * 3 ∧
    (hankel (census (-2 : ℤ) 3) 1 2).det = -(2 ^ 2 * 3 ^ 2) ∧
    (hankel (census (-2 : ℤ) 3) 1 3).det = -(2 ^ 5 * 3 ^ 4 * 11) ∧
    (hankel (census (-2 : ℤ) 3) 1 4).det = -(2 ^ 9 * 3 ^ 8) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [det_unique]; decide
  · rw [ruler_hankel_two, det_fin_two]; decide
  · rw [ruler_hankel_three, det_fin_three]; decide
  · rw [ruler_hankel_four]
    simp [det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

/-- [proved-standard; formal-checked] **The ruler's Hankel determinant of order five is zero**, as every larger one is:
four numbers hold the ten counts and every count after them. -/
theorem ruler_hankel_det_five : (hankel (census (-2 : ℤ) 3) 1 5).det = 0 :=
  census_hankel_det_eq_zero (-2) 3 1 (by norm_num)

/-- [proved-standard; formal-checked] **The order-four determinant is not zero**: with `ruler_hankel_det_five` and
`census_hankel_det_eq_zero`, the finite reading of the census's Hankel rank four. -/
theorem ruler_hankel_det_four_ne_zero : (hankel (census (-2 : ℤ) 3) 1 4).det ≠ 0 := by
  rw [ruler_hankel_dets.2.2.2]; norm_num

/-- [proved-standard; formal-checked] **No shorter key holds the ruler's census**: every linear recurrence over `ℤ`
that the census satisfies has order at least four, and `census_isSolution` gives one of order four. -/
theorem ruler_no_recurrence_of_order_under_four (E : LinearRecurrence ℤ)
    (h : E.IsSolution (census (-2 : ℤ) 3)) : 4 ≤ E.order := by
  by_contra hlt
  exact ruler_hankel_det_four_ne_zero
    (hankel_det_eq_zero_of_order_lt E _ h 1 (Nat.lt_of_not_le hlt))

end Holonics.Foundation.HankelKey
