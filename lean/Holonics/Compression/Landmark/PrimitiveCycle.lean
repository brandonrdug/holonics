import Holonics.Aeon.Production.Zeta
import Mathlib.Dynamics.PeriodicPts.Lemmas
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic

/-!
# Primes of the machine: the primitive-cycle Euler product of the return-map zeta

[definition] A finite **return map** is a map `f` of a finite set of occurrences, with the `0/1`
matrix `M_f` of `Aeon/Production/Zeta` (`mapMatrix`); `N_n = tr(M_fⁿ)` counts its closed aeons of
`n` epochs (`trace_pow_mapMatrix`). A **primitive cycle** of length `d` is a periodic orbit of
least period `d` (`primitiveCycles`, Mathlib's `periodicOrbit`); its count is `p_d`
(`primitiveCount`). Primitive cycles are the primes of the machine: every closed aeon is a
repetition of exactly one of them.

[proved-derived; formal-checked] What is proved.

1. **Each primitive cycle of length `d` carries exactly `d` occurrences**
   (`card_minimalPeriod_eq`: `#{x | least period d} = d · p_d`).
2. **The counting identity** `N_n = tr(M_fⁿ) = Σ_(d ∣ n) d · p_d` for `n ≥ 1`
   (`periodic_count`, `trace_pow_eq_primitive`).
3. **Möbius inversion** recovers the primes from the counts:
   `d · p_d = Σ_(ab = d) μ(a) N_b` (`primitive_count_moebius`).
4. **The Euler product.** The transfer determinant is the product over primitive cycles,
   `det(1 − T·M_f) = ∏_d (1 − T^d)^(p_d)` as polynomials (`transfer_determinant_euler_product`).
   The proof is the log/trace identity: the logarithmic derivative of one primitive factor
   `1 − T^d` is `−Σ_k d·[d ∣ k+1] Tᵏ` (`cycleFactor_logDeriv`), so the product's logarithmic
   derivative has coefficients `−Σ_(d ∣ k+1) d p_d = −N_(k+1)`, which is the transfer
   determinant's (`Zeta.transferDet_derivative`); a power series is fixed by its logarithmic
   derivative and constant term (`HasLogDeriv.unique`).

[proved-derived; formal-checked] A join, not a further law: rewriting the Euler product into the
existing `Aeon/Production/Zeta.zeta_eq_exp` reads the dynamical zeta as the product over primitive
cycles, `exp(Σ_n N_n Tⁿ/n) · ∏_d (1 − T^d)^(p_d) = 1`, i.e. `ζ(T) = ∏_γ (1 − T^|γ|)⁻¹`
(`zeta_euler_product`).

[counterexample; formal-checked] **Nonnegativity is load-bearing.** The signed return map `[[−1]]`
has `N_1 = −1`, so the Möbius inversion would give `1 · p_1 = −1`: no map of occurrences has these
counts (`signed_map_has_no_primitive_cycles`).

[open] Owed in #62: for a general nonnegative integer matrix (a multigraph's return map) the
Möbius-inverted `p_d` are the numbers of primitive closed walks up to rotation (necklace counts,
e.g. `[[2]]`: `2, 1, 2, 3, 6, …`), and the Euler product is infinite; the necklace integrality and
the infinite product are not formalized here. The prime-number case (`ζ(s) = ∏_p (1 − p^(−s))⁻¹`
as the zeta of the scaling flow) is an analogy of the same form, not a theorem of this module.

No `axiom`, no `sorry`.
-/

noncomputable section

namespace Holonics.Compression.Landmark.PrimitiveCycle

open Finset Function PowerSeries
open Holonics.Aeon.Production.Zeta

/-! ## 1. Logarithmic derivatives of power series -/

/-- [definition] `A` is the logarithmic derivative of `F`: `F′ = F·A`. -/
def HasLogDeriv (F A : PowerSeries ℚ) : Prop := derivative ℚ F = F * A

namespace HasLogDeriv

theorem one : HasLogDeriv 1 0 := by
  unfold HasLogDeriv
  rw [derivative_one, mul_zero]

theorem mul {F G A B : PowerSeries ℚ} (hF : HasLogDeriv F A) (hG : HasLogDeriv G B) :
    HasLogDeriv (F * G) (A + B) := by
  unfold HasLogDeriv at *
  rw [Derivation.leibniz, hF, hG, smul_eq_mul, smul_eq_mul]
  ring

theorem pow {F A : PowerSeries ℚ} (hF : HasLogDeriv F A) (n : ℕ) :
    HasLogDeriv (F ^ n) (C (n : ℚ) * A) := by
  induction n with
  | zero => simpa using one
  | succ n ih =>
    rw [pow_succ]
    have := ih.mul hF
    unfold HasLogDeriv at *
    rw [this]
    push_cast
    rw [map_add, map_one]
    ring

theorem prod {ι : Type*} (s : Finset ι) (F A : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, HasLogDeriv (F i) (A i)) : HasLogDeriv (∏ i ∈ s, F i) (∑ i ∈ s, A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using one
  | insert a s ha ih =>
    rw [prod_insert ha, sum_insert ha]
    exact (h a (mem_insert_self a s)).mul (ih fun i hi => h i (mem_insert_of_mem hi))

/-- [proved-derived; formal-checked] **A power series is fixed by its logarithmic derivative and
its constant term.** -/
theorem unique {F G A : PowerSeries ℚ} (hF : HasLogDeriv F A) (hG : HasLogDeriv G A)
    (h0 : constantCoeff F = constantCoeff G) (hG0 : constantCoeff G ≠ 0) : F = G := by
  have hinv : G⁻¹ * G = 1 := PowerSeries.inv_mul_cancel G hG0
  have hsq : G⁻¹ ^ 2 * G = G⁻¹ := by rw [sq, mul_assoc, hinv, mul_one]
  have hH : derivative ℚ (F * G⁻¹) = derivative ℚ 1 := by
    unfold HasLogDeriv at hF hG
    rw [Derivation.leibniz, derivative_inv', hF, hG, derivative_one, smul_eq_mul, smul_eq_mul]
    linear_combination (-(F * A)) * hsq
  have hc : constantCoeff (F * G⁻¹) = constantCoeff (1 : PowerSeries ℚ) := by
    rw [map_mul, constantCoeff_inv, h0, mul_inv_cancel₀ hG0, map_one]
  have h1 : F * G⁻¹ = 1 := derivative.ext hH hc
  calc F = F * (G⁻¹ * G) := by rw [hinv, mul_one]
    _ = (F * G⁻¹) * G := by ring
    _ = G := by rw [h1, one_mul]

end HasLogDeriv

/-! ## 2. The factor of one primitive cycle -/

/-- [definition] The logarithmic current of a primitive cycle of length `d`:
`Σ_k d·[d ∣ k+1] Tᵏ`, the derivative of `Σ_j T^(dj)/j`. -/
def cycleCurrent (d : ℕ) : PowerSeries ℚ := PowerSeries.mk fun k => if d ∣ k + 1 then (d : ℚ) else 0

theorem one_sub_X_pow_mul_cycleCurrent (d : ℕ) (hd : 0 < d) :
    (1 - X ^ d) * cycleCurrent d = C (d : ℚ) * X ^ (d - 1) := by
  ext k
  rw [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_C_mul_X_pow]
  simp only [cycleCurrent, coeff_mk]
  by_cases hkd : d ≤ k
  · have hne : k ≠ d - 1 := by omega
    have hiff : d ∣ k + 1 ↔ d ∣ k - d + 1 := by
      have : k + 1 = (k - d + 1) + d := by omega
      rw [this]
      exact Nat.dvd_add_self_right
    rw [if_pos hkd, if_neg hne]
    by_cases h : d ∣ k + 1
    · rw [if_pos h, if_pos (hiff.mp h), sub_self]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h')), sub_self]
  · rw [if_neg hkd, sub_zero]
    have hiff : d ∣ k + 1 ↔ k = d - 1 := by
      constructor
      · intro h
        have := Nat.le_of_dvd (by omega) h
        omega
      · intro h
        rw [h, Nat.sub_add_cancel hd]
    by_cases h : d ∣ k + 1
    · rw [if_pos h, if_pos (hiff.mp h)]
    · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

/-- [proved-derived; formal-checked] **The logarithmic derivative of one primitive factor**
`1 − T^d` is `−Σ_k d·[d ∣ k+1] Tᵏ`. -/
theorem cycleFactor_logDeriv (d : ℕ) (hd : 0 < d) :
    HasLogDeriv (1 - X ^ d) (-cycleCurrent d) := by
  unfold HasLogDeriv
  rw [mul_neg, one_sub_X_pow_mul_cycleCurrent d hd, map_sub, derivative_one, derivative_pow,
    derivative_X, zero_sub, mul_one, map_natCast]

/-! ## 3. Primitive cycles of a finite return map -/

section Primitive

variable {α : Type*} [Fintype α] [DecidableEq α] (f : α → α)

/-- [definition] The primitive cycles of length `d`: the periodic orbits of least period `d`. -/
def primitiveCycles (d : ℕ) : Finset (Cycle α) :=
  (univ.filter fun x => minimalPeriod f x = d).image (periodicOrbit f)

/-- [definition] The number `p_d` of primitive cycles of length `d`. -/
def primitiveCount (d : ℕ) : ℕ := (primitiveCycles f d).card

/-- [proved-derived; formal-checked] **A primitive cycle of length `d` carries `d` occurrences:**
`#{x | least period d} = d · p_d`. -/
theorem card_minimalPeriod_eq (d : ℕ) (hd : 0 < d) :
    (univ.filter fun x => minimalPeriod f x = d).card = d * primitiveCount f d := by
  rw [card_eq_sum_card_image (periodicOrbit f), primitiveCount, primitiveCycles, mul_comm,
    ← smul_eq_mul, ← sum_const]
  refine sum_congr rfl fun c hc => ?_
  obtain ⟨x, hx, rfl⟩ := mem_image.mp hc
  have hxd : minimalPeriod f x = d := (mem_filter.mp hx).2
  have hxp : x ∈ periodicPts f := minimalPeriod_pos_iff_mem_periodicPts.mp (hxd ▸ hd)
  have hfib : ((univ.filter fun x => minimalPeriod f x = d).filter
      fun y => periodicOrbit f y = periodicOrbit f x) = (range d).image (fun i => f^[i] x) := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_range]
    constructor
    · rintro ⟨hyd, hyo⟩
      have hyp : y ∈ periodicPts f := minimalPeriod_pos_iff_mem_periodicPts.mp (hyd ▸ hd)
      have hymem : y ∈ periodicOrbit f x := hyo ▸ self_mem_periodicOrbit hyp
      obtain ⟨n, hn⟩ := (mem_periodicOrbit_iff hxp).mp hymem
      refine ⟨n % d, Nat.mod_lt _ hd, ?_⟩
      rw [← hn, ← hxd, iterate_mod_minimalPeriod_eq]
    · rintro ⟨i, -, rfl⟩
      exact ⟨by rw [minimalPeriod_apply_iterate hxp, hxd], periodicOrbit_apply_iterate_eq hxp i⟩
  rw [hfib, card_image_of_injOn, card_range]
  intro i hi j hj hij
  apply iterate_injOn_Iio_minimalPeriod
  · simp only [coe_range, Set.mem_Iio] at hi ⊢; rw [hxd]; exact hi
  · simp only [coe_range, Set.mem_Iio] at hj ⊢; rw [hxd]; exact hj
  · exact hij

/-- [proved-derived; formal-checked] Above the size of the occurrence set there is no primitive
cycle. -/
theorem primitiveCount_eq_zero_of_card_lt (d : ℕ) (hd : Fintype.card α < d) :
    primitiveCount f d = 0 := by
  rw [primitiveCount, primitiveCycles, card_eq_zero, image_eq_empty, filter_eq_empty_iff]
  intro x _ hx
  have := minimalPeriod_le_card (f := f) (x := x)
  omega

/-- [proved-derived; formal-checked] **The counting identity:** the closed aeons of `n` epochs are
the repetitions of the primitive cycles whose lengths divide `n`,
`#{x | fⁿ x = x} = Σ_(d ∣ n) d · p_d`. -/
theorem periodic_count (n : ℕ) (hn : 0 < n) :
    (univ.filter fun x => f^[n] x = x).card = ∑ d ∈ n.divisors, d * primitiveCount f d := by
  rw [card_eq_sum_card_fiberwise (f := minimalPeriod f) (t := n.divisors)]
  · refine sum_congr rfl fun d hd => ?_
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
    rw [← card_minimalPeriod_eq f d hdpos, filter_filter]
    congr 1
    apply filter_congr
    intro x _
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have : IsPeriodicPt f n x := isPeriodicPt_iff_minimalPeriod_dvd.mpr (h ▸ hdn)
      exact this
  · intro x hx
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hx
    have hdvd : minimalPeriod f x ∣ n := isPeriodicPt_iff_minimalPeriod_dvd.mp hx
    exact Nat.mem_divisors.mpr ⟨hdvd, hn.ne'⟩

/-- [proved-derived; formal-checked] **The counting identity on the return map:**
`tr(M_fⁿ) = Σ_(d ∣ n) d · p_d`. -/
theorem trace_pow_eq_primitive (n : ℕ) (hn : 0 < n) :
    Matrix.trace (mapMatrix f ^ n) = ∑ d ∈ n.divisors, (d : ℚ) * primitiveCount f d := by
  rw [trace_pow_mapMatrix, periodic_count f n hn]
  push_cast
  rfl

/-- [proved-derived; formal-checked] **Möbius inversion: the primes of the machine from its
counts,** `d · p_d = Σ_(ab = d) μ(a) N_b`. -/
theorem primitive_count_moebius (d : ℕ) (hd : 0 < d) :
    ((d * primitiveCount f d : ℕ) : ℤ) = ∑ x ∈ d.divisorsAntidiagonal,
      (ArithmeticFunction.moebius x.1 : ℤ) * ((univ.filter fun y => f^[x.2] y = y).card : ℤ) := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun i => ((i * primitiveCount f i : ℕ) : ℤ))
    (g := fun n => ((univ.filter fun y => f^[n] y = y).card : ℤ))).mp
    (fun n hn => by
      rw [periodic_count f n hn]
      push_cast
      rfl) d hd
  exact h.symm

/-- [proved-derived; formal-checked] **The Euler product of the transfer determinant:**
`det(1 − T·M_f) = ∏_d (1 − T^d)^(p_d)`, as power series. -/
theorem transfer_determinant_euler_product_series :
    ((mapMatrix f).charpolyRev : PowerSeries ℚ)
      = ∏ d ∈ Icc 1 (Fintype.card α), (1 - X ^ d) ^ primitiveCount f d := by
  set A : PowerSeries ℚ := -PowerSeries.mk fun k => Matrix.trace (mapMatrix f ^ (k + 1)) with hA
  have h1 : constantCoeff ((mapMatrix f).charpolyRev : PowerSeries ℚ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have h2 : constantCoeff
      (∏ d ∈ Icc 1 (Fintype.card α), (1 - X ^ d) ^ primitiveCount f d : PowerSeries ℚ) = 1 := by
    rw [map_prod]
    apply prod_eq_one
    intro x hx
    have hx1 : x ≠ 0 := by simp only [mem_Icc] at hx; omega
    simp [zero_pow hx1]
  apply HasLogDeriv.unique (A := A) _ _ (h1.trans h2.symm) (by rw [h2]; exact one_ne_zero)
  · unfold HasLogDeriv
    rw [transferDet_derivative, hA]
    ring
  · have hprod := HasLogDeriv.prod (Icc 1 (Fintype.card α))
      (fun d => (1 - X ^ d) ^ primitiveCount f d)
      (fun d => C (primitiveCount f d : ℚ) * (-cycleCurrent d))
      (fun d hd => (cycleFactor_logDeriv d (by simp at hd; omega)).pow _)
    convert hprod using 1
    rw [hA]
    ext k
    simp only [map_neg, coeff_mk, map_sum, coeff_C_mul, cycleCurrent, mul_neg, sum_neg_distrib,
      neg_inj]
    rw [trace_pow_eq_primitive f (k + 1) (Nat.succ_pos k)]
    have hfilter : ∑ x ∈ Icc 1 (Fintype.card α),
        (primitiveCount f x : ℚ) * (if x ∣ k + 1 then (x : ℚ) else 0)
        = ∑ x ∈ (Icc 1 (Fintype.card α)).filter (· ∣ k + 1), (x : ℚ) * primitiveCount f x := by
      rw [sum_filter]
      refine sum_congr rfl fun x _ => ?_
      split_ifs <;> ring
    rw [hfilter]
    symm
    apply sum_subset
    · intro x hx
      simp only [mem_filter, mem_Icc] at hx
      exact Nat.mem_divisors.mpr ⟨hx.2, Nat.succ_ne_zero k⟩
    · intro x hx hnot
      have hxpos : 0 < x := Nat.pos_of_mem_divisors hx
      have hxd : x ∣ k + 1 := Nat.dvd_of_mem_divisors hx
      have hcard : Fintype.card α < x := by
        by_contra hle
        apply hnot
        simp only [mem_filter, mem_Icc]
        exact ⟨⟨hxpos, not_lt.mp hle⟩, hxd⟩
      rw [primitiveCount_eq_zero_of_card_lt f x hcard]
      simp

/-- [proved-derived; formal-checked] **The Euler product of the transfer determinant, as
polynomials:** `det(1 − T·M_f) = ∏_d (1 − T^d)^(p_d)`. -/
theorem transfer_determinant_euler_product :
    (mapMatrix f).charpolyRev
      = ∏ d ∈ Icc 1 (Fintype.card α), (1 - Polynomial.X ^ d) ^ primitiveCount f d := by
  have hcoe : ((∏ d ∈ Icc 1 (Fintype.card α), (1 - Polynomial.X ^ d) ^ primitiveCount f d :
      Polynomial ℚ) : PowerSeries ℚ)
      = ∏ d ∈ Icc 1 (Fintype.card α), (1 - X ^ d) ^ primitiveCount f d := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_prod]
    refine prod_congr rfl fun d _ => ?_
    rw [map_pow, map_sub, map_one, map_pow, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_X]
  apply Polynomial.coe_injective ℚ
  rw [transfer_determinant_euler_product_series, hcoe]

/-- [proved-derived; formal-checked] A join: `transfer_determinant_euler_product_series` rewritten
into `Zeta.zeta_eq_exp`, reading the dynamical zeta as the Euler product over primitive cycles,
`exp(Σ_n N_n Tⁿ/n) · ∏_d (1 − T^d)^(p_d) = 1`, i.e. `ζ(T) = ∏_γ (1 − T^|γ|)⁻¹`. -/
theorem zeta_euler_product :
    (PowerSeries.exp ℚ).subst (cycleLog (mapMatrix f)) *
        ∏ d ∈ Icc 1 (Fintype.card α), (1 - X ^ d) ^ primitiveCount f d = 1 := by
  rw [← transfer_determinant_euler_product_series]
  exact zeta_eq_exp _

end Primitive

/-! ## 4. Nonnegativity is load-bearing -/

/-- [counterexample; formal-checked] **A signed return map has no primitive cycles.** `[[−1]]` has
`N_1 = tr M = −1`, which no map of occurrences realizes, since `N_1` counts fixed occurrences. -/
theorem signed_map_has_no_primitive_cycles :
    Matrix.trace (!![-1] : Matrix (Fin 1) (Fin 1) ℚ) = -1 ∧
      ∀ (β : Type) [Fintype β] [DecidableEq β] (g : β → β),
        Matrix.trace (mapMatrix g ^ 1) ≠ Matrix.trace ((!![-1] : Matrix (Fin 1) (Fin 1) ℚ) ^ 1) := by
  refine ⟨by simp [Matrix.trace], fun β _ _ g h => ?_⟩
  rw [trace_pow_mapMatrix] at h
  have h1 : Matrix.trace ((!![-1] : Matrix (Fin 1) (Fin 1) ℚ) ^ 1) = -1 := by simp [Matrix.trace]
  rw [h1] at h
  have : (0 : ℚ) ≤ ((univ.filter fun x => g^[1] x = x).card : ℚ) := by positivity
  linarith

section Audit
#print axioms HasLogDeriv.unique
#print axioms cycleFactor_logDeriv
#print axioms card_minimalPeriod_eq
#print axioms periodic_count
#print axioms trace_pow_eq_primitive
#print axioms primitive_count_moebius
#print axioms transfer_determinant_euler_product
#print axioms zeta_euler_product
#print axioms signed_map_has_no_primitive_cycles
end Audit

end Holonics.Compression.Landmark.PrimitiveCycle
