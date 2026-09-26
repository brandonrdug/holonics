import Holonics.Transport.NavigatorTraceFaces
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# The dynamical zeta of the epoch return map

[definition] Aeon record A8, Lean obligation 5. A finite **return map** is a square matrix `M`,
and `N_n = tr(Mⁿ)` is its cycle count of `n` epochs. For the `0/1` matrix of a map `f` of a finite
set of occurrences, `tr(M_fⁿ) = #{x | fⁿ x = x}` counts the cycles of `n` epochs exactly
(`trace_pow_mapMatrix`); for a matrix of natural numbers, `M i k` parallel restrictions from `i` to
`k`, the words of depth `n` from `i` to `j` are `(Mⁿ)ᵢⱼ` many (`card_returnWord`), so `tr(Mⁿ)`
counts the closed words of `n` epochs. Its **transfer determinant** is Mathlib's
`charpolyRev M = det(1 − T·M)`, the face `Transport/NavigatorTraceFaces` conserves. Its
**dynamical zeta** is `ζ(T) = 1/det(1 − T·M)`, and its **cycle series** is
`cycleLog M = Σ_(n≥1) N_n Tⁿ/n` (`cycleLog`).

[proved-derived; formal-checked] What is proved.

1. **Jacobi's formula** for a matrix of polynomials (`derivative_det`), and for the transfer
   matrix: `d/dT det(1 − T·M) = −tr(adj(1 − T·M) · M)` (`derivative_charpolyRev`).
2. **The resolvent series.** `(1 − T·M) · Σ_k Tᵏ Mᵏ = 1` in power series
   (`transfer_mul_resolventSeries`), so `adj(1 − T·M) = det(1 − T·M) · Σ_k Tᵏ Mᵏ`
   (`adjugate_transfer`).
3. **The logarithmic derivative of the transfer determinant is the cycle count series**, over
   every commutative ring and with no division (Newton's identities):
   `d/dT det(1 − T·M) = −det(1 − T·M) · Σ_k tr(Mᵏ⁺¹) Tᵏ` (`transferDet_derivative`), i.e.
   `T ζ'/ζ = Σ_(n≥1) N_n Tⁿ`.
4. **The dynamical zeta is the exponential of the cycle series** over `ℚ`:
   `exp(Σ_(n≥1) tr(Mⁿ) Tⁿ/n) · det(1 − T·M) = 1` as formal power series (`zeta_eq_exp`), using
   Mathlib's substitution into `PowerSeries.exp`.
5. **Joined to the machine's trace faces.** For the machine of rotation–dilation sites,
   `det(1 − T·M) = ∏_g (1 − a_g T + q_g T²)` (`machine_charpolyRev`, from
   `NavigatorTraceFaces.machine_factor_of_companions`), its cycle counts are the sums of the site
   trace sequences `N_n = Σ_g t_n(a_g, q_g)` (`machine_cycle_count`, from
   `NavigatorTraceFaces.machine_trace_sequence` and
   `LocalFactor.theCompanionPowersCarryTheSequence`), and so `exp(Σ_n N_n Tⁿ/n) · ∏_g (1 − a_g T + q_g T²) = 1` (`machine_zeta`): the machine's
   conserved transfer determinant **is** the reciprocal of its dynamical zeta.
6. **Growth of the cycle counts.** For a nonnegative return map with a positive eigenvector
   `M v = ρ v` (a Perron vector), `0 ≤ N_n ≤ d · ρⁿ` exactly (`cycle_count_le_perron`): the cycle
   counts grow at most at rate `log ρ`, so `ζ` has no pole in `|T| < 1/ρ`. For a rotation site
   the existing bound `t_n² ≤ 4 qⁿ` (`TraceSequence.theLevelOneBoundGivesEveryLevel`) is the same
   statement at `ρ = √q`.
7. **The words of a return map.** A return map of natural numbers presents a navigator whose words
   (`ReturnWord`: a first restriction followed by a word) are its epochs. The words of depth `n`
   from `i` to `j` are `(Mⁿ)ᵢⱼ` many (`card_returnWord`); a weighted sum over the words from a
   start set `S` is `1_Sᵀ Mⁿ b` (`sum_returnWord`); all of them are `1ᵀ Mⁿ 1` (`wordCount`). The
   one-state map `[a]` has `det(1 − T·[a]) = 1 − a T` (`charpolyRev_oneState`, read at a point by
   `eval_charpolyRev` and `eval_charpolyRev_oneState`), powers `[aⁿ]` (`oneState_pow_apply`) and
   `aⁿ` words (`wordCount_oneState`), as many as the addresses `Fin n → Fin N` when `a = N`
   (`card_returnWord_oneState`); on one state every word is a cycle (`oneState_trace_pow`).
   **The transfer determinant times the word series is a polynomial** as formal power series,
   `det(1 − T·M) · Σ_n (aᵀ Mⁿ b) Tⁿ = aᵀ adj(1 − T·M) b` (`transferDet_mul_wordSeries`, from
   `adjugate_transfer`). `Foundation/FractalString` reads these laws in the scale chart `T = r^s`.

[counterexample; formal-checked] **Nonnegativity is load-bearing for the growth bound**
(`signed_return_map_exceeds_bound`): `[[3,−2],[−2,3]]` has the positive eigenvector `(1,1)` with
`ρ = 1`, yet `tr M = 6 > 2 · 1`. Trace faces are not a complete action certificate
(`NavigatorTraceFaces.identityTwo_and_unipotentTwo_are_separated_by_source_receiver`), so the
zeta is a face of the return map, not the map.

[open] Owed in #62: the equality `h = log ρ(M) = limsup (1/n) log N_n` for nonnegative `M`, the
radius of convergence of `ζ` and the location of its first pole at `T = e^(−h)` need the
Perron–Frobenius theorem (existence of the Perron vector at the spectral radius, and a lower bound
on `N_n`), which Mathlib does not carry; only the upper bound is proved here. The flow zeta `∏_c (1 − e^(−s·t(c)))⁻¹` and the trace formula
are not treated. [proved-standard, not proved here] Where the word series converges at a point `T`
it is the polynomial `aᵀ adj(1 − T·M) b` over `det(1 − T·M)`, so the poles of its continuation lie
among the zeros of the transfer determinant; this analytic statement, and its reading at
`T = r^s` in `Foundation/FractalString`, is owed in #62.

No `axiom`, no `sorry`.
-/

noncomputable section

namespace Holonics.Aeon.Production.Zeta

open Polynomial Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-! ## 1. Jacobi's formula -/

section Jacobi

variable {R : Type*} [CommRing R]

/-- [proved-derived; formal-checked] **Jacobi's formula.** The derivative of a determinant of
polynomials is the sum over columns of the determinant with that column differentiated. -/
theorem derivative_det (A : Matrix n n R[X]) :
    derivative A.det = ∑ j, (A.updateCol j (fun i => derivative (A i j))).det := by
  simp only [det_apply]
  rw [map_sum, sum_comm]
  refine sum_congr rfl fun σ _ => ?_
  rw [Units.smul_def, map_zsmul, derivative_prod_finset, smul_sum]
  refine sum_congr rfl fun j _ => ?_
  rw [Units.smul_def]
  congr 1
  rw [← mul_prod_erase univ _ (mem_univ j)]
  simp only [updateCol_apply, ite_true]
  rw [mul_comm]
  congr 1
  exact prod_congr rfl fun i hi => by rw [if_neg (ne_of_mem_erase hi)]

/-- [proved-derived; formal-checked] **Jacobi's formula for the transfer matrix:**
`d/dT det(1 − T·M) = −tr(adj(1 − T·M) · M)`. -/
theorem derivative_charpolyRev (M : Matrix n n R) :
    derivative M.charpolyRev = -trace (adjugate (1 - (X : R[X]) • M.map C) * M.map C) := by
  rw [charpolyRev, derivative_det]
  have hcol : ∀ j, (fun i => derivative ((1 - (X : R[X]) • M.map C) i j)) =
      -(fun i => C (M i j)) := by
    intro j; funext i
    simp only [Matrix.sub_apply, one_apply, Matrix.smul_apply, map_apply, smul_eq_mul,
      Pi.neg_apply]
    split_ifs <;> simp
  simp_rw [hcol, ← cramer_apply, cramer_eq_adjugate_mulVec]
  simp only [trace, Matrix.diag, Matrix.mul_apply, mulVec, dotProduct, map_apply, Pi.neg_apply,
    mul_neg, sum_neg_distrib]

end Jacobi

/-! ## 2. The resolvent series and the logarithmic derivative -/

section Resolvent

variable {R : Type*} [CommRing R]

/-- [definition] The resolvent series `Σ_k Tᵏ Mᵏ`, entrywise. -/
def resolventSeries (M : Matrix n n R) : Matrix n n (PowerSeries R) :=
  fun i j => PowerSeries.mk fun k => (M ^ k) i j

theorem coeff_mul_resolventSeries (M : Matrix n n R) (i j : n) (k : ℕ) :
    PowerSeries.coeff k ((M.map PowerSeries.C * resolventSeries M) i j) = (M ^ (k + 1)) i j := by
  rw [pow_succ', Matrix.mul_apply, Matrix.mul_apply, map_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [map_apply, PowerSeries.coeff_C_mul, resolventSeries, PowerSeries.coeff_mk]

theorem coeff_resolventSeries_mul (M : Matrix n n R) (i j : n) (k : ℕ) :
    PowerSeries.coeff k ((resolventSeries M * M.map PowerSeries.C) i j) = (M ^ (k + 1)) i j := by
  rw [pow_succ, Matrix.mul_apply, Matrix.mul_apply, map_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [map_apply, mul_comm, PowerSeries.coeff_C_mul, resolventSeries, PowerSeries.coeff_mk,
    mul_comm]

/-- [proved-derived; formal-checked] `(1 − T·M) · Σ_k Tᵏ Mᵏ = 1`. -/
theorem transfer_mul_resolventSeries (M : Matrix n n R) :
    (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C) * resolventSeries M = 1 := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.smul_mul]
  ext i j k
  rw [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, map_sub]
  rcases k with _ | k
  · simp [resolventSeries, one_apply]
  · rw [PowerSeries.coeff_succ_X_mul, coeff_mul_resolventSeries, resolventSeries,
      PowerSeries.coeff_mk, sub_self, one_apply]
    split_ifs <;> simp

theorem map_transfer (M : Matrix n n R) :
    (Polynomial.coeToPowerSeries.ringHom (R := R)).mapMatrix (1 - (X : R[X]) • M.map C) =
      1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C := by
  ext i j : 1
  simp only [RingHom.mapMatrix_apply, map_apply, Matrix.sub_apply, one_apply, Matrix.smul_apply,
    smul_eq_mul]
  split_ifs <;> simp [Polynomial.coeToPowerSeries.ringHom_apply] <;> ring

/-- [proved-derived; formal-checked] The transfer determinant as a power series. -/
theorem coe_charpolyRev (M : Matrix n n R) :
    (M.charpolyRev : PowerSeries R) =
      (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C).det := by
  rw [← map_transfer, ← RingHom.map_det, charpolyRev, Polynomial.coeToPowerSeries.ringHom_apply]

/-- [proved-derived; formal-checked] `adj(1 − T·M) = det(1 − T·M) · Σ_k Tᵏ Mᵏ`. -/
theorem adjugate_transfer (M : Matrix n n R) :
    adjugate (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C) =
      (1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C).det • resolventSeries M := by
  set A := 1 - (PowerSeries.X : PowerSeries R) • M.map PowerSeries.C
  calc adjugate A = adjugate A * (A * resolventSeries M) := by
        rw [transfer_mul_resolventSeries, Matrix.mul_one]
    _ = (adjugate A * A) * resolventSeries M := by rw [Matrix.mul_assoc]
    _ = A.det • resolventSeries M := by rw [adjugate_mul, Matrix.smul_mul, Matrix.one_mul]

/-- [proved-derived; formal-checked] `tr(Σ_k Tᵏ Mᵏ · M) = Σ_k tr(Mᵏ⁺¹) Tᵏ`. -/
theorem trace_resolventSeries_mul (M : Matrix n n R) :
    trace (resolventSeries M * M.map PowerSeries.C) =
      PowerSeries.mk fun k => trace (M ^ (k + 1)) := by
  ext k
  rw [PowerSeries.coeff_mk, trace, trace, map_sum]
  exact sum_congr rfl fun i _ => coeff_resolventSeries_mul M i i k

/-- [proved-derived; formal-checked] **The logarithmic derivative of the transfer determinant is
the cycle count series** (Newton's identities), over every commutative ring:
`d/dT det(1 − T·M) = −det(1 − T·M) · Σ_k tr(Mᵏ⁺¹) Tᵏ`. -/
theorem transferDet_derivative (M : Matrix n n R) :
    PowerSeries.derivative R (M.charpolyRev : PowerSeries R) =
      -(M.charpolyRev : PowerSeries R) * PowerSeries.mk (fun k => trace (M ^ (k + 1))) := by
  set ι := Polynomial.coeToPowerSeries.ringHom (R := R)
  have hMc : (M.map Polynomial.C).map ι = M.map PowerSeries.C := by
    ext i j : 1; simp [ι, Polynomial.coeToPowerSeries.ringHom_apply]
  rw [PowerSeries.derivative_coe, derivative_charpolyRev,
    ← Polynomial.coeToPowerSeries.ringHom_apply, map_neg, AddMonoidHom.map_trace,
    ← RingHom.mapMatrix_apply, map_mul, RingHom.map_adjugate, map_transfer,
    RingHom.mapMatrix_apply, hMc, adjugate_transfer, Matrix.smul_mul, trace_smul,
    trace_resolventSeries_mul, coe_charpolyRev, smul_eq_mul, neg_mul]

end Resolvent

/-! ## 3. The zeta is the exponential of the cycle series -/

/-- [definition] The cycle series `Σ_(n≥1) tr(Mⁿ) Tⁿ/n`. -/
def cycleLog (M : Matrix n n ℚ) : PowerSeries ℚ :=
  PowerSeries.mk fun k => if k = 0 then 0 else trace (M ^ k) / k

/-- [proved-derived; formal-checked] **The dynamical zeta.**
`exp(Σ_(n≥1) tr(Mⁿ) Tⁿ/n) · det(1 − T·M) = 1` as formal power series over `ℚ`:
`ζ(T) = 1/det(1 − T·M) = exp Σ_n N_n Tⁿ/n`. -/
theorem zeta_eq_exp (M : Matrix n n ℚ) :
    (PowerSeries.exp ℚ).subst (cycleLog M) * (M.charpolyRev : PowerSeries ℚ) = 1 := by
  have hL0 : PowerSeries.constantCoeff (cycleLog M) = 0 := by
    simp [cycleLog, PowerSeries.constantCoeff_mk]
  have hL : PowerSeries.HasSubst (cycleLog M) := PowerSeries.HasSubst.of_constantCoeff_zero' hL0
  have hLd : PowerSeries.derivative ℚ (cycleLog M) =
      PowerSeries.mk fun k => trace (M ^ (k + 1)) := by
    ext k
    rw [PowerSeries.coeff_derivative, cycleLog, PowerSeries.coeff_mk, PowerSeries.coeff_mk,
      if_neg (Nat.succ_ne_zero k)]
    push_cast
    field_simp
  set F := (PowerSeries.exp ℚ).subst (cycleLog M) with hF
  have hFd : PowerSeries.derivative ℚ F = F * PowerSeries.derivative ℚ (cycleLog M) := by
    rw [hF, PowerSeries.derivative_subst hL, PowerSeries.derivative_exp]
  have hF0 : PowerSeries.constantCoeff F = 1 := by
    have h := PowerSeries.constantCoeff_subst (R := ℚ) hL (PowerSeries.exp ℚ)
    change PowerSeries.constantCoeff F = _ at h
    rw [h, finsum_eq_single _ 0]
    · simp
    · intro d hd
      rw [map_pow]
      change _ • (PowerSeries.constantCoeff (cycleLog M)) ^ d = 0
      rw [hL0, zero_pow hd, smul_zero]
  apply PowerSeries.derivative.ext
  · rw [Derivation.leibniz, hFd, hLd, transferDet_derivative, smul_eq_mul, smul_eq_mul,
      PowerSeries.derivative_one]
    ring
  · rw [map_mul, hF0, map_one, one_mul, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
      Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]

/-! ## 4. Joined to the machine's trace faces -/

section Machine

open Holonics.Transport.NavigatorTraceFaces Holonics.Geometry.LocalFactor

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

/-- [definition] The machine of rotation–dilation sites: block-diagonal companions. -/
def machine {R : Type*} [CommRing R] (a q : σ → R) : Matrix (Fin 2 × σ) (Fin 2 × σ) R :=
  blockDiagonal fun g => companion (a g) (q g)

omit [Fintype σ] in
theorem companion_map {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (a q : R) :
    (companion a q).map f = companion (f a) (f q) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [companion]

/-- [proved-derived; formal-checked] **The machine's transfer determinant is the product of the
site factors**, as a polynomial in `T`. -/
theorem machine_charpolyRev {R : Type*} [CommRing R] (a q : σ → R) :
    (machine a q).charpolyRev = ∏ g, (1 - C (a g) * X + C (q g) * X ^ 2) := by
  have hmap : (machine a q).map C = machine (fun g => C (a g)) (fun g => C (q g)) := by
    rw [machine, blockDiagonal_map _ _ (map_zero C)]
    simp only [companion_map]
    rfl
  rw [charpolyRev, hmap, machine, machine_factor_of_companions]

/-- [proved-derived; formal-checked] **The machine's cycle counts are the site trace
sequences:** `N_n = tr(Mⁿ) = Σ_g t_n(a_g, q_g)`. -/
theorem machine_cycle_count (a q : σ → ℤ) (k : ℕ) :
    trace (machine a q ^ k) = ∑ g, Holonics.Geometry.TraceSequence.trace (a g) (q g) k := by
  rw [machine, machine_trace_sequence]
  exact sum_congr rfl fun g _ => theCompanionPowersCarryTheSequence (a g) (q g) k

/-- [proved-derived; formal-checked] **The machine's conserved transfer determinant is the
reciprocal of its dynamical zeta:** `exp(Σ_n N_n Tⁿ/n) · ∏_g (1 − a_g T + q_g T²) = 1`. -/
theorem machine_zeta (a q : σ → ℚ) :
    (PowerSeries.exp ℚ).subst (cycleLog (machine a q)) *
        ((∏ g, (1 - C (a g) * X + C (q g) * X ^ 2) : ℚ[X]) : PowerSeries ℚ) = 1 := by
  rw [← machine_charpolyRev]
  exact zeta_eq_exp _

end Machine

/-! ## 5. Growth of the cycle counts -/

section Growth

/-- [proved-derived; formal-checked] **Cycle counts grow at most at the Perron rate.** For a
nonnegative return map with a positive eigenvector `M v = ρ v`, `0 ≤ tr(Mᵏ) ≤ d · ρᵏ`. -/
theorem cycle_count_le_perron {M : Matrix n n ℚ} (hM : ∀ i j, 0 ≤ M i j) {v : n → ℚ}
    (hv : ∀ i, 0 < v i) {ρ : ℚ} (heig : M *ᵥ v = ρ • v) (k : ℕ) :
    0 ≤ trace (M ^ k) ∧ trace (M ^ k) ≤ Fintype.card n * ρ ^ k := by
  have hpow : ∀ k, (M ^ k) *ᵥ v = ρ ^ k • v := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, heig, smul_smul, pow_succ,
        mul_comm]
  have hnonneg : ∀ k i j, 0 ≤ (M ^ k) i j := by
    intro k
    induction k with
    | zero => intro i j; rw [pow_zero, one_apply]; split_ifs <;> norm_num
    | succ k ih =>
      intro i j; rw [pow_succ, Matrix.mul_apply]
      exact sum_nonneg fun l _ => mul_nonneg (ih i l) (hM l j)
  have hdiag : ∀ i, (M ^ k) i i ≤ ρ ^ k := by
    intro i
    have hrow : ((M ^ k) *ᵥ v) i = ρ ^ k * v i := by rw [hpow k]; simp
    have hle : (M ^ k) i i * v i ≤ ((M ^ k) *ᵥ v) i := by
      rw [mulVec, dotProduct]
      exact single_le_sum (f := fun j => (M ^ k) i j * v j)
        (fun j _ => mul_nonneg (hnonneg k i j) (hv j).le) (mem_univ i)
    rw [hrow] at hle
    exact le_of_mul_le_mul_right hle (hv i)
  refine ⟨sum_nonneg fun i _ => hnonneg k i i, ?_⟩
  calc trace (M ^ k) = ∑ i, (M ^ k) i i := rfl
    _ ≤ ∑ _i : n, ρ ^ k := sum_le_sum fun i _ => hdiag i
    _ = Fintype.card n * ρ ^ k := by rw [sum_const, card_univ, nsmul_eq_mul]

/-- [definition] The `0/1` matrix of a map of occurrences: `M_f x y = 1` exactly when `f x = y`. -/
def mapMatrix (f : n → n) : Matrix n n ℚ := fun x y => if f x = y then 1 else 0

/-- [proved-derived; formal-checked] Its powers are the matrices of the iterates:
`(M_fᵏ) x y = [fᵏ x = y]`. -/
theorem mapMatrix_pow_apply (f : n → n) (k : ℕ) (x y : n) :
    (mapMatrix f ^ k) x y = if f^[k] x = y then 1 else 0 := by
  induction k generalizing x with
  | zero =>
    simp only [pow_zero, one_apply, Function.iterate_zero, id]
    congr
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply, Function.iterate_succ_apply]
    simp only [mapMatrix, ite_mul, one_mul, zero_mul, sum_ite_eq, mem_univ, if_true]
    exact ih (f x)

/-- [proved-derived; formal-checked] **The cycle count of a map is its number of periodic points**:
`tr(M_fᵏ) = #{x | fᵏ x = x}`. -/
theorem trace_pow_mapMatrix (f : n → n) (k : ℕ) :
    trace (mapMatrix f ^ k) = (#(univ.filter fun x => f^[k] x = x) : ℚ) := by
  simp only [trace, diag_apply, mapMatrix_pow_apply]
  rw [sum_boole]

/-- [definition] A signed return map with a positive eigenvector. -/
def signedMap : Matrix (Fin 2) (Fin 2) ℚ := !![3, -2; -2, 3]

/-- [counterexample; formal-checked] **Nonnegativity is load-bearing.** `[[3,−2],[−2,3]]` fixes the
positive vector `(1,1)` (`ρ = 1`) but `tr M = 6 > 2 · 1`. -/
theorem signed_return_map_exceeds_bound :
    signedMap *ᵥ ![1, 1] = (1 : ℚ) • ![1, 1] ∧ (2 : ℚ) * 1 ^ 1 < trace (signedMap ^ 1) := by
  refine ⟨?_, ?_⟩
  · ext i; fin_cases i <;> simp [signedMap, mulVec, dotProduct, Fin.sum_univ_two] <;> norm_num
  · simp [signedMap, trace, Fin.sum_univ_two]; norm_num

end Growth

/-! ## 6. The words of a return map

A return map `M` of natural numbers counts the parallel restrictions `M i k` from the state `i` to
the state `k`; its words are the epochs of the navigator it presents. The laws here hold for every
return map; `Foundation/FractalString` reads them in the scale chart `T = r^s`. -/

section Words

universe u

variable {σ : Type u} [Fintype σ] [DecidableEq σ]

/-- [definition] **A word of a return map**: `n` restrictions from state `i` to state `j`, where
`M i k` counts the parallel restrictions from `i` to `k`. The empty word stays at its state; a
longer word is a first restriction followed by a word. The words are the epochs of the navigator
the return map presents. -/
def ReturnWord (M : Matrix σ σ ℕ) : ℕ → σ → σ → Type u
  | 0, i, j => {_u : PUnit.{u + 1} // i = j}
  | n + 1, i, j => Σ k : σ, Fin (M i k) × ReturnWord M n k j

/-- [definition] There are finitely many words at every depth. -/
instance instFintypeReturnWord (M : Matrix σ σ ℕ) :
    (n : ℕ) → (i j : σ) → Fintype (ReturnWord M n i j)
  | 0, i, j => inferInstanceAs (Fintype {_u : PUnit.{u + 1} // i = j})
  | n + 1, i, j =>
      letI : ∀ k, Fintype (ReturnWord M n k j) := fun k => instFintypeReturnWord M n k j
      inferInstanceAs (Fintype (Σ k : σ, Fin (M i k) × ReturnWord M n k j))

/-- [proved-derived; formal-checked] **The return map counts the words**: the words of depth `n`
from `i` to `j` are `(Mⁿ)ᵢⱼ` many. This is the walk-count reading of the powers, so the cycle
count `tr(Mⁿ)` counts the closed words of `n` epochs. -/
theorem card_returnWord (M : Matrix σ σ ℕ) (n : ℕ) (i j : σ) :
    Fintype.card (ReturnWord M n i j) = (M ^ n) i j := by
  induction n generalizing i j with
  | zero =>
      rw [pow_zero, Matrix.one_apply]
      change Fintype.card {_u : PUnit.{u + 1} // i = j} = _
      by_cases h : i = j
      · subst h; simp
      · rw [if_neg h, Fintype.card_eq_zero_iff]
        exact ⟨fun w => h w.2⟩
  | succ n ih =>
      rw [pow_succ', Matrix.mul_apply]
      change Fintype.card (Σ k : σ, Fin (M i k) × ReturnWord M n k j) = _
      rw [Fintype.card_sigma]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Fintype.card_prod, Fintype.card_fin, ih]

/-- [proved-derived; formal-checked] **The words from a start set are counted by `1_Sᵀ Mⁿ`.** A
sum over the words of depth `n` from the start set `S` of end weights `b` is `1_Sᵀ Mⁿ b`; with
`b = 1` it is the word count from `S`. -/
theorem sum_returnWord {A : Type*} [CommSemiring A] (M : Matrix σ σ ℕ) (S : Finset σ)
    (b : σ → A) (n : ℕ) :
    ∑ i ∈ S, ∑ j, ∑ _w : ReturnWord M n i j, b j =
      ∑ i, ∑ j, (if i ∈ S then 1 else 0) * ((M.map (Nat.cast : ℕ → A)) ^ n) i j * b j := by
  have hpow : (M.map (Nat.cast : ℕ → A)) ^ n = (M ^ n).map (Nat.cast : ℕ → A) := by
    have := (RingHom.map_pow ((Nat.castRingHom A).mapMatrix (m := σ)) M n).symm
    simpa using this
  calc ∑ i ∈ S, ∑ j, ∑ _w : ReturnWord M n i j, b j
      = ∑ i ∈ S, ∑ j, ((M ^ n) i j : A) * b j := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_const, Finset.card_univ, card_returnWord, nsmul_eq_mul]
    _ = ∑ i, if i ∈ S then ∑ j, ((M ^ n) i j : A) * b j else 0 := by
        rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter]
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hpow]
        split_ifs <;> simp

/-- [definition] **The depth-`n` word count** `1ᵀ Mⁿ 1` of a navigator whose words are counted by
the return map `M`: its epochs of `n` steps from every state to every state (`card_returnWord`
counts the words themselves). The closed ones, `tr Mⁿ`, are the cycle counts. -/
def wordCount {S : Type*} [Semiring S] {τ : Type*} [Fintype τ] [DecidableEq τ]
    (M : Matrix τ τ S) (n : ℕ) : S :=
  ∑ i, ∑ j, (M ^ n) i j

end Words

section OneState

variable {R : Type*} [CommRing R]

/-- [proved-derived; formal-checked] **The one-state transfer determinant.** The return map `[a]`
of one state with weight `a` has `det(1 − T·[a]) = 1 − a T`. -/
theorem charpolyRev_oneState (a : R) :
    (!![a] : Matrix (Fin 1) (Fin 1) R).charpolyRev = 1 - C a * X := by
  rw [Matrix.charpolyRev, Matrix.det_unique]
  simp

/-- [proved-derived; formal-checked] **The transfer determinant at a point.** Reading `T` at the
value `z` gives `det(1 − z·M)`. -/
theorem eval_charpolyRev (M : Matrix n n R) (z : R) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, coe_evalRingHom]
  split_ifs <;> simp [mul_comm (M i j)]

/-- [proved-derived; formal-checked] The one-state transfer determinant at `z` is `1 − a z`. -/
theorem eval_charpolyRev_oneState (a z : R) :
    (!![a] : Matrix (Fin 1) (Fin 1) R).charpolyRev.eval z = 1 - a * z := by
  rw [charpolyRev_oneState, eval_sub, eval_one, eval_mul, eval_C, eval_X]

/-- [proved-derived; formal-checked] The powers of a one-state return map: `[a]ⁿ = [aⁿ]`. -/
theorem oneState_pow_apply {S : Type*} [Semiring S] (a : S) (k : ℕ) :
    ((!![a] : Matrix (Fin 1) (Fin 1) S) ^ k) 0 0 = a ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ, Matrix.mul_apply, Fin.sum_univ_one, ih, pow_succ]
      simp

/-- [proved-derived; formal-checked] A one-state return map `[a]` counts `aⁿ` words at depth
`n`. -/
theorem wordCount_oneState {S : Type*} [Semiring S] (a : S) (k : ℕ) :
    wordCount (!![a] : Matrix (Fin 1) (Fin 1) S) k = a ^ k := by
  simp only [wordCount, Fin.sum_univ_one]
  exact oneState_pow_apply a k

/-- [proved-derived; formal-checked] **On one state every word is a cycle**: `tr [a]ⁿ = 1ᵀ[a]ⁿ1 =
aⁿ`. For a one-state return map the cycle counts of the dynamical zeta and the word counts
coincide. -/
theorem oneState_trace_pow {S : Type*} [CommSemiring S] (a : S) (k : ℕ) :
    Matrix.trace ((!![a] : Matrix (Fin 1) (Fin 1) S) ^ k) = a ^ k ∧
      wordCount (!![a] : Matrix (Fin 1) (Fin 1) S) k = a ^ k := by
  refine ⟨?_, wordCount_oneState a k⟩
  rw [Matrix.trace, Fin.sum_univ_one, Matrix.diag_apply, oneState_pow_apply]

/-- [proved-derived; formal-checked] The words of the one-state return map `[N]` are as many as the
addresses `Fin k → Fin N` of `k` choices among `N` parallel restrictions. -/
theorem card_returnWord_oneState (N k : ℕ) :
    Fintype.card (ReturnWord (!![N] : Matrix (Fin 1) (Fin 1) ℕ) k 0 0) =
      Fintype.card (Fin k → Fin N) := by
  rw [card_returnWord, oneState_pow_apply, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]

/-- [proved-derived; formal-checked] **The transfer determinant times the word series is a
polynomial** (formal power series). For a return map `M` over a commutative ring, start weights
`a` and end weights `b`, `det(1 − T·M) · Σ_k (aᵀ Mᵏ b) Tᵏ = aᵀ adj(1 − T·M) b`: the resolvent
identity `adj(1 − T·M) = det(1 − T·M)·Σ_k Tᵏ Mᵏ` (`adjugate_transfer`) paired with `a` and `b`.
[proved-standard, not proved here] Where the series converges at a point `T` it equals that
polynomial over the transfer determinant, so the poles of its continuation lie among the zeros of
`det(1 − T·M)`; the analytic statement is owed in #62. -/
theorem transferDet_mul_wordSeries (M : Matrix n n R) (a b : n → R) :
    (M.charpolyRev : PowerSeries R) *
        PowerSeries.mk (fun k => ∑ i, ∑ j, a i * (M ^ k) i j * b j) =
      ((∑ i, ∑ j, C (a i) * (1 - (X : R[X]) • M.map C).adjugate i j * C (b j) : R[X]) :
        PowerSeries R) := by
  have hadj : ∀ i j, (((1 - (X : R[X]) • M.map C).adjugate i j : R[X]) : PowerSeries R) =
      (M.charpolyRev : PowerSeries R) * resolventSeries M i j := by
    intro i j
    have hentry : (((1 - (X : R[X]) • M.map C).adjugate i j : R[X]) : PowerSeries R) =
        ((Polynomial.coeToPowerSeries.ringHom (R := R)).mapMatrix
          (1 - (X : R[X]) • M.map C).adjugate) i j := rfl
    rw [hentry, RingHom.map_adjugate, map_transfer, adjugate_transfer, ← coe_charpolyRev]
    rfl
  have hseries : PowerSeries.mk (fun k => ∑ i, ∑ j, a i * (M ^ k) i j * b j) =
      ∑ i, ∑ j, PowerSeries.C (a i) * resolventSeries M i j * PowerSeries.C (b j) := by
    ext k
    simp only [PowerSeries.coeff_mk, map_sum, PowerSeries.coeff_mul_C, PowerSeries.coeff_C_mul,
      resolventSeries]
  have hcoe : ((∑ i, ∑ j, C (a i) * (1 - (X : R[X]) • M.map C).adjugate i j * C (b j) : R[X]) :
      PowerSeries R) = ∑ i, ∑ j, PowerSeries.C (a i) *
        (((1 - (X : R[X]) • M.map C).adjugate i j : R[X]) : PowerSeries R) *
          PowerSeries.C (b j) := by
    rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, map_mul, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeToPowerSeries.ringHom_apply,
      Polynomial.coe_C, Polynomial.coe_C]
  rw [hseries, hcoe, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hadj]
  ring

end OneState

section Audit

#print axioms derivative_det
#print axioms derivative_charpolyRev
#print axioms transfer_mul_resolventSeries
#print axioms transferDet_derivative
#print axioms zeta_eq_exp
#print axioms machine_charpolyRev
#print axioms machine_cycle_count
#print axioms machine_zeta
#print axioms cycle_count_le_perron
#print axioms signed_return_map_exceeds_bound
#print axioms trace_pow_mapMatrix
#print axioms card_returnWord
#print axioms sum_returnWord
#print axioms charpolyRev_oneState
#print axioms eval_charpolyRev
#print axioms eval_charpolyRev_oneState
#print axioms oneState_pow_apply
#print axioms wordCount_oneState
#print axioms oneState_trace_pow
#print axioms card_returnWord_oneState
#print axioms transferDet_mul_wordSeries

end Audit

end Holonics.Aeon.Production.Zeta
