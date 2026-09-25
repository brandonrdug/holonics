import Holonics.Transport.GeneratorTraceFaces
import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic

/-!
# The dynamical zeta of the epoch return map

[definition] Aeon record A8, Lean obligation 5. A finite **return map** is a square matrix `M`,
and `N_n = tr(Mⁿ)` is its cycle count of `n` epochs. For the `0/1` matrix of a map `f` of a finite
set of occurrences, `tr(M_fⁿ) = #{x | fⁿ x = x}` counts the cycles of `n` epochs exactly
(`trace_pow_mapMatrix`); for a general nonnegative integer matrix the walk-count reading of
`(Mⁿ)ᵢᵢ` is the standard one and is not restated here. Its **transfer determinant** is Mathlib's
`charpolyRev M = det(1 − T·M)`, the face `Transport/GeneratorTraceFaces` conserves. Its
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
   `GeneratorTraceFaces.machine_factor_of_companions`), its cycle counts are the sums of the site
   trace sequences `N_n = Σ_g t_n(a_g, q_g)` (`machine_cycle_count`, from
   `GeneratorTraceFaces.machine_trace_sequence` and
   `LocalFactor.theCompanionPowersCarryTheSequence`), and so `exp(Σ_n N_n Tⁿ/n) · ∏_g (1 − a_g T + q_g T²) = 1` (`machine_zeta`): the machine's
   conserved transfer determinant **is** the reciprocal of its dynamical zeta.
6. **Growth of the cycle counts.** For a nonnegative return map with a positive eigenvector
   `M v = ρ v` (a Perron vector), `0 ≤ N_n ≤ d · ρⁿ` exactly (`cycle_count_le_perron`): the cycle
   counts grow at most at rate `log ρ`, so `ζ` has no pole in `|T| < 1/ρ`. For a rotation site
   the existing bound `t_n² ≤ 4 qⁿ` (`TraceSequence.theLevelOneBoundGivesEveryLevel`) is the same
   statement at `ρ = √q`.

[counterexample; formal-checked] **Nonnegativity is load-bearing for the growth bound**
(`signed_return_map_exceeds_bound`): `[[3,−2],[−2,3]]` has the positive eigenvector `(1,1)` with
`ρ = 1`, yet `tr M = 6 > 2 · 1`. Trace faces are not a complete action certificate
(`GeneratorTraceFaces.identityTwo_and_unipotentTwo_are_separated_by_source_receiver`), so the
zeta is a face of the return map, not the map.

[open] Owed in #62: the equality `h = log ρ(M) = limsup (1/n) log N_n` for nonnegative `M`, the
radius of convergence of `ζ` and the location of its first pole at `T = e^(−h)` need the
Perron–Frobenius theorem (existence of the Perron vector at the spectral radius, and a lower bound
on `N_n`), which Mathlib does not carry; only the upper bound is proved here. The flow zeta `∏_c (1 − e^(−s·t(c)))⁻¹` and the trace formula
are not treated.

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

open Holonics.Transport.GeneratorTraceFaces Holonics.Geometry.LocalFactor

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

end Audit

end Holonics.Aeon.Production.Zeta
