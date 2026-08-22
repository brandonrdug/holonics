import ElementaryHolonics.Millennium.HeckeTheta
import ElementaryHolonics.Millennium.BirchSwinnertonDyer
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import ElementaryHolonics.Millennium.HeckeEuler

/-!
# HeckeWitness: the analytic datum of the congruent-number curve at one

**The join of the construction to the pose.**  `HeckeTheta` built the completed
L-function `heckeLambda` — entire, `Λ(2−s) = Λ(s)`, central value a positive real —
from the theta function alone.  This file removes the archimedean factor and returns
the analytic half of the `LDatum` witness at `n = 1`:

* `heckeL` — the L-function itself, `L(s) = (√32/2π)^{−s}·Γ(s)⁻¹·Λ(s)`, **entire**
  because `1/Γ` is entire;
* `theCompletedProductFormulaHolds` — away from the poles of `Γ`,
  `completed 32 heckeL = heckeLambda`: the pose's product chart agrees with the
  constructed completed function exactly where that chart is lawful;
* `theWitnessFunctionalEquation` — `Λ(2−s) = Λ(s)`: sign `+1` at one, as the parity
  ledger demands;
* `theLFunctionCentralValueIsPositive` / `theLFunctionDoesNotVanishAtOne` —
  `L(1) = (2π/√32)·Λ(1) > 0`: **the analytic side of rank zero at one**, matching the
  completed descent (`RankZero`: exactly four points; one is not a congruent number).

**Boundary**: the arithmetic half of the witness — the identification of `heckeCoeff`
with the point counts (`coeff_prime`), its multiplicativity and Euler recursion, and
the `LSeries` agreement — is the Gaussian-integer/Jacobi-sum arithmetic and remains
the named open face.  Every theorem here is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HeckeWitness

open Real Complex
open Soma.Holonics.Millennium.HeckeTheta
open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.GaussCoefficient

/-- The L-function of the congruent-number curve at one: the completed function with
its archimedean factor removed.  Entire, because `1/Γ` is entire. -/
def heckeL (s : ℂ) : ℂ :=
  ((Real.sqrt 32 : ℂ) / (2 * Real.pi)) ^ (-s) * (Complex.Gamma s)⁻¹ * heckeLambda s

private lemma base_ne_zero : ((Real.sqrt 32 : ℂ) / (2 * Real.pi)) ≠ 0 := by
  apply div_ne_zero
  · simp only [ne_eq, Complex.ofReal_eq_zero]
    have : (0 : ℝ) < Real.sqrt 32 := Real.sqrt_pos.mpr (by norm_num)
    exact ne_of_gt this
  · simp only [ne_eq, mul_eq_zero, not_or]
    constructor
    · norm_num
    · simp only [Complex.ofReal_eq_zero]
      exact Real.pi_ne_zero

/-- **The L-function is entire.** -/
theorem theLFunctionIsEntire : Differentiable ℂ heckeL := by
  apply Differentiable.mul
  · apply Differentiable.mul
    · exact fun s => (differentiableAt_id.neg.const_cpow (Or.inl base_ne_zero))
    · exact Complex.differentiable_one_div_Gamma
  · exact theCompletedLFunctionIsEntire

/-- **The product chart agrees with the constructed completed function** wherever the
chart is lawful — away from the poles of `Γ`. -/
theorem theCompletedProductFormulaHolds (s : ℂ) (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    completed 32 heckeL s = heckeLambda s := by
  unfold completed heckeL
  have hG : Complex.Gamma s ≠ 0 := Complex.Gamma_ne_zero (by exact_mod_cast hs)
  have hb : ((Real.sqrt ((32 : ℕ) : ℝ) : ℂ) / (2 * Real.pi)) ≠ 0 := by
    push_cast
    exact base_ne_zero
  have hpow : ((Real.sqrt ((32 : ℕ) : ℝ) : ℂ) / (2 * Real.pi)) ^ s ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hb]
    exact Complex.exp_ne_zero _
  rw [Complex.cpow_neg]
  field_simp
  norm_num

/-- **The functional equation of the witness**: sign `+1` at one. -/
theorem theWitnessFunctionalEquation (s : ℂ) : heckeLambda (2 - s) = heckeLambda s :=
  theCompletedLFunctionalEquation s

/-- **The central value of the L-function is a positive real**:
`L(1) = (2π/√32)·Λ(1)` with `Λ(1)` the integral of the positive theta. -/
theorem theLFunctionCentralValueIsPositive : ∃ r : ℝ, 0 < r ∧ heckeL 1 = (r : ℂ) := by
  obtain ⟨t, ht, hEq⟩ := theCentralValueIsThePositiveThetaIntegral
  refine ⟨2 * Real.pi / Real.sqrt 32 * t, ?_, ?_⟩
  · have h32 : (0 : ℝ) < Real.sqrt 32 := Real.sqrt_pos.mpr (by norm_num)
    have := Real.pi_pos
    positivity
  · unfold heckeL
    rw [hEq, Complex.Gamma_one, inv_one, mul_one, Complex.cpow_neg, Complex.cpow_one, inv_div]
    push_cast
    ring

/-- **The L-function does not vanish at the center** — the analytic side of rank zero
at one. -/
theorem theLFunctionDoesNotVanishAtOne : heckeL 1 ≠ 0 := by
  obtain ⟨r, hr, hEq⟩ := theLFunctionCentralValueIsPositive
  rw [hEq]
  exact_mod_cast hr.ne'

/-! ## The Dirichlet series agreement

`hasSum_mellin` converts the theta's Dirichlet expansion into the L-function's
Dirichlet series; the conductor `32` is exactly the normalization that cancels the
scale: `(√32/2π)·(π/(2√2)) = 1`. -/

private lemma sqrt2_pos' : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

private lemma sqrt32_eq : Real.sqrt 32 = 4 * Real.sqrt 2 := by
  rw [show (32 : ℝ) = 4 ^ 2 * 2 from by norm_num, Real.sqrt_mul (by positivity),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 4)]

private lemma scale_pos : (0 : ℝ) < π / (2 * Real.sqrt 2) := by
  have h1 := Real.pi_pos
  have h2 := sqrt2_pos'
  positivity

/-- The theta's Dirichlet expansion, in the exponential form `hasSum_mellin` reads. -/
private lemma theta_hasSum_exp {t : ℝ} (ht : t ∈ Set.Ioi (0 : ℝ)) :
    HasSum (fun m : ℕ => ((heckeCoeff m : ℤ) : ℂ) *
      rexp (-(π / (2 * Real.sqrt 2) * m) * t)) ((heckeTheta t : ℝ) : ℂ) := by
  have h := theHeckeThetaIsItsDirichletSeries (Set.mem_Ioi.mp ht)
  have hfun : (fun m : ℕ => ((heckeCoeff m : ℤ) : ℂ) *
      ((rexp (-2 * π * (t / (4 * Real.sqrt 2)) * (m : ℝ)) : ℝ) : ℂ))
      = fun m : ℕ => ((heckeCoeff m : ℤ) : ℂ) * rexp (-(π / (2 * Real.sqrt 2) * m) * t) := by
    funext m
    congr 2
    have hs := sqrt2_pos'
    field_simp
    ring
  rwa [hfun] at h

/-- The summability input: the crude circle bound against `re s > 3`. -/
private lemma dirichlet_summable {s : ℂ} (hs : 3 < s.re) :
    Summable fun m : ℕ => ‖((heckeCoeff m : ℤ) : ℂ)‖ / (π / (2 * Real.sqrt 2) * m) ^ s.re := by
  have hC := scale_pos
  set σ : ℝ := s.re with hσ
  set C : ℝ := π / (2 * Real.sqrt 2) with hC_def
  have hmaj : Summable fun m : ℕ => (9 / C ^ σ) * ((m : ℝ) ^ ((2 : ℝ) - σ)) := by
    apply Summable.mul_left
    rw [Real.summable_nat_rpow]
    linarith
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hmaj
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · rw [show ((heckeCoeff 0 : ℤ) : ℂ) = 0 from by rw [heckeCoeff_zero]; norm_num]
    simp only [norm_zero, Nat.cast_zero, zero_div]
    positivity
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hnorm : ‖((heckeCoeff m : ℤ) : ℂ)‖ ≤ 9 * (m : ℝ) ^ 2 := by
    rw [show ((heckeCoeff m : ℤ) : ℂ) = (((heckeCoeff m : ℤ) : ℝ) : ℂ) from by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
    have h1 := heckeCoeff_abs_le m
    have h2 : |((heckeCoeff m : ℤ) : ℝ)| ≤ ((9 * (m : ℤ) ^ 2 : ℤ) : ℝ) := by
      rw [← Int.cast_abs]
      exact_mod_cast h1
    push_cast at h2
    linarith
  have hpow : (C * m) ^ σ = C ^ σ * (m : ℝ) ^ σ :=
    Real.mul_rpow hC.le hm0.le
  have hexp : (m : ℝ) ^ ((2 : ℝ) - σ) = (m : ℝ) ^ 2 / (m : ℝ) ^ σ := by
    rw [Real.rpow_sub hm0, show ((2 : ℝ)) = ((2 : ℕ) : ℝ) from by norm_num,
      Real.rpow_natCast]
  rw [hpow, hexp, show 9 / C ^ σ * ((m : ℝ) ^ 2 / (m : ℝ) ^ σ)
      = 9 * (m : ℝ) ^ 2 / (C ^ σ * (m : ℝ) ^ σ) from div_mul_div_comm 9 (C ^ σ) _ _]
  gcongr

/-- **The L-function agrees with the Dirichlet series of its coefficients** on the
half-plane `re s > 3`. -/
theorem theLFunctionAgreesWithItsDirichletSeries {s : ℂ} (hs : 3 < s.re) :
    heckeL s = LSeries (fun m => ((heckeCoeff m : ℤ) : ℂ)) s := by
  have hs0 : 0 < s.re := by linarith
  have hC := scale_pos
  have hmel : HasSum (fun m : ℕ => Complex.Gamma s * ((heckeCoeff m : ℤ) : ℂ) /
      ((π / (2 * Real.sqrt 2) * m : ℝ) : ℂ) ^ s)
      (mellin (Complex.ofReal ∘ heckeTheta) s) := by
    refine hasSum_mellin (fun m => ?_) hs0 (fun t ht => theta_hasSum_exp ht)
      (dirichlet_summable hs)
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · left
      rw [heckeCoeff_zero]
      norm_num
    · right
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      positivity
  have hΛ : mellin (Complex.ofReal ∘ heckeTheta) s = heckeLambda s :=
    (theCompletedLFunctionHasMellin s).2
  rw [hΛ] at hmel
  have hG : Complex.Gamma s ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.neg_re, Complex.natCast_re] at hre
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have htsum : heckeLambda s = Complex.Gamma s *
      ∑' m : ℕ, ((heckeCoeff m : ℤ) : ℂ) / ((π / (2 * Real.sqrt 2) * m : ℝ) : ℂ) ^ s := by
    rw [← tsum_mul_left, ← hmel.tsum_eq]
    exact tsum_congr fun m => by ring
  have hterm : ∀ m : ℕ, ((heckeCoeff m : ℤ) : ℂ) / ((π / (2 * Real.sqrt 2) * m : ℝ) : ℂ) ^ s
      = ((((π / (2 * Real.sqrt 2) : ℝ)) : ℂ) ^ s)⁻¹ *
          LSeries.term (fun m => ((heckeCoeff m : ℤ) : ℂ)) s m := by
    intro m
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · rw [LSeries.term_zero, heckeCoeff_zero]
      norm_num
    · rw [LSeries.term_of_ne_zero (by omega : m ≠ 0)]
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      have hsplit : ((π / (2 * Real.sqrt 2) * m : ℝ) : ℂ) ^ s
          = ((π / (2 * Real.sqrt 2) : ℝ) : ℂ) ^ s * ((m : ℝ) : ℂ) ^ s := by
        rw [Complex.ofReal_mul]
        exact Complex.mul_cpow_ofReal_nonneg hC.le hm0.le s
      rw [hsplit]
      have hCs : ((π / (2 * Real.sqrt 2) : ℝ) : ℂ) ^ s ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hC.ne')]
        exact Complex.exp_ne_zero _
      have hms : ((m : ℝ) : ℂ) ^ s ≠ 0 := by
        rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hm0.ne')]
        exact Complex.exp_ne_zero _
      rw [show (((m : ℝ) : ℂ)) = ((m : ℕ) : ℂ) from by push_cast; rfl] at hsplit hms ⊢
      field_simp
  have hfinal : heckeLambda s = Complex.Gamma s *
      (((((π / (2 * Real.sqrt 2) : ℝ)) : ℂ) ^ s)⁻¹ *
        LSeries (fun m => ((heckeCoeff m : ℤ) : ℂ)) s) := by
    rw [htsum, tsum_congr hterm, tsum_mul_left]
    rfl
  have hb0 : (0 : ℝ) < Real.sqrt 32 / (2 * π) := by
    have h1 := Real.pi_pos
    have h2 : (0 : ℝ) < Real.sqrt 32 := Real.sqrt_pos.mpr (by norm_num)
    positivity
  have hbase : ((Real.sqrt 32 : ℂ) / (2 * Real.pi)) = (((Real.sqrt 32 / (2 * π) : ℝ)) : ℂ) := by
    push_cast
    rfl
  have hcancel : (Real.sqrt 32 / (2 * π) : ℝ) * (π / (2 * Real.sqrt 2)) = 1 := by
    rw [sqrt32_eq]
    have h1 := Real.pi_pos
    have h2 := sqrt2_pos'
    field_simp
    ring
  have hkey : ((Real.sqrt 32 : ℂ) / (2 * Real.pi)) ^ (-s) *
      ((((π / (2 * Real.sqrt 2) : ℝ)) : ℂ) ^ s)⁻¹ = 1 := by
    rw [hbase, Complex.cpow_neg, ← mul_inv,
      ← Complex.mul_cpow_ofReal_nonneg hb0.le scale_pos.le, ← Complex.ofReal_mul, hcancel]
    simp
  have hGinv : (Complex.Gamma s)⁻¹ * Complex.Gamma s = 1 := inv_mul_cancel₀ hG
  unfold heckeL
  rw [hfinal]
  linear_combination (LSeries (fun m => ((heckeCoeff m : ℤ) : ℂ)) s *
      ((Complex.Gamma s)⁻¹ * Complex.Gamma s)) * hkey
    + LSeries (fun m => ((heckeCoeff m : ℤ) : ℂ)) s * hGinv

/-! ## The coefficient identification: measured instances and the blind frames

The full identification `heckeCoeff p = a_p` at every good prime is Gauss's theorem
(1814) — the quartic-residue evaluation.  Its blind half is already a theorem on both
sides, and the sighted half is kernel-checked at the first three sighted primes. -/

/-- On the blind frames `p ≡ 3 (mod 4)` the two coefficient streams agree: both vanish
— the reflection census on the curve side, the two-squares refusal on the Hecke side. -/
theorem theCoefficientsAgreeOnTheBlindFrames (p : ℕ) [Fact p.Prime] (h3 : p % 4 = 3) :
    (heckeCoeff p : ℤ) = traceOfFrobenius 1 p := by
  rw [heckeCoeff_three_mod_four h3, theCoefficientVanishesOnTheBlindFrames 1 p h3]

set_option maxRecDepth 4000 in
/-- The identification at the first sighted prime: `c₅ = a₅ = −2`. -/
theorem theCoefficientsAgreeAtFive : (heckeCoeff 5 : ℤ) = traceOfFrobenius 1 5 := by decide

set_option maxRecDepth 20000 in
/-- The identification at thirteen: `c₁₃ = a₁₃ = 6`. -/
theorem theCoefficientsAgreeAtThirteen : (heckeCoeff 13 : ℤ) = traceOfFrobenius 1 13 := by
  decide

set_option maxRecDepth 40000 in
/-- The identification at seventeen: `c₁₇ = a₁₇ = 2`. -/
theorem theCoefficientsAgreeAtSeventeen : (heckeCoeff 17 : ℤ) = traceOfFrobenius 1 17 := by
  decide

/-- The bad-prime clause of the pose, discharged for the Hecke stream: the only bad
prime is two, and every even-norm shell is empty. -/
theorem theBadPrimeClauseHolds (p k : ℕ) (hp : p.Prime) (hdvd : p ∣ 2 * 1) :
    ((heckeCoeff (p ^ (k + 1)) : ℤ) : ℂ) = ((heckeCoeff p : ℤ) : ℂ) ^ (k + 1) := by
  have hp2 : p = 2 := by
    have h2 : p ∣ 2 := by simpa using hdvd
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  subst hp2
  rw [heckeCoeff_even (by simp [Nat.pow_mod]), heckeCoeff_even (by norm_num)]
  norm_num

/-! ## The witness

Every field of the pose's analytic datum is now a theorem.  The declared receiver of
`BirchSwinnertonDyer.lean` — posed 2026-08-22 as conditional — is inhabited. -/

open Soma.Holonics.Millennium.HeckeEuler in
/-- **THE WITNESS**: the analytic datum of the congruent-number curve at one.  Every
field is kernel-checked: the coefficients are the computable shell sums, their prime
values are the point counts (Gauss), their Euler structure is the Gaussian-integer
factorization, the L-function is the Mellin transform of the theta function, and the
functional equation is the theta transformation law with sign `+1`. -/
noncomputable def theWitness : LDatum 1 where
  coeff := fun m => ((heckeCoeff m : ℤ) : ℂ)
  coeff_one := by
    rw [heckeCoeff_one]
    norm_num
  coeff_prime := fun p hp hpd => by
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro h
      exact hpd ⟨1, show 2 * 1 = p * 1 from by rw [h]⟩
    have h := theCoefficientsAgreeAtEveryOddPrime (p := p) hp2
    exact_mod_cast h
  coeff_mul := fun a b hab => by
    have h := heckeCoeff_mul hab
    exact_mod_cast h
  coeff_prime_pow := fun p k hp hpd => by
    haveI : Fact p.Prime := ⟨hp⟩
    have hp2 : p ≠ 2 := by
      intro h
      exact hpd ⟨1, show 2 * 1 = p * 1 from by rw [h]⟩
    have h := heckeCoeff_prime_pow_recursion (p := p) hp2 k
    exact_mod_cast h
  coeff_bad := fun p k hp hpd => theBadPrimeClauseHolds p k hp hpd
  L := heckeL
  analytic := theLFunctionIsEntire
  agrees := fun s hs => theLFunctionAgreesWithItsDirichletSeries hs
  conductor := 32
  conductor_pos := by norm_num
  sign := 1
  sign_pm := Or.inl rfl
  Lambda := heckeLambda
  Lambda_analytic := theCompletedLFunctionIsEntire
  Lambda_eq := fun s hs => (theCompletedProductFormulaHolds s hs).symm
  functional_equation := fun s => by
    rw [theCompletedLFunctionalEquation s]
    push_cast
    ring

/-- **The pose is unconditional at one**: the analytic datum exists. -/
theorem theWitnessExists : Nonempty (LDatum 1) := ⟨theWitness⟩

/-- **The analytic rank at one is zero**: the witness's L-function does not vanish at
the center, because its central value is `(2π/√32)` times the integral of the positive
theta function. -/
theorem theAnalyticRankAtOneIsZero : analyticRank theWitness = 0 := by
  unfold analyticRank
  rw [analyticOrderAt_eq_zero]
  right
  exact theLFunctionDoesNotVanishAtOne

/-! ## The two-sided rank-zero instance -/

/-- Every point of the curve at one is two-torsion: the four-point classification. -/
private lemma every_point_two_torsion (P : (FamilyFace.E ((1 : ℕ) : ℚ)).Point) :
    P + P = 0 := by
  have hEq : FamilyFace.E ((1 : ℕ) : ℚ) = Descent.E := by
    unfold FamilyFace.E Descent.E
    norm_num
  revert P
  rw [hEq]
  intro P
  rcases RankZero.theFourHalfTurnsAreTheWholePopulationHolds P with h | h | h | h <;> subst h
  · rfl
  · exact Descent.theThreePointsAreHalfTurns.1
  · exact Descent.theThreePointsAreHalfTurns.2.1
  · exact Descent.theThreePointsAreHalfTurns.2.2

/-- **The algebraic rank at one is zero**: rank at least zero holds vacuously, and no
point is independent modulo torsion because every point is two-torsion — the completed
descent (`RankZero`: one is not a congruent number) speaking as the posed rank
predicate. -/
theorem theAlgebraicRankAtOneIsZero : AlgebraicRankIs 1 0 := by
  constructor
  · exact ⟨fun i => i.elim0, fun c _ i => i.elim0⟩
  · rintro ⟨Pts, hInd⟩
    have h2 : (2 : ℤ) = 0 := by
      refine hInd (fun _ => 2) ?_ 0
      refine ⟨1, one_pos, ?_⟩
      have hsum : (∑ i : Fin 1, (2 : ℤ) • Pts i) = (2 : ℤ) • Pts 0 := by
        rw [Finset.sum_fin_eq_sum_range]
        simp
      rw [hsum]
      have h2t : (2 : ℤ) • Pts 0 = 0 := by
        rw [show (2 : ℤ) = 1 + 1 from rfl, add_zsmul, one_zsmul]
        exact every_point_two_torsion (Pts 0)
      rw [h2t]
      simp
    norm_num at h2

/-- **THE TWO-SIDED RANK-ZERO INSTANCE AT ONE.**  The witness's analytic rank and the
curve's algebraic rank are both zero: the first fully kernel-checked two-sided instance
of the Birch–Swinnerton-Dyer rank correspondence.  On the analytic side the central
value is the integral of the positive theta function; on the algebraic side the
completed descent leaves only the four half-turns. -/
theorem theTwoSidedRankZeroInstance :
    analyticRank theWitness = (0 : ℕ) ∧ AlgebraicRankIs 1 0 :=
  ⟨theAnalyticRankAtOneIsZero, theAlgebraicRankAtOneIsZero⟩

end Soma.Holonics.Millennium.HeckeWitness
