import ElementaryHolonics.Millennium.FamilyDuplication
import Mathlib.NumberTheory.LSeries.AbstractFuncEq
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.Tactic

/-!
# FamilyThetaFE: the theta functional equation and the central vanishing across the family

**The analytic arm of the congruent-number campaign, family-wise.**  The duplication
identity (`FamilyDuplication`) converts, at every prime `p ≡ 1 (mod 4)`, into:

* **`theFamilyThetaFunctionalEquation`** — `θ_p(1/x) = χ_p(2)·x²·θ_p(x)`: weight two,
  level `32p²`, sign `χ_p(2)`.
* **`theFamilySignIsTheSecondSupplement`** — the sign is decided by `p mod 8`
  (the second supplement of quadratic reciprocity): `+1` at `p ≡ 1 (mod 8)`,
  `−1` at `p ≡ 5 (mod 8)`.
* **`theCompletedLFunctionIsEntireAtEverySplitPrime`**,
  **`theCompletedFunctionalEquationAtEverySplitPrime`** — the strong FE-pair returns
  `Λ_p` entire with `Λ_p(2−s) = χ_p(2)·Λ_p(s)`.
* **`theOddHandForcesTheCentralVanishingOnTheFiveModEightFamily`** — for **every**
  prime `p ≡ 5 (mod 8)`, the sign is `−1` and `Λ_p(1) = 0`: the central value dies by
  parity alone, across an infinite family at once.  Analytic rank at least one on the
  whole `p ≡ 5 (mod 8)` branch, kernel-checked with no L-value computation.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyThetaFE

open Real HurwitzZeta Complex
open Soma.Holonics.Millennium.FamilyDuplication

private lemma sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

/-! ## 1. The family theta function -/

/-- **The theta function of the congruent-number family at the split prime `p`**: the
`χ_p`-weighted Gaussian class sum, presented as `4p` times the `2p²` products of
shifted Hurwitz kernels at argument `4p√2·x` — conductor `32p²`, weight two. -/
def thetaP (p : ℕ) [Fact p.Prime] (x : ℝ) : ℝ :=
  4 * p * ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
    (wP p e d : ℝ) *
      (oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
          (4 * p * Real.sqrt 2 * x) *
       evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) (4 * p * Real.sqrt 2 * x))

private lemma rpow_two_of_pos {t : ℝ} (ht : 0 < t) :
    t ^ ((3 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) = t ^ 2 := by
  rw [← Real.rpow_add ht, show (3 : ℝ) / 2 + 1 / 2 = ((2 : ℕ) : ℝ) from by norm_num,
    Real.rpow_natCast]

/-! ## 2. The theta functional equation -/

set_option maxHeartbeats 1000000 in
/-- **THE FAMILY THETA FUNCTIONAL EQUATION.**  At every prime `p ≡ 1 (mod 4)` and
`x > 0`, `θ_p(1/x) = χ_p(2)·x²·θ_p(x)`: weight two, level `32p²`, **sign `χ_p(2)`** —
the two mathlib Hurwitz-kernel functional equations composed through the family
duplication identity, with the modulus a parameter. -/
theorem theFamilyThetaFunctionalEquation (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1)
    {x : ℝ} (hx : 0 < x) :
    thetaP p (1 / x) = ((XP p 2 : ℤ) : ℝ) * x ^ 2 * thetaP p x := by
  have hp : p.Prime := Fact.out
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos
  have h4p : (0 : ℝ) < 4 * p * Real.sqrt 2 := by positivity
  have hy : (0 : ℝ) < x / (4 * p * Real.sqrt 2) := by positivity
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : (4 : ℝ) * p * Real.sqrt 2 ≠ 0 := h4p.ne'
  unfold thetaP
  rw [show 4 * (p : ℝ) * Real.sqrt 2 * (1 / x) = 1 / (x / (4 * p * Real.sqrt 2)) from by
    rw [one_div_div]; ring]
  have hterm : ∀ e ∈ Finset.range p, ∀ d ∈ Finset.range (2 * p),
      (wP p e d : ℝ) *
        (oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
            (1 / (x / (4 * p * Real.sqrt 2))) *
         evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
            (1 / (x / (4 * p * Real.sqrt 2))))
      = (x ^ 2 / (32 * p ^ 2)) * ((wP p e d : ℝ) *
          (sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2)) *
           cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2)))) := by
    intro e _ d _
    rw [oddKernel_functional_equation _ (1 / (x / (4 * p * Real.sqrt 2))),
      evenKernel_functional_equation _ (1 / (x / (4 * p * Real.sqrt 2))),
      one_div_one_div,
      show (1 / (x / (4 * p * Real.sqrt 2))) = (x / (4 * p * Real.sqrt 2))⁻¹ from
        one_div _,
      Real.inv_rpow hy.le, Real.inv_rpow hy.le, one_div, one_div, inv_inv, inv_inv]
    have hpow : (x / (4 * p * Real.sqrt 2)) ^ ((3 : ℝ) / 2) *
        (x / (4 * p * Real.sqrt 2)) ^ ((1 : ℝ) / 2) = x ^ 2 / (32 * p ^ 2) := by
      rw [rpow_two_of_pos hy, div_pow]
      congr 1
      rw [mul_pow, mul_pow]
      linear_combination (16 * (p : ℝ) ^ 2) * hss
    calc (wP p e d : ℝ) *
          ((x / (4 * p * Real.sqrt 2)) ^ ((3 : ℝ) / 2) *
            sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2)) *
           ((x / (4 * p * Real.sqrt 2)) ^ ((1 : ℝ) / 2) *
            cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2))))
        = ((x / (4 * p * Real.sqrt 2)) ^ ((3 : ℝ) / 2) *
            (x / (4 * p * Real.sqrt 2)) ^ ((1 : ℝ) / 2)) * ((wP p e d : ℝ) *
            (sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2)) *
             cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2)))) := by
          ring
      _ = _ := by rw [hpow]
  rw [Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun d hd => hterm e he d hd]
  have hpull : ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
      (x ^ 2 / (32 * p ^ 2)) * ((wP p e d : ℝ) *
        (sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
            (x / (4 * p * Real.sqrt 2)) *
         cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
            (x / (4 * p * Real.sqrt 2))))
      = (x ^ 2 / (32 * p ^ 2)) * ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
          (wP p e d : ℝ) *
            (sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
                (x / (4 * p * Real.sqrt 2)) *
             cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
                (x / (4 * p * Real.sqrt 2))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
  have hp2 : p ≠ 2 := by omega
  have hsign1 : ((-1 : ℝ)) ^ ((p - 1) / 2) = 1 :=
    Even.neg_one_pow ⟨(p - 1) / 4, by omega⟩
  rw [hpull, theFamilyDuplicationIdentity p hp2 hy, hsign1, one_mul]
  have h32 : 32 * (p : ℝ) ^ 2 * (x / (4 * p * Real.sqrt 2)) = 4 * p * Real.sqrt 2 * x := by
    rw [show 32 * (p : ℝ) ^ 2 * (x / (4 * p * Real.sqrt 2))
        = 32 * (p : ℝ) ^ 2 * x / (4 * p * Real.sqrt 2) from by ring,
      div_eq_iff hne]
    linear_combination (-16 * (p : ℝ) ^ 2 * x) * hss
  rw [h32]
  have hpne : (p : ℝ) ≠ 0 := hp'.ne'
  field_simp

/-! ## 3. The family sign law: the second supplement -/

/-- **THE FAMILY SIGN IS THE SECOND SUPPLEMENT.**  For every odd prime `p`, the sign
`χ_p(2)` of the family theta functional equation is decided by `p mod 8` — quadratic
reciprocity's second supplement, reading the root-number dial of the congruent-number
family. -/
theorem theFamilySignIsTheSecondSupplement (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    XP p 2 = if p % 8 = 1 ∨ p % 8 = 7 then 1 else -1 := by
  have hp : p.Prime := Fact.out
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · exact absurd h hp2
    · exact h
  have h2 : ((2 : ℤ) : ZMod p) = (2 : ZMod p) := by norm_num
  unfold XP
  rw [h2, quadraticChar_two hchar, ZMod.card p, ZMod.χ₈_nat_eq_if_mod_eight,
    if_neg (by omega)]

/-- The sign is `−1` on the `p ≡ 5 (mod 8)` branch. -/
theorem theFamilySignOnFiveModEight (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 5) :
    XP p 2 = -1 := by
  rw [theFamilySignIsTheSecondSupplement p (by omega)]
  rw [if_neg (by omega)]

/-- The sign is `+1` on the `p ≡ 1 (mod 8)` branch. -/
theorem theFamilySignOnOneModEight (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 1) :
    XP p 2 = 1 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  rw [theFamilySignIsTheSecondSupplement p hp2]
  rw [if_pos (Or.inl hp8)]

/-! ## 4. Continuity and decay of the family theta -/

lemma continuousOn_thetaP (p : ℕ) [Fact p.Prime] :
    ContinuousOn (thetaP p) (Set.Ioi 0) := by
  have hp : p.Prime := Fact.out
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold thetaP
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_sum _ fun e _ => ?_
  refine continuousOn_finset_sum _ fun d _ => ?_
  refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul ?_ ?_)
  · refine (continuousOn_oddKernel _).comp (Continuous.continuousOn (by fun_prop)) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx ⊢
    positivity
  · refine (continuousOn_evenKernel _).comp (Continuous.continuousOn (by fun_prop)) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx ⊢
    positivity

private lemma isBigO_term_rpow (p : ℕ) [Fact p.Prime] (e d : ℕ) (r : ℝ) :
    (fun x : ℝ => (wP p e d : ℝ) *
        (oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
            (4 * p * Real.sqrt 2 * x) *
         evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) (4 * p * Real.sqrt 2 * x)))
      =O[Filter.atTop] fun x : ℝ => x ^ r := by
  have hp : p.Prime := Fact.out
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos
  have h4p : (0 : ℝ) < 4 * p * Real.sqrt 2 := by positivity
  have ht : Filter.Tendsto (fun x : ℝ => 4 * p * Real.sqrt 2 * x)
      Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop h4p
  obtain ⟨c₁, hc₁, hodd'⟩ :=
    isBigO_atTop_oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
  obtain ⟨c₂, hc₂, heven'⟩ :=
    isBigO_atTop_evenKernel_sub (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
  have hodd : (fun x : ℝ =>
      oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
        (4 * p * Real.sqrt 2 * x))
      =O[Filter.atTop] fun x => rexp (-(4 * p * Real.sqrt 2 * c₁) * x) := by
    refine (hodd'.comp_tendsto ht).congr' Filter.EventuallyEq.rfl ?_
    exact Filter.Eventually.of_forall fun x => by
      show rexp (-c₁ * (4 * p * Real.sqrt 2 * x)) = rexp (-(4 * p * Real.sqrt 2 * c₁) * x)
      congr 1
      ring
  have heven : (fun x : ℝ =>
      evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) (4 * p * Real.sqrt 2 * x))
      =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
    have hsub : (fun x : ℝ =>
        evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) (4 * p * Real.sqrt 2 * x)
          - (if (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) = 0 then 1 else 0))
        =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
      refine (heven'.comp_tendsto ht).trans ?_
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
      show |((fun x => rexp (-c₂ * x)) ∘ fun x => 4 * p * Real.sqrt 2 * x) x| ≤ 1 * ‖(1 : ℝ)‖
      simp only [Function.comp_apply]
      rw [abs_of_nonneg (Real.exp_nonneg _), norm_one, mul_one]
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ c₂ * (4 * p * Real.sqrt 2 * x) := by positivity
      linarith
    have hconst : (fun _ : ℝ =>
        (if (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) = 0 then (1 : ℝ) else 0))
        =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards with x
      split_ifs <;> simp
    have := hsub.add hconst
    refine this.congr_left fun x => ?_
    ring
  have hprod := (hodd.const_mul_left (wP p e d : ℝ)).mul heven
  have hexp : (fun x : ℝ => (wP p e d : ℝ) *
      oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
        (4 * p * Real.sqrt 2 * x) *
      evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) (4 * p * Real.sqrt 2 * x))
      =O[Filter.atTop] fun x => rexp (-(4 * p * Real.sqrt 2 * c₁) * x) := by
    refine hprod.congr_right fun x => mul_one _
  have hfin := hexp.trans
    (isLittleO_exp_neg_mul_rpow_atTop
      (show (0 : ℝ) < 4 * p * Real.sqrt 2 * c₁ by positivity) r).isBigO
  refine hfin.congr_left fun x => ?_
  ring

lemma isBigO_atTop_thetaP (p : ℕ) [Fact p.Prime] (r : ℝ) :
    thetaP p =O[Filter.atTop] fun x : ℝ => x ^ r := by
  unfold thetaP
  have hsum : (fun x : ℝ => ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
      (wP p e d : ℝ) *
        (oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
            (4 * p * Real.sqrt 2 * x) *
         evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle) (4 * p * Real.sqrt 2 * x)))
      =O[Filter.atTop] fun x : ℝ => x ^ r := by
    have h1 : ∀ e ∈ Finset.range p, (fun x : ℝ => ∑ d ∈ Finset.range (2 * p),
        (wP p e d : ℝ) *
          (oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
              (4 * p * Real.sqrt 2 * x) *
           evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
              (4 * p * Real.sqrt 2 * x)))
        =O[Filter.atTop] fun x : ℝ => x ^ r := fun e _ =>
      Asymptotics.IsBigO.sum fun d _ => isBigO_term_rpow p e d r
    exact Asymptotics.IsBigO.sum h1
  exact hsum.const_mul_left (4 * p)

/-! ## 5. The strong FE-pair and the completed L-function -/

/-- The family sign is nonzero. -/
private lemma XP_two_ne_zero (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1) :
    ((XP p 2 : ℤ) : ℂ) ≠ 0 := by
  have hp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  intro h
  have h1 : XP p 2 = 0 := by exact_mod_cast h
  unfold XP at h1
  rw [show ((2 : ℤ) : ZMod p) = (2 : ZMod p) from by norm_num] at h1
  rw [quadraticChar_eq_zero_iff] at h1
  have h2 : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast h1
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h2
  have := Int.le_of_dvd (by norm_num) h2
  omega

/-- The strong FE-pair of the congruent-number family at the split prime `p`:
`f = g = θ_p`, weight `2`, **sign `χ_p(2)`**, no constant terms. -/
def familyFEPair (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1) : StrongFEPair ℂ where
  f := Complex.ofReal ∘ thetaP p
  g := Complex.ofReal ∘ thetaP p
  k := 2
  hk := two_pos
  ε := ((XP p 2 : ℤ) : ℂ)
  hε := XP_two_ne_zero p hp1
  f₀ := 0
  g₀ := 0
  hf₀ := rfl
  hg₀ := rfl
  hf_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_thetaP p)).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_thetaP p)).locallyIntegrableOn measurableSet_Ioi
  h_feq x hx := by
    have hfe := theFamilyThetaFunctionalEquation p hp1 (Set.mem_Ioi.mp hx)
    simp only [Function.comp_apply, smul_eq_mul, hfe]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    push_cast
    ring
  hf_top r := by
    simpa using isBigO_ofReal_left.mpr (isBigO_atTop_thetaP p r)
  hg_top r := by
    simpa using isBigO_ofReal_left.mpr (isBigO_atTop_thetaP p r)

/-- **The completed L-function of the congruent-number family at the split prime `p`**:
the Mellin transform of `θ_p`, with no convergence region. -/
def lambdaP (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1) : ℂ → ℂ := (familyFEPair p hp1).Λ

/-- **`Λ_p` is entire at every split prime** — the strong FE-pair machinery returns
differentiability on all of `ℂ` at once, no continuation step, with the modulus a
parameter. -/
theorem theCompletedLFunctionIsEntireAtEverySplitPrime (p : ℕ) [Fact p.Prime]
    (hp1 : p % 4 = 1) : Differentiable ℂ (lambdaP p hp1) :=
  (familyFEPair p hp1).differentiable_Λ

/-- The Mellin representation of `Λ_p` at every `s`. -/
theorem theCompletedLFunctionHasMellinAtEverySplitPrime (p : ℕ) [Fact p.Prime]
    (hp1 : p % 4 = 1) (s : ℂ) :
    HasMellin (Complex.ofReal ∘ thetaP p) s (lambdaP p hp1 s) :=
  (familyFEPair p hp1).hasMellin s

/-- **THE COMPLETED FUNCTIONAL EQUATION AT EVERY SPLIT PRIME**:
`Λ_p(2−s) = χ_p(2)·Λ_p(s)`.  Weight two, sign the second supplement — the reflection
of the whole congruent-number family, kernel-checked with the modulus a parameter. -/
theorem theCompletedFunctionalEquationAtEverySplitPrime (p : ℕ) [Fact p.Prime]
    (hp1 : p % 4 = 1) (s : ℂ) :
    lambdaP p hp1 (2 - s) = ((XP p 2 : ℤ) : ℂ) * lambdaP p hp1 s := by
  have h := (familyFEPair p hp1).functional_equation s
  rw [show (familyFEPair p hp1).k = (2 : ℝ) from rfl,
    show (familyFEPair p hp1).ε = ((XP p 2 : ℤ) : ℂ) from rfl] at h
  have hsymm : (familyFEPair p hp1).symm.Λ = (familyFEPair p hp1).Λ := rfl
  rw [hsymm] at h
  simpa [lambdaP, smul_eq_mul] using h

/-- **THE ODD HAND FORCES THE CENTRAL VANISHING ON THE `p ≡ 5 (mod 8)` FAMILY:
`Λ_p(1) = 0` for every prime `p ≡ 5 (mod 8)`.**  The second supplement makes the sign
`−1`, and the value at the fixed point of an odd reflection dies by parity alone —
analytic rank at least one across an infinite branch of the congruent-number family,
kernel-checked with no L-value computation. -/
theorem theOddHandForcesTheCentralVanishingOnTheFiveModEightFamily
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 5) :
    lambdaP p (by omega) 1 = 0 := by
  have hp1 : p % 4 = 1 := by omega
  have h := theCompletedFunctionalEquationAtEverySplitPrime p hp1 1
  rw [show (2 : ℂ) - 1 = 1 from by norm_num, theFamilySignOnFiveModEight p hp8] at h
  push_cast at h
  linear_combination h / 2


/-! ## 6. The theta as its lattice class sum -/

private lemma XP_two_sq (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1) :
    ((XP p 2 : ℤ) : ℂ) * ((XP p 2 : ℤ) : ℂ) = 1 := by
  have hp : p.Prime := Fact.out
  have hp5 : 5 ≤ p := by have := hp.two_le; omega
  have h20 : ((2 : ℤ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
    intro h
    have := Int.le_of_dvd (by norm_num) h
    omega
  have h := quadraticChar_sq_one h20
  rw [pow_two] at h
  have h2 : XP p 2 * XP p 2 = 1 := h
  exact_mod_cast h2

set_option maxHeartbeats 1000000 in
/-- **The family theta is its own lattice class sum**: for `t > 0`,
`θ_p(t) = Σ_{(k,l)∈ℤ²} (4k+1)·(−1)^l·χ_p((4k+1)²+4l²)·exp(−(π√2/(4p))·((4k+1)²+4l²)·t)`
— the `χ_p`-weighted Gaussian class sum at every split prime, returned as a `HasSum`
so the receiver can integrate against it term by term.  The functional-equation sign
`χ_p(2)` cancels out of the lattice presentation, as it must. -/
theorem theFamilyThetaIsItsLatticeSum (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1)
    {t : ℝ} (ht : 0 < t) :
    HasSum (fun q : ℤ × ℤ =>
      ((4 * q.1 + 1 : ℤ) : ℝ) * (if q.2 % 2 = 0 then (1 : ℝ) else -1) *
        (XP p ((4 * q.1 + 1) ^ 2 + 4 * q.2 ^ 2) : ℝ) *
        rexp (-(π * Real.sqrt 2 / (4 * p)) *
          (((4 * q.1 + 1) ^ 2 + 4 * q.2 ^ 2 : ℤ) : ℝ) * t))
      (thetaP p t) := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hs : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos
  set y : ℝ := Real.sqrt 2 * t / (8 * p) with hy_def
  have hy : 0 < y := by positivity
  have h32 : 32 * (p : ℝ) ^ 2 * y = 4 * p * Real.sqrt 2 * t := by
    rw [hy_def]
    field_simp
    ring
  have hχ := XP_two_sq p hp1
  set χ : ℂ := ((XP p 2 : ℤ) : ℂ) with hχdef
  have hpc : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0.ne'
  have hCdef : ((thetaP p t : ℝ) : ℂ)
      = 4 * (p : ℂ) * ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
          ((wP p e d : ℤ) : ℂ) *
            (((oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
                (32 * p ^ 2 * y) : ℝ) : ℂ) *
             ((evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
                (32 * p ^ 2 * y) : ℝ) : ℂ)) := by
    rw [h32]
    unfold thetaP
    push_cast
    rfl
  set S : ℂ := ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
      ((wP p e d : ℤ) : ℂ) *
        (((oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
            (32 * p ^ 2 * y) : ℝ) : ℂ) *
         ((evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
            (32 * p ^ 2 * y) : ℝ) : ℂ)) with hSdef
  have hC : ((thetaP p t : ℝ) : ℂ) = χ / (8 * p) * ∑' q : ℤ × ℤ, hFinalP p y q := by
    rw [hCdef]
    have hps := primal_side_eq p hp0 hy
    rw [← hSdef] at hps
    field_simp
    linear_combination (-χ) * hps + (-(32 * (p : ℂ) ^ 2 * S)) * hχ
  have hSum : HasSum (fun q : ℤ × ℤ => χ / (8 * p) * hFinalP p y (gridEmb q))
      (((thetaP p t : ℝ) : ℂ)) := by
    have h1 : HasSum (hFinalP p y) (∑' q : ℤ × ℤ, hFinalP p y q) :=
      (summable_hFinalP p hy).hasSum
    have h2 : HasSum (fun q : ℤ × ℤ => hFinalP p y (gridEmb q))
        (∑' q : ℤ × ℤ, hFinalP p y q) :=
      (gridEmb_injective.hasSum_iff (hFinalP_support p y)).mpr h1
    have h3 := h2.mul_left (χ / (8 * p))
    rwa [← hC] at h3
  have hpt : ∀ q : ℤ × ℤ, χ / (8 * p) * hFinalP p y (gridEmb q)
      = ((((4 * q.1 + 1 : ℤ) : ℝ) * (if q.2 % 2 = 0 then (1 : ℝ) else -1) *
          (XP p ((4 * q.1 + 1) ^ 2 + 4 * q.2 ^ 2) : ℝ) *
          rexp (-(π * Real.sqrt 2 / (4 * p)) *
            (((4 * q.1 + 1) ^ 2 + 4 * q.2 ^ 2 : ℤ) : ℝ) * t) : ℝ) : ℂ) := by
    rintro ⟨k, l⟩
    show χ / (8 * p) * hFinalP p y (4 * k + 1, 2 * l) = _
    unfold hFinalP
    rw [if_pos (show (4 * k + 1) % 4 = 1 by omega)]
    have hcs : cs4 (2 * l) = ((if l % 2 = 0 then (1 : ℝ) else -1 : ℝ) : ℂ) := by
      unfold cs4
      rcases Int.even_or_odd l with ⟨u, hu⟩ | ⟨u, hu⟩
      · rw [if_pos (by omega), if_pos (by omega)]
        norm_num
      · rw [if_neg (by omega), if_pos (by omega), if_neg (by omega)]
        norm_num
    have hchi : XP p (2 * ((4 * k + 1) ^ 2 + (2 * l) ^ 2))
        = XP p 2 * XP p ((4 * k + 1) ^ 2 + 4 * l ^ 2) := by
      rw [XP_mul p, show (4 * k + 1) ^ 2 + (2 * l) ^ 2
        = (4 * k + 1) ^ 2 + 4 * l ^ 2 from by ring]
    have henv : envF y (4 * k + 1) (2 * l)
        = rexp (-(π * Real.sqrt 2 / (4 * p)) *
            (((4 * k + 1) ^ 2 + 4 * l ^ 2 : ℤ) : ℝ) * t) := by
      unfold envF
      rw [hy_def]
      congr 1
      push_cast
      field_simp
      ring
    rw [hcs, hchi, henv]
    push_cast
    field_simp
    linear_combination ((4 * (k : ℂ) + 1) *
      ((if l % 2 = 0 then (1 : ℝ) else -1 : ℝ) : ℂ) *
      ((XP p ((4 * k + 1) ^ 2 + 4 * l ^ 2) : ℤ) : ℂ)) * hχ
  have hSum2 : HasSum (fun q : ℤ × ℤ =>
      ((((4 * q.1 + 1 : ℤ) : ℝ) * (if q.2 % 2 = 0 then (1 : ℝ) else -1) *
        (XP p ((4 * q.1 + 1) ^ 2 + 4 * q.2 ^ 2) : ℝ) *
        rexp (-(π * Real.sqrt 2 / (4 * p)) *
          (((4 * q.1 + 1) ^ 2 + 4 * q.2 ^ 2 : ℤ) : ℝ) * t) : ℝ) : ℂ))
      (((thetaP p t : ℝ) : ℂ)) := by
    refine hSum.congr_fun ?_
    intro q
    exact (hpt q).symm
  exact Complex.hasSum_ofReal.mp hSum2

set_option maxHeartbeats 1000000 in
/-- **The family theta is the twisted Gaussian class sum**: over the positive quartic
class `(a+b) ≡ 1 (mod 4)`, `b` even, with weight `a·χ_p(a²+b²)` — the Hecke sum of the
twisted character in its folded real form, at scale `√2·x/(8p)`, at every split
prime. -/
theorem theFamilyThetaIsTheTwistedClassSum (p : ℕ) [Fact p.Prime] (hp1 : p % 4 = 1)
    {x : ℝ} (hx : 0 < x) :
    HasSum (fun q : ℤ × ℤ =>
      if (q.1 + q.2) % 4 = 1 ∧ q.2 % 2 = 0 then
        ((q.1 : ℤ) : ℂ) * ((XP p (q.1 ^ 2 + q.2 ^ 2) : ℤ) : ℂ) *
          ((rexp (-2 * π * (Real.sqrt 2 * x / (8 * p)) *
            ((q.1 : ℝ) ^ 2 + (q.2 : ℝ) ^ 2)) : ℝ) : ℂ)
      else 0) ((thetaP p x : ℝ) : ℂ) := by
  have hp : p.Prime := Fact.out
  have hp0 : 0 < p := hp.pos
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp0
  have hs : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos
  set y : ℝ := Real.sqrt 2 * x / (8 * p) with hy_def
  have hy : 0 < y := by positivity
  have h32 : 32 * (p : ℝ) ^ 2 * y = 4 * p * Real.sqrt 2 * x := by
    rw [hy_def]
    field_simp
    ring
  have hχ := XP_two_sq p hp1
  set χ : ℂ := ((XP p 2 : ℤ) : ℂ) with hχdef
  have hpc : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp0.ne'
  have hCdef : ((thetaP p x : ℝ) : ℂ)
      = 4 * (p : ℂ) * ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
          ((wP p e d : ℤ) : ℂ) *
            (((oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
                (32 * p ^ 2 * y) : ℝ) : ℂ) *
             ((evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
                (32 * p ^ 2 * y) : ℝ) : ℂ)) := by
    rw [h32]
    unfold thetaP
    push_cast
    rfl
  set S : ℂ := ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
      ((wP p e d : ℤ) : ℂ) *
        (((oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
            (32 * p ^ 2 * y) : ℝ) : ℂ) *
         ((evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
            (32 * p ^ 2 * y) : ℝ) : ℂ)) with hSdef
  have hC : ((thetaP p x : ℝ) : ℂ) = χ / (2 * p) * ∑' q : ℤ × ℤ, hPlusP p y q := by
    rw [hCdef]
    have hps := primal_side_eq p hp0 hy
    rw [← hSdef] at hps
    have h4 := tsum_hFinalP_eq_four_hPlusP p hy
    rw [h4] at hps
    field_simp
    linear_combination (-(1 / 4) * χ) * hps + (-(8 * (p : ℂ) ^ 2 * S)) * hχ
  have hSum : HasSum (fun q : ℤ × ℤ => χ / (2 * p) * hPlusP p y q)
      ((thetaP p x : ℝ) : ℂ) := by
    have h1 := (summable_hPlusP p hy).hasSum.mul_left (χ / (2 * p))
    rwa [← hC] at h1
  refine hSum.congr_fun fun q => ?_
  obtain ⟨a, b⟩ := q
  show (if (a + b) % 4 = 1 ∧ b % 2 = 0 then
      ((a : ℤ) : ℂ) * ((XP p (a ^ 2 + b ^ 2) : ℤ) : ℂ) *
        ((rexp (-2 * π * y * ((a : ℝ) ^ 2 + (b : ℝ) ^ 2)) : ℝ) : ℂ)
    else 0) = χ / (2 * p) * hPlusP p y (a, b)
  unfold hPlusP
  split_ifs with h
  · have hchi : XP p (2 * (a ^ 2 + b ^ 2)) = XP p 2 * XP p (a ^ 2 + b ^ 2) :=
      XP_mul p 2 (a ^ 2 + b ^ 2)
    rw [hchi]
    unfold envF
    push_cast
    field_simp
    linear_combination (-((a : ℂ) * ((XP p (a ^ 2 + b ^ 2) : ℤ) : ℂ))) * hχ
  · ring


/-! ## 7. The functional equation and completed function at every odd prime -/

set_option maxHeartbeats 1000000 in
/-- **THE FAMILY THETA FUNCTIONAL EQUATION AT EVERY ODD PRIME**:
`θ_p(1/x) = w_p·x²·θ_p(x)` with the classical root number
`w_p = (−1)^{(p−1)/2}·χ_p(2)` — `+1` at `p ≡ 1, 3 (mod 8)`, `−1` at
`p ≡ 5, 7 (mod 8)`. -/
theorem theFamilyThetaFunctionalEquationAtEveryOddPrime (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) {x : ℝ} (hx : 0 < x) :
    thetaP p (1 / x)
      = ((-1 : ℝ)) ^ ((p - 1) / 2) * ((XP p 2 : ℤ) : ℝ) * x ^ 2 * thetaP p x := by
  have hp : p.Prime := Fact.out
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hs : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos
  have h4p : (0 : ℝ) < 4 * p * Real.sqrt 2 := by positivity
  have hy : (0 : ℝ) < x / (4 * p * Real.sqrt 2) := by positivity
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : (4 : ℝ) * p * Real.sqrt 2 ≠ 0 := h4p.ne'
  unfold thetaP
  rw [show 4 * (p : ℝ) * Real.sqrt 2 * (1 / x) = 1 / (x / (4 * p * Real.sqrt 2)) from by
    rw [one_div_div]; ring]
  have hterm : ∀ e ∈ Finset.range p, ∀ d ∈ Finset.range (2 * p),
      (wP p e d : ℝ) *
        (oddKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
            (1 / (x / (4 * p * Real.sqrt 2))) *
         evenKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
            (1 / (x / (4 * p * Real.sqrt 2))))
      = (x ^ 2 / (32 * p ^ 2)) * ((wP p e d : ℝ) *
          (sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2)) *
           cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2)))) := by
    intro e _ d _
    rw [oddKernel_functional_equation _ (1 / (x / (4 * p * Real.sqrt 2))),
      evenKernel_functional_equation _ (1 / (x / (4 * p * Real.sqrt 2))),
      one_div_one_div,
      show (1 / (x / (4 * p * Real.sqrt 2))) = (x / (4 * p * Real.sqrt 2))⁻¹ from
        one_div _,
      Real.inv_rpow hy.le, Real.inv_rpow hy.le, one_div, one_div, inv_inv, inv_inv]
    have hpow : (x / (4 * p * Real.sqrt 2)) ^ ((3 : ℝ) / 2) *
        (x / (4 * p * Real.sqrt 2)) ^ ((1 : ℝ) / 2) = x ^ 2 / (32 * p ^ 2) := by
      rw [rpow_two_of_pos hy, div_pow]
      congr 1
      rw [mul_pow, mul_pow]
      linear_combination (16 * (p : ℝ) ^ 2) * hss
    calc (wP p e d : ℝ) *
          ((x / (4 * p * Real.sqrt 2)) ^ ((3 : ℝ) / 2) *
            sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2)) *
           ((x / (4 * p * Real.sqrt 2)) ^ ((1 : ℝ) / 2) *
            cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2))))
        = ((x / (4 * p * Real.sqrt 2)) ^ ((3 : ℝ) / 2) *
            (x / (4 * p * Real.sqrt 2)) ^ ((1 : ℝ) / 2)) * ((wP p e d : ℝ) *
            (sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2)) *
             cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
              (x / (4 * p * Real.sqrt 2)))) := by
          ring
      _ = _ := by rw [hpow]
  rw [Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun d hd => hterm e he d hd]
  have hpull : ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
      (x ^ 2 / (32 * p ^ 2)) * ((wP p e d : ℝ) *
        (sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
            (x / (4 * p * Real.sqrt 2)) *
         cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
            (x / (4 * p * Real.sqrt 2))))
      = (x ^ 2 / (32 * p ^ 2)) * ∑ e ∈ Finset.range p, ∑ d ∈ Finset.range (2 * p),
          (wP p e d : ℝ) *
            (sinKernel (((4 * (e : ℝ) + 1) / (4 * p) : ℝ) : UnitAddCircle)
                (x / (4 * p * Real.sqrt 2)) *
             cosKernel (((d : ℝ) / (2 * p) : ℝ) : UnitAddCircle)
                (x / (4 * p * Real.sqrt 2))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
  rw [hpull, theFamilyDuplicationIdentity p hp2 hy]
  have h32 : 32 * (p : ℝ) ^ 2 * (x / (4 * p * Real.sqrt 2)) = 4 * p * Real.sqrt 2 * x := by
    rw [show 32 * (p : ℝ) ^ 2 * (x / (4 * p * Real.sqrt 2))
        = 32 * (p : ℝ) ^ 2 * x / (4 * p * Real.sqrt 2) from by ring,
      div_eq_iff hne]
    linear_combination (-16 * (p : ℝ) ^ 2 * x) * hss
  rw [h32]
  have hpne : (p : ℝ) ≠ 0 := hp'.ne'
  field_simp

/-- The root number is nonzero at every odd prime. -/
private lemma sign_ne_zero (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) :
    ((((-1 : ℤ)) ^ ((p - 1) / 2) * XP p 2 : ℤ) : ℂ) ≠ 0 := by
  have hp : p.Prime := Fact.out
  intro h
  have h1 : ((-1 : ℤ)) ^ ((p - 1) / 2) * XP p 2 = 0 := by exact_mod_cast h
  rcases mul_eq_zero.mp h1 with h2 | h2
  · have := pow_ne_zero ((p - 1) / 2) (by norm_num : (-1 : ℤ) ≠ 0)
    exact this h2
  · unfold XP at h2
    rw [show ((2 : ℤ) : ZMod p) = (2 : ZMod p) from by norm_num] at h2
    rw [quadraticChar_eq_zero_iff] at h2
    have h3 : ((2 : ℤ) : ZMod p) = 0 := by exact_mod_cast h2
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h3
    have h4 := Int.le_of_dvd (by norm_num) h3
    have h5 := hp.two_le
    have h6 : p = 2 := by omega
    exact hp2 h6

/-- The strong FE-pair at every odd prime: `f = g = θ_p`, weight `2`, sign the
classical root number `(−1)^{(p−1)/2}·χ_p(2)`. -/
def familyFEPairOdd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : StrongFEPair ℂ where
  f := Complex.ofReal ∘ thetaP p
  g := Complex.ofReal ∘ thetaP p
  k := 2
  hk := two_pos
  ε := ((((-1 : ℤ)) ^ ((p - 1) / 2) * XP p 2 : ℤ) : ℂ)
  hε := sign_ne_zero p hp2
  f₀ := 0
  g₀ := 0
  hf₀ := rfl
  hg₀ := rfl
  hf_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_thetaP p)).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_thetaP p)).locallyIntegrableOn measurableSet_Ioi
  h_feq x hx := by
    have hfe := theFamilyThetaFunctionalEquationAtEveryOddPrime p hp2
      (Set.mem_Ioi.mp hx)
    simp only [Function.comp_apply, smul_eq_mul, hfe]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    push_cast
    ring
  hf_top r := by
    simpa using isBigO_ofReal_left.mpr (isBigO_atTop_thetaP p r)
  hg_top r := by
    simpa using isBigO_ofReal_left.mpr (isBigO_atTop_thetaP p r)

/-- **The completed L-function at every odd prime**: the Mellin transform of `θ_p`. -/
def lambdaPOdd (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2) : ℂ → ℂ :=
  (familyFEPairOdd p hp2).Λ

/-- **`Λ_p` is entire at every odd prime.** -/
theorem theCompletedLFunctionIsEntireAtEveryOddPrime (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) : Differentiable ℂ (lambdaPOdd p hp2) :=
  (familyFEPairOdd p hp2).differentiable_Λ

/-- The Mellin representation at every odd prime. -/
theorem theCompletedLFunctionHasMellinAtEveryOddPrime (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (s : ℂ) :
    HasMellin (Complex.ofReal ∘ thetaP p) s (lambdaPOdd p hp2 s) :=
  (familyFEPairOdd p hp2).hasMellin s

/-- **THE COMPLETED FUNCTIONAL EQUATION AT EVERY ODD PRIME**:
`Λ_p(2−s) = (−1)^{(p−1)/2}·χ_p(2)·Λ_p(s)` — the classical root number, at both
residue branches of the congruent-number family at once. -/
theorem theCompletedFunctionalEquationAtEveryOddPrime (p : ℕ) [Fact p.Prime]
    (hp2 : p ≠ 2) (s : ℂ) :
    lambdaPOdd p hp2 (2 - s)
      = ((((-1 : ℤ)) ^ ((p - 1) / 2) * XP p 2 : ℤ) : ℂ) * lambdaPOdd p hp2 s := by
  have h := (familyFEPairOdd p hp2).functional_equation s
  rw [show (familyFEPairOdd p hp2).k = (2 : ℝ) from rfl,
    show (familyFEPairOdd p hp2).ε
      = ((((-1 : ℤ)) ^ ((p - 1) / 2) * XP p 2 : ℤ) : ℂ) from rfl] at h
  have hsymm : (familyFEPairOdd p hp2).symm.Λ = (familyFEPairOdd p hp2).Λ := rfl
  rw [hsymm] at h
  simpa [lambdaPOdd, smul_eq_mul] using h

/-- **The central value vanishes on the whole odd-sign locus `p ≡ 5, 7 (mod 8)`**:
the root number is `−1` there, and the fixed point of an odd reflection dies. -/
theorem theOddHandForcesTheCentralVanishingOnTheOddSignBranches
    (p : ℕ) [Fact p.Prime] (hp8 : p % 8 = 5 ∨ p % 8 = 7) :
    lambdaPOdd p (by rcases hp8 with h | h <;> omega) 1 = 0 := by
  have hp2 : p ≠ 2 := by rcases hp8 with h | h <;> omega
  have hsign : (((-1 : ℤ)) ^ ((p - 1) / 2) * XP p 2 : ℤ) = -1 := by
    have hXP := theFamilySignIsTheSecondSupplement p hp2
    rcases hp8 with h | h
    · rw [hXP, if_neg (by omega)]
      have heven : Even ((p - 1) / 2) := ⟨(p - 1) / 4, by omega⟩
      rw [heven.neg_one_pow]
      ring
    · rw [hXP, if_pos (Or.inr (by omega))]
      have hodd : Odd ((p - 1) / 2) := ⟨(p - 3) / 4, by omega⟩
      rw [hodd.neg_one_pow]
      ring
  have h := theCompletedFunctionalEquationAtEveryOddPrime p hp2 1
  rw [show (2 : ℂ) - 1 = 1 from by norm_num, hsign] at h
  push_cast at h
  linear_combination h / 2

end Soma.Holonics.Millennium.FamilyThetaFE

