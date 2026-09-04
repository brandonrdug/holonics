import ElementaryHolonics.Millennium.BirchSwinnertonDyerParity
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv

/-!
# The sign law: the functional-equation sign is the parity of the central order

If an analytic function satisfies the reflection `f (2c − s) = ε · f s`, then its leading Taylor
coefficient at `c` satisfies `ε = (−1)^m`, where `m` is the order of vanishing at `c`.  Applied to
the completed L-function of an L-datum this reads the sign of the functional equation as the
parity of the central order: sign `+1` forces even order, sign `−1` forces odd order.
-/

noncomputable section

namespace Soma.Holonics.Millennium.BirchSwinnertonDyerSignLaw

open Soma.Holonics.Millennium.BirchSwinnertonDyer
open Soma.Holonics.Millennium.BirchSwinnertonDyerParity
open Complex Filter Topology

/-- **Reflection reads parity.** -/
theorem sign_eq_neg_one_pow_of_reflection {f : ℂ → ℂ} {c ε : ℂ} (hf : AnalyticAt ℂ f c)
    (hsym : ∀ s, f (2 * c - s) = ε * f s) {m : ℕ} (hm : analyticOrderAt f c = m) :
    ε = (-1) ^ m := by
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp hm
  have hr : Tendsto (fun z : ℂ => 2 * c - z) (𝓝 c) (𝓝 c) := by
    have h : Tendsto (fun z : ℂ => 2 * c - z) (𝓝 c) (𝓝 (2 * c - c)) :=
      tendsto_const_nhds.sub tendsto_id
    have h2 : (2 : ℂ) * c - c = c := by ring
    rwa [h2] at h
  have hfg' : ∀ᶠ z in 𝓝 c, f (2 * c - z) = (2 * c - z - c) ^ m • g (2 * c - z) :=
    hr.eventually hfg
  have : (𝓝[≠] c).NeBot := NormedField.nhdsNE_neBot c
  have key : ∀ᶠ z in 𝓝[≠] c, (-1 : ℂ) ^ m * g (2 * c - z) = ε * g z := by
    have h1 := hfg.filter_mono (nhdsWithin_le_nhds (s := {c}ᶜ))
    have h2 := hfg'.filter_mono (nhdsWithin_le_nhds (s := {c}ᶜ))
    filter_upwards [h1, h2, self_mem_nhdsWithin] with z hz1 hz2 hz
    simp only [smul_eq_mul] at hz1 hz2
    have hzc : z - c ≠ 0 := sub_ne_zero.mpr hz
    have hpow : (z - c) ^ m ≠ 0 := pow_ne_zero _ hzc
    have hs := hsym z
    rw [hz2, hz1] at hs
    have h3 : (2 : ℂ) * c - z - c = -(z - c) := by ring
    rw [h3, neg_pow] at hs
    apply mul_left_cancel₀ hpow
    linear_combination hs
  have hcont1 : Tendsto (fun z => (-1 : ℂ) ^ m * g (2 * c - z)) (𝓝 c)
      (𝓝 ((-1) ^ m * g c)) :=
    tendsto_const_nhds.mul (hg.continuousAt.tendsto.comp hr)
  have hcont2 : Tendsto (fun z => ε * g z) (𝓝 c) (𝓝 (ε * g c)) :=
    tendsto_const_nhds.mul hg.continuousAt.tendsto
  have heq : (-1 : ℂ) ^ m * g c = ε * g c :=
    tendsto_nhds_unique_of_eventuallyEq (hcont1.mono_left nhdsWithin_le_nhds)
      (hcont2.mono_left nhdsWithin_le_nhds) key
  exact (mul_right_cancel₀ hg0 heq).symm

variable {n : ℕ}

/-- **The sign law for the completed L-function.** -/
theorem sign_eq_neg_one_pow_centralOrder (W : LDatum n) {m : ℕ}
    (hm : analyticOrderAt W.Lambda 1 = m) : (W.sign : ℂ) = (-1) ^ m :=
  sign_eq_neg_one_pow_of_reflection (W.Lambda_analytic.analyticAt 1)
    (fun s => by
      rw [show (2 : ℂ) * 1 - s = 2 - s by ring]
      exact W.functional_equation s) hm

/-- Sign `+1` forces an even central order. -/
theorem even_centralOrder_of_sign_one (W : LDatum n) (hw : W.sign = 1) {m : ℕ}
    (hm : analyticOrderAt W.Lambda 1 = m) : Even m := by
  have h := sign_eq_neg_one_pow_centralOrder W hm
  rw [hw] at h
  have h' : ((-1 : ℂ)) ^ m = 1 := by
    have : ((1 : ℤ) : ℂ) = 1 := by norm_num
    rw [this] at h
    exact h.symm
  rcases Nat.even_or_odd m with he | ho
  · exact he
  · rw [ho.neg_one_pow] at h'
    norm_num at h'

/-- Sign `−1` forces an odd central order. -/
theorem odd_centralOrder_of_sign_neg_one (W : LDatum n) (hw : W.sign = -1) {m : ℕ}
    (hm : analyticOrderAt W.Lambda 1 = m) : Odd m := by
  have h := sign_eq_neg_one_pow_centralOrder W hm
  rw [hw] at h
  have h' : ((-1 : ℂ)) ^ m = -1 := by
    have : ((-1 : ℤ) : ℂ) = -1 := by norm_num
    rw [this] at h
    exact h.symm
  rcases Nat.even_or_odd m with he | ho
  · rw [he.neg_one_pow] at h'
    norm_num at h'
  · exact ho

/-- The archimedean prefactor of the completed L-function. -/
def archimedeanPrefactor (N : ℕ) (s : ℂ) : ℂ :=
  ((Real.sqrt N : ℂ) / (2 * Real.pi)) ^ s * Complex.Gamma s

theorem completed_eq_prefactor_mul (N : ℕ) (L : ℂ → ℂ) (s : ℂ) :
    completed N L s = archimedeanPrefactor N s * L s := rfl

theorem archimedeanPrefactor_one_ne_zero {N : ℕ} (hN : 0 < N) :
    archimedeanPrefactor N 1 ≠ 0 := by
  unfold archimedeanPrefactor
  rw [cpow_one, Complex.Gamma_one, mul_one]
  apply div_ne_zero
  · exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
  · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)

theorem analyticAt_archimedeanPrefactor {N : ℕ} (hN : 0 < N) :
    AnalyticAt ℂ (archimedeanPrefactor N) 1 := by
  have hc : ((Real.sqrt N : ℂ) / (2 * Real.pi)) ≠ 0 := by
    apply div_ne_zero
    · exact_mod_cast (Real.sqrt_pos.mpr (by exact_mod_cast hN)).ne'
    · exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (1 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  refine DifferentiableOn.analyticAt (s := {s : ℂ | 0 < s.re}) ?_ (hopen.mem_nhds hmem)
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · exact differentiableAt_id.const_cpow (Or.inl hc)
  · apply Complex.differentiableAt_Gamma
    intro m hm
    have hre : (0 : ℝ) < s.re := hs
    rw [hm] at hre
    simp only [neg_re, natCast_re] at hre
    linarith [Nat.cast_nonneg (α := ℝ) m]

/-- Near the centre the completed function is the prefactor times `L`. -/
theorem Lambda_eventuallyEq (W : LDatum n) :
    W.Lambda =ᶠ[𝓝 1] archimedeanPrefactor W.conductor * W.L := by
  have hopen : IsOpen {s : ℂ | 0 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  have hmem : (1 : ℂ) ∈ {s : ℂ | 0 < s.re} := by simp
  filter_upwards [hopen.mem_nhds hmem] with s hs
  rw [W.Lambda_eq s, completed_eq_prefactor_mul, Pi.mul_apply]
  intro m hm
  have hre : (0 : ℝ) < s.re := hs
  rw [hm] at hre
  simp only [neg_re, natCast_re] at hre
  linarith [Nat.cast_nonneg (α := ℝ) m]

/-- The central order of the completed function is the analytic rank. -/
theorem analyticOrderAt_Lambda_eq_analyticRank (W : LDatum n) :
    analyticOrderAt W.Lambda 1 = analyticRank W := by
  rw [analyticOrderAt_congr (Lambda_eventuallyEq W), analyticRank,
    analyticOrderAt_mul (analyticAt_archimedeanPrefactor W.conductor_pos)
      (W.analytic.analyticAt 1),
    analyticOrderAt_eq_zero.mpr (Or.inr (archimedeanPrefactor_one_ne_zero W.conductor_pos)),
    zero_add]

/-- **The sign law.** The sign of the functional equation is the parity of the analytic rank. -/
theorem theSignIsTheParityOfTheAnalyticRank (W : LDatum n) {m : ℕ}
    (hm : analyticRank W = m) : (W.sign : ℂ) = (-1) ^ m :=
  sign_eq_neg_one_pow_centralOrder W (by rw [analyticOrderAt_Lambda_eq_analyticRank, hm])

theorem even_analyticRank_of_sign_one (W : LDatum n) (hw : W.sign = 1) {m : ℕ}
    (hm : analyticRank W = m) : Even m :=
  even_centralOrder_of_sign_one W hw (by rw [analyticOrderAt_Lambda_eq_analyticRank, hm])

theorem odd_analyticRank_of_sign_neg_one (W : LDatum n) (hw : W.sign = -1) {m : ℕ}
    (hm : analyticRank W = m) : Odd m :=
  odd_centralOrder_of_sign_neg_one W hw (by rw [analyticOrderAt_Lambda_eq_analyticRank, hm])

end Soma.Holonics.Millennium.BirchSwinnertonDyerSignLaw
