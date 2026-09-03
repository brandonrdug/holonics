import Mathlib
import ElementaryHolonics.RH.RiemannXi

/-!
# FT1 (i): the value of `ξ` at the seam's centre is positive

`completedRiemannZeta₀ (½)` is Mathlib's `Λ₀(¼)/2` for the even Hurwitz FE-pair at `a = 0`, and
`Λ₀ = mellin f_modif` with `f_modif` the theta kernel with its constant terms removed on both
sides of `x = 1`.  At the symmetric point `¼` the Mellin integrand is real and nonnegative: on
`(1, ∞)` it is `x^{−3/4}(θ(x) − 1)`, on `(0, 1)` it is `x^{−3/4}(θ(x) − x^{−1/2})`, which the theta
functional equation turns into `x^{−5/4}(θ(1/x) − 1)`.  The theta tail obeys
`0 ≤ θ(t) − 1 ≤ 4 e^{−πt}` for `t ≥ 1`, so the whole integrand is bounded by `4 e^{−x}` on
`(0, ∞)`, whose integral is `4`.  Hence `0 ≤ Λ₀(¼) ≤ 4`, so `0 ≤ completedRiemannZeta₀ (½) ≤ 2`,
and

```text
ξ(½) = (½ · (−½) · Λ₀(½) + 1) / 2 = ½ − Λ₀(½)/8 ≥ ½ − ¼ > 0.
```

This discharges the hypothesis `riemannXi (½) ≠ 0` carried by `FosterTanks` and `OffLineJensen`.
The true value is `ξ(½) ≈ 0.4971`; the bound here is crude on purpose.  No zero is mentioned.

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.XiCentre

open Complex Real Set MeasureTheory HurwitzZeta
open Soma.Holonics.RH.RiemannXi

/-! ## The theta tail -/

/-- The theta kernel at `a = 0`, as a real function. -/
abbrev θ (t : ℝ) : ℝ := evenKernel 0 t

/-- The tail of the theta kernel, as a sum over the nonzero integers. -/
theorem hasSum_theta_sub_one {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ => if n = 0 then 0 else rexp (-π * (n : ℝ) ^ 2 * t)) (θ t - 1) := by
  have h := hasSum_int_evenKernel₀ (0 : ℝ) ht
  simp only [add_zero, QuotientAddGroup.mk_zero, eq_self_iff_true, if_true, Int.cast_eq_zero] at h
  exact h

/-- **The theta tail is nonnegative.** -/
theorem theta_sub_one_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ θ t - 1 :=
  (hasSum_theta_sub_one ht).nonneg fun n => by
    split_ifs
    · exact le_rfl
    · exact (Real.exp_pos _).le

/-- The geometric majorant of the theta tail. -/
def tailMajorant (t : ℝ) (n : ℤ) : ℝ :=
  if n = 0 then 0 else rexp (-π * t) * rexp (-π) ^ (n.natAbs - 1)

theorem hasSum_tailMajorant (t : ℝ) :
    HasSum (tailMajorant t) (2 * (rexp (-π * t) / (1 - rexp (-π)))) := by
  have hr : rexp (-π) < 1 := by
    have : rexp (-π) < rexp 0 := Real.exp_lt_exp.mpr (by linarith [Real.pi_pos])
    simpa using this
  have hr0 : 0 ≤ rexp (-π) := (Real.exp_pos _).le
  have hgeom : HasSum (fun m : ℕ => rexp (-π * t) * rexp (-π) ^ m)
      (rexp (-π * t) / (1 - rexp (-π))) := by
    have := (hasSum_geometric_of_lt_one hr0 hr).mul_left (rexp (-π * t))
    simpa [div_eq_mul_inv] using this
  have hpos : HasSum (fun m : ℕ => tailMajorant t (m : ℤ)) (rexp (-π * t) / (1 - rexp (-π))) := by
    have h1 : HasSum (fun m : ℕ => tailMajorant t ((m + 1 : ℕ) : ℤ))
        (rexp (-π * t) / (1 - rexp (-π))) := by
      refine hgeom.congr_fun ?_
      intro m
      have hm1 : ((m + 1 : ℕ) : ℤ) ≠ 0 := by omega
      have hm2 : ((m + 1 : ℕ) : ℤ).natAbs - 1 = m := by omega
      simp only [tailMajorant, if_neg hm1, hm2]
    have h2 := (hasSum_nat_add_iff (f := fun m : ℕ => tailMajorant t (m : ℤ)) 1).mp h1
    have h0 : tailMajorant t ((0 : ℕ) : ℤ) = 0 := by simp [tailMajorant]
    rw [Finset.sum_range_one, h0, add_zero] at h2
    exact h2
  have hneg : HasSum (fun m : ℕ => tailMajorant t (-((m : ℤ) + 1)))
      (rexp (-π * t) / (1 - rexp (-π))) := by
    refine hgeom.congr_fun ?_
    intro m
    have hm1 : (-((m : ℤ) + 1)) ≠ 0 := by omega
    have hm2 : (-((m : ℤ) + 1)).natAbs - 1 = m := by omega
    simp only [tailMajorant, if_neg hm1, hm2]
  have := hpos.of_nat_of_neg_add_one hneg
  convert this using 1
  ring

/-- **The theta tail is at most `4 e^{−πt}` for `t ≥ 1`.** -/
theorem theta_sub_one_le {t : ℝ} (ht : 1 ≤ t) : θ t - 1 ≤ 4 * rexp (-π * t) := by
  have ht0 : 0 < t := by linarith
  have hle : ∀ n : ℤ, (if n = 0 then (0 : ℝ) else rexp (-π * (n : ℝ) ^ 2 * t)) ≤
      tailMajorant t n := by
    intro n
    unfold tailMajorant
    split_ifs with h0
    · exact le_rfl
    · rw [← Real.exp_nat_mul, ← Real.exp_add, Real.exp_le_exp]
      have hn : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs h0
        exact_mod_cast this
      have hnat : ((n.natAbs - 1 : ℕ) : ℝ) = |(n : ℝ)| - 1 := by
        have h1 : 1 ≤ n.natAbs := Int.natAbs_pos.mpr h0
        rw [Nat.cast_sub h1, Nat.cast_natAbs, Int.cast_abs]
        simp
      rw [hnat]
      have hsq : (n : ℝ) ^ 2 = |(n : ℝ)| ^ 2 := (sq_abs _).symm
      rw [hsq]
      have h1 : 0 ≤ |(n : ℝ)| - 1 := sub_nonneg.mpr hn
      have h2 : 0 ≤ (|(n : ℝ)| + 1) * t - 1 := by nlinarith
      have key : 0 ≤ (|(n : ℝ)| ^ 2 - 1) * t - (|(n : ℝ)| - 1) := by
        nlinarith [mul_nonneg h1 h2]
      nlinarith [mul_nonneg Real.pi_pos.le key]
  have := hasSum_le hle (hasSum_theta_sub_one ht0) (hasSum_tailMajorant t)
  refine this.trans ?_
  have hr : rexp (-π) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num), one_div, inv_inv]
    have := Real.add_one_le_exp π
    linarith [Real.pi_gt_three]
  have hden : 1 / 2 ≤ 1 - rexp (-π) := by linarith
  have hE : 0 ≤ rexp (-π * t) := (Real.exp_pos _).le
  calc 2 * (rexp (-π * t) / (1 - rexp (-π))) ≤ 2 * (rexp (-π * t) / (1 / 2)) := by
        gcongr
      _ = 4 * rexp (-π * t) := by ring

/-! ## The Mellin integrand at the symmetric point -/

/-- The modified theta kernel of the FE-pair, as a real function. -/
def kernel (x : ℝ) : ℝ :=
  (Ioi 1).indicator (fun x => θ x - 1) x +
    (Ioo 0 1).indicator (fun x => θ x - x ^ (-(1 / 2 : ℝ))) x

/-- The FE-pair's modified kernel is the coercion of `kernel`. -/
theorem f_modif_eq (x : ℝ) : (hurwitzEvenFEPair 0).f_modif x = (kernel x : ℂ) := by
  unfold WeakFEPair.f_modif kernel
  have hf : (hurwitzEvenFEPair 0).f = ofReal ∘ evenKernel 0 := rfl
  have hf₀ : (hurwitzEvenFEPair 0).f₀ = 1 := by simp [hurwitzEvenFEPair]
  have hg₀ : (hurwitzEvenFEPair 0).g₀ = 1 := rfl
  have hε : (hurwitzEvenFEPair 0).ε = 1 := rfl
  have hk : (hurwitzEvenFEPair 0).k = 1 / 2 := rfl
  simp only [hf, hf₀, hg₀, hε, hk, Function.comp, Pi.add_apply, smul_eq_mul, one_mul, mul_one]
  push_cast
  by_cases h1 : x ∈ Ioi 1
  · have h2 : x ∉ Ioo 0 1 := fun h => by
      simp only [mem_Ioi] at h1
      exact absurd h.2 (not_lt.mpr h1.le)
    simp [indicator_of_mem h1, indicator_of_notMem h2]
  · by_cases h2 : x ∈ Ioo 0 1
    · simp [indicator_of_notMem h1, indicator_of_mem h2]
    · simp [indicator_of_notMem h1, indicator_of_notMem h2]

/-- **The kernel is nonnegative.** -/
theorem kernel_nonneg (x : ℝ) : 0 ≤ kernel x := by
  unfold kernel
  apply add_nonneg
  · by_cases h : x ∈ Ioi 1
    · rw [indicator_of_mem h]
      exact theta_sub_one_nonneg (by simp only [mem_Ioi] at h; linarith)
    · rw [indicator_of_notMem h]
  · by_cases h : x ∈ Ioo 0 1
    · rw [indicator_of_mem h]
      obtain ⟨hx0, hx1⟩ := h
      have hfe : θ x = x ^ (-(1 / 2 : ℝ)) * θ (1 / x) := by
        have := evenKernel_functional_equation 0 x
        rw [← evenKernel_eq_cosKernel_of_zero, one_div (x ^ (1 / 2 : ℝ)),
          ← Real.rpow_neg hx0.le] at this
        exact this
      have hfe' : θ x - x ^ (-(1 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) * (θ (1 / x) - 1) := by
        rw [hfe]
        ring
      rw [hfe']
      apply mul_nonneg (Real.rpow_nonneg hx0.le _)
      exact theta_sub_one_nonneg (by positivity)
    · rw [indicator_of_notMem h]

/-- The elementary inequality `y^{5/4} e^{−πy} ≤ e^{−π}` for `y ≥ 1`, in the form used on
`(0, 1)`: `x^{−5/4} e^{−π/x} ≤ e^{−π}`. -/
theorem rpow_mul_exp_le {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x)) ≤ rexp (-π) := by
  rw [Real.rpow_def_of_pos hx0, ← Real.exp_add, Real.exp_le_exp]
  have hlog : Real.log (1 / x) ≤ 1 / x - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div one_ne_zero hx0.ne', Real.log_one] at hlog
  have hπ : (5 / 4 : ℝ) ≤ π := by linarith [Real.pi_gt_three]
  have hx' : 0 ≤ 1 / x - 1 := by
    rw [sub_nonneg, le_div_iff₀ hx0]
    linarith
  nlinarith

/-- **The weighted kernel is bounded by `4 e^{−x}` on `(0, ∞)`.** -/
theorem weighted_kernel_le {x : ℝ} (hx : 0 < x) :
    x ^ (-(3 / 4 : ℝ)) * kernel x ≤ 4 * rexp (-x) := by
  unfold kernel
  rcases lt_trichotomy x 1 with h | h | h
  · have h1 : x ∉ Ioi 1 := by simp [mem_Ioi]; linarith
    have h2 : x ∈ Ioo 0 1 := ⟨hx, h⟩
    rw [indicator_of_notMem h1, indicator_of_mem h2, zero_add]
    have hfe : θ x = x ^ (-(1 / 2 : ℝ)) * θ (1 / x) := by
      have := evenKernel_functional_equation 0 x
      rw [← evenKernel_eq_cosKernel_of_zero, one_div (x ^ (1 / 2 : ℝ)),
        ← Real.rpow_neg hx.le] at this
      exact this
    have hfe' : θ x - x ^ (-(1 / 2 : ℝ)) = x ^ (-(1 / 2 : ℝ)) * (θ (1 / x) - 1) := by
      rw [hfe]
      ring
    rw [hfe', ← mul_assoc, ← Real.rpow_add hx]
    have hy : 1 ≤ 1 / x := by
      rw [le_div_iff₀ hx]
      linarith
    have htail := theta_sub_one_le hy
    have hpow : 0 ≤ x ^ (-(3 / 4 : ℝ) + -(1 / 2 : ℝ)) := Real.rpow_nonneg hx.le _
    calc x ^ (-(3 / 4 : ℝ) + -(1 / 2 : ℝ)) * (θ (1 / x) - 1)
        ≤ x ^ (-(3 / 4 : ℝ) + -(1 / 2 : ℝ)) * (4 * rexp (-π * (1 / x))) :=
          mul_le_mul_of_nonneg_left htail hpow
      _ = 4 * (x ^ (-(5 / 4 : ℝ)) * rexp (-π * (1 / x))) := by
          rw [show (-(3 / 4 : ℝ) + -(1 / 2 : ℝ)) = -(5 / 4 : ℝ) by norm_num]
          ring
      _ ≤ 4 * rexp (-π) := by
          gcongr
          exact rpow_mul_exp_le hx h
      _ ≤ 4 * rexp (-x) := by
          gcongr
          linarith [Real.pi_gt_three]
  · subst h
    simp
    all_goals positivity
  · have h1 : x ∈ Ioi 1 := h
    have h2 : x ∉ Ioo 0 1 := fun hh => absurd hh.2 (not_lt.mpr h.le)
    rw [indicator_of_mem h1, indicator_of_notMem h2, add_zero]
    have htail := theta_sub_one_le h.le
    have hpow1 : x ^ (-(3 / 4 : ℝ)) ≤ 1 := by
      rw [Real.rpow_neg hx.le]
      exact inv_le_one_of_one_le₀ (Real.one_le_rpow h.le (by norm_num))
    have hpow0 : 0 ≤ x ^ (-(3 / 4 : ℝ)) := Real.rpow_nonneg hx.le _
    have hnn : 0 ≤ θ x - 1 := theta_sub_one_nonneg hx
    calc x ^ (-(3 / 4 : ℝ)) * (θ x - 1) ≤ 1 * (θ x - 1) := by gcongr
      _ = θ x - 1 := one_mul _
      _ ≤ 4 * rexp (-π * x) := htail
      _ ≤ 4 * rexp (-x) := by
          gcongr
          nlinarith [Real.pi_gt_three]

/-! ## The value -/

/-- The real Mellin integral at the symmetric point. -/
def I₀ : ℝ := ∫ x in Ioi (0 : ℝ), x ^ (-(3 / 4 : ℝ)) * kernel x

/-- The Mellin transform of the modified kernel at `¼` is a real integral. -/
theorem lambda₀_quarter_eq : (hurwitzEvenFEPair 0).Λ₀ (1 / 4) = (I₀ : ℂ) := by
  unfold WeakFEPair.Λ₀ mellin I₀
  calc ∫ t in Ioi (0 : ℝ), (t : ℂ) ^ ((1 / 4 : ℂ) - 1) • (hurwitzEvenFEPair 0).f_modif t
      = ∫ t in Ioi (0 : ℝ), ((t ^ (-(3 / 4 : ℝ)) * kernel t : ℝ) : ℂ) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x hx
        have hx0 : 0 ≤ x := le_of_lt hx
        simp only
        rw [f_modif_eq, smul_eq_mul, ofReal_mul, ofReal_cpow hx0]
        congr 2
        push_cast
        norm_num
    _ = _ := integral_complex_ofReal

theorem mellinConvergent_quarter : MellinConvergent (hurwitzEvenFEPair 0).f_modif (1 / 4) :=
  ((hurwitzEvenFEPair 0).isStrongFEPair_toStrongFEPair.hasMellin (1 / 4)).1

/-- The real integrand is integrable on `(0, ∞)`. -/
theorem integrableOn_weighted_kernel :
    IntegrableOn (fun x : ℝ => x ^ (-(3 / 4 : ℝ)) * kernel x) (Ioi 0) := by
  have h := mellinConvergent_quarter
  unfold MellinConvergent at h
  have hcongr : EqOn (fun t : ℝ => (t : ℂ) ^ ((1 / 4 : ℂ) - 1) • (hurwitzEvenFEPair 0).f_modif t)
      (fun t : ℝ => ((t ^ (-(3 / 4 : ℝ)) * kernel t : ℝ) : ℂ)) (Ioi 0) := by
    intro t ht
    have ht0 : 0 ≤ t := le_of_lt ht
    simp only
    rw [f_modif_eq, smul_eq_mul, ofReal_mul, ofReal_cpow ht0]
    congr 2
    push_cast
    norm_num
  have h' : IntegrableOn (fun t : ℝ => ((t ^ (-(3 / 4 : ℝ)) * kernel t : ℝ) : ℂ)) (Ioi 0) :=
    h.congr_fun hcongr measurableSet_Ioi
  have hre := h'.re
  exact (by simpa using hre :
    Integrable (fun x : ℝ => x ^ (-(3 / 4 : ℝ)) * kernel x) (volume.restrict (Ioi 0)))

/-- **`0 ≤ Λ₀(¼) ≤ 4`** as a real number. -/
theorem lambda₀_quarter_bounds : 0 ≤ I₀ ∧ I₀ ≤ 4 := by
  unfold I₀
  constructor
  · apply setIntegral_nonneg measurableSet_Ioi
    intro x hx
    exact mul_nonneg (Real.rpow_nonneg (le_of_lt hx) _) (kernel_nonneg x)
  · have hmaj : IntegrableOn (fun x : ℝ => 4 * rexp (-x)) (Ioi 0) :=
      (integrableOn_exp_neg_Ioi 0).const_mul 4
    calc ∫ x in Ioi (0 : ℝ), x ^ (-(3 / 4 : ℝ)) * kernel x
        ≤ ∫ x in Ioi (0 : ℝ), 4 * rexp (-x) := by
          apply setIntegral_mono_on integrableOn_weighted_kernel hmaj measurableSet_Ioi
          intro x hx
          exact weighted_kernel_le hx
      _ = 4 * ∫ x in Ioi 0, rexp (-x) := by rw [integral_const_mul]
      _ = 4 := by rw [integral_exp_neg_Ioi_zero, mul_one]

/-- **The completed zeta at `½` lies in `[0, 2]`.** -/
theorem completedRiemannZeta₀_one_half_bounds :
    ∃ v : ℝ, 0 ≤ v ∧ v ≤ 2 ∧ completedRiemannZeta₀ (1 / 2) = (v : ℂ) := by
  refine ⟨I₀ / 2, ?_, ?_, ?_⟩
  · linarith [lambda₀_quarter_bounds.1]
  · linarith [lambda₀_quarter_bounds.2]
  · rw [completedRiemannZeta₀, completedHurwitzZetaEven₀]
    have h : ((1 / 2 : ℂ) / 2) = 1 / 4 := by norm_num
    rw [h, lambda₀_quarter_eq]
    push_cast
    ring

/-- **`ξ(½)` is positive**, hence nonzero. -/
theorem riemannXi_one_half_pos : ∃ v : ℝ, 0 < v ∧ riemannXi (1 / 2) = (v : ℂ) := by
  obtain ⟨v, hv0, hv2, hv⟩ := completedRiemannZeta₀_one_half_bounds
  refine ⟨(1 - v / 4) / 2, by linarith, ?_⟩
  unfold riemannXi
  rw [hv]
  push_cast
  ring

/-- **The centre value is nonzero**: the hypothesis carried by `FosterTanks` and
`OffLineJensen` is discharged. -/
theorem riemannXi_one_half_ne_zero : riemannXi (1 / 2) ≠ 0 := by
  obtain ⟨v, hv, h⟩ := riemannXi_one_half_pos
  rw [h]
  exact_mod_cast hv.ne'

end Soma.Holonics.RH.XiCentre
