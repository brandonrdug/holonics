import ElementaryHolonics.RH.WeightSymmetry

/-!
# Order-one growth, with no Stirling estimate and no maximum principle

`MellinHorizon` reduced the entire size of `Λ₀` to one real function — `‖Λ₀(s)‖ ≤ W(Re s/2)`, the
height contributing pure phase.  `WeightSymmetry` showed that function is its own reflection.  This
file bounds it.

The weight splits at one and each half is elementary:

* **below one the exponent only helps** — `t^{σ−1} ≤ 1` there for `σ ≥ 1`, so that piece is a
  constant `W₀` independent of `σ`;
* **above one the kernel decays exponentially**, and the tail is then *exactly* Euler's integral:
  `∫₀^∞ t^{σ−1}e^{−pt} dt = (1/p)^σ·Γ(σ)`.

```text
W(σ) ≤ W₀ + C·(1/p)^σ·Γ(σ)        for σ ≥ 1
```

Mathlib supplies the decay only *eventually* (`isBigO_atTop_evenKernel_sub`); `theKernelDecays`
closes the compact middle by continuity, where `e^{−pt}` is bounded below.  The kernel's value at
`t = 1` is `0` by construction — the two indicators deliberately leave a gap — which is why that
point needs its own line.

So the whole growth of the completed zeta is the growth of a Gamma function **of half the
abscissa, and nothing whatever in the height direction.**  The stated absences this front carried
for days — no complex Stirling, no strip Phragmén–Lindelöf — were both true of the *names* and
both irrelevant: reflection gave the Gamma magnitude exactly, and the Mellin representation gave
the strip bound with no maximum principle at all.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section
namespace Soma.Holonics.RH.Growth

open Complex MeasureTheory Set Real Asymptotics HurwitzZeta
open _root_.Filter hiding ker
open Soma.Holonics.RH.MellinHorizon Soma.Holonics.RH.WeightSymmetry

/-- Above one the modified kernel is just `θ − 1`. -/
theorem theKernelAboveOne {t : ℝ} (ht : 1 < t) :
    ker t = ((evenKernel 0 t : ℝ) : ℂ) - 1 := by
  have h1 : t ∈ Ioi (1:ℝ) := ht
  have h2 : t ∉ Ioo (0:ℝ) 1 := by simp; intro _; linarith
  simp [ker, WeakFEPair.f_modif, Set.indicator_of_mem h1, Set.indicator_of_notMem h2,
    hurwitzEvenFEPair]

/-- Its magnitude above one, as a real absolute value. -/
theorem theKernelNormAboveOne {t : ℝ} (ht : 1 < t) : ‖ker t‖ = |evenKernel 0 t - 1| := by
  rw [theKernelAboveOne ht, ← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]

/-- The kernel vanishes at one, by construction — the two indicators deliberately leave a gap. -/
theorem theKernelVanishesAtOne : ker 1 = 0 := by
  have h1 : (1:ℝ) ∉ Ioi (1:ℝ) := by simp
  have h2 : (1:ℝ) ∉ Ioo (0:ℝ) 1 := by simp
  simp [ker, WeakFEPair.f_modif, Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

/-- **THE KERNEL DECAYS EXPONENTIALLY ABOVE ONE**, with an explicit constant.  Mathlib gives the
decay only *eventually*; the compact middle is closed by continuity, and `e^{-pt}` is bounded
below there. -/
theorem theKernelDecays :
    ∃ C p : ℝ, 0 < p ∧ 0 ≤ C ∧ ∀ t : ℝ, 1 ≤ t → ‖ker t‖ ≤ C * Real.exp (-p * t) := by
  obtain ⟨p, hp, hO⟩ := isBigO_atTop_evenKernel_sub 0
  obtain ⟨C₀, hC₀⟩ := hO.bound
  obtain ⟨T, hT⟩ := eventually_atTop.mp hC₀
  set T' : ℝ := max T 2 with hT'def
  have hT'2 : (2:ℝ) ≤ T' := le_max_right _ _
  have hsub : Icc (1:ℝ) T' ⊆ Ioi 0 := fun x hx => lt_of_lt_of_le zero_lt_one hx.1
  have hcont : ContinuousOn (fun t : ℝ => |evenKernel 0 t - 1|) (Icc 1 T') :=
    (((continuousOn_evenKernel 0).mono hsub).sub continuousOn_const).abs
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  have hMle : ∀ x ∈ Icc (1:ℝ) T', |evenKernel 0 x - 1| ≤ M := by
    intro x hx; simpa using hM x hx
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hMle 1 ⟨le_refl 1, by linarith⟩)
  refine ⟨max C₀ (M * Real.exp (p * T')), p, hp, ?_, ?_⟩
  · exact le_trans (le_trans hM0
      (le_mul_of_one_le_right hM0 (Real.one_le_exp (by positivity)))) (le_max_right _ _)
  intro t ht
  rcases le_or_gt t T' with hle | hgt
  · have hb : ‖ker t‖ ≤ M := by
      rcases eq_or_lt_of_le ht with h1 | h1
      · rw [← h1, theKernelVanishesAtOne]; simpa using hM0
      · rw [theKernelNormAboveOne h1]; exact hMle t ⟨ht, hle⟩
    calc ‖ker t‖ ≤ M := hb
      _ = M * Real.exp (p * T') * Real.exp (-(p * T')) := by
          rw [mul_assoc, ← Real.exp_add]; simp
      _ ≤ max C₀ (M * Real.exp (p * T')) * Real.exp (-p * t) := by
          have h1 : Real.exp (-(p * T')) ≤ Real.exp (-p * t) := by
            apply Real.exp_le_exp.mpr; nlinarith [hp, hle]
          have h2 : (0:ℝ) ≤ M * Real.exp (p * T') := by positivity
          exact mul_le_mul (le_max_right _ _) h1 (Real.exp_pos _).le
            (le_trans h2 (le_max_right _ _))
  · have hTt : T ≤ t := le_trans (le_max_left _ _) hgt.le
    have hb := hT t hTt
    simp only [if_pos rfl] at hb
    rw [theKernelNormAboveOne (by linarith : (1:ℝ) < t), ← Real.norm_eq_abs]
    calc ‖evenKernel 0 t - 1‖ ≤ C₀ * ‖Real.exp (-p * t)‖ := hb
      _ = C₀ * Real.exp (-p * t) := by rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      _ ≤ max C₀ (M * Real.exp (p * T')) * Real.exp (-p * t) :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-! ## The weight splits at one, and the tail is a Gamma integral -/

/-- `Ioi 0` splits at one. -/
theorem theSplitAtOne : Ioi (0:ℝ) = Ioo 0 1 ∪ Ici 1 := by
  ext t
  simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
  constructor
  · intro ht
    rcases lt_or_ge t 1 with h | h
    · exact Or.inl ⟨ht, h⟩
    · exact Or.inr h
  · rintro (⟨h, _⟩ | h)
    · exact h
    · linarith

/-- **THE WEIGHT IS BOUNDED BY A CONSTANT PLUS A GAMMA FACTOR.**  Below one the exponent only
helps, since `t^{σ−1} ≤ 1` there for `σ ≥ 1`; above one the kernel's exponential decay turns the
tail into Euler's integral exactly.  So

```text
W(σ) ≤ W₀ + C·(1/p)^σ·Γ(σ)   for σ ≥ 1
```

with `W₀` the near-zero part and `C, p` the decay constants — **the entire growth of `Λ₀` in one
inequality**, and it is order one because `Γ(σ)` is. -/
theorem theWeightHasGammaGrowth :
    ∃ W₀ C p : ℝ, 0 < p ∧ 0 ≤ C ∧ 0 ≤ W₀ ∧
      ∀ σ : ℝ, 1 ≤ σ → mellinWeight ker σ ≤ W₀ + C * (1 / p) ^ σ * Real.Gamma σ := by
  obtain ⟨C, p, hp, hC, hdecay⟩ := theKernelDecays
  refine ⟨∫ t in Ioo (0:ℝ) 1, ‖ker t‖, C, p, hp, hC, ?_, ?_⟩
  · exact setIntegral_nonneg measurableSet_Ioo (fun t _ => norm_nonneg _)
  intro σ hσ
  have hσ0 : (0:ℝ) < σ := lt_of_lt_of_le zero_lt_one hσ
  have hconv : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖ker t‖) (Ioi 0) :=
    theWeightIntegrandIsIntegrable (theEvenKernelConverges ((σ : ℝ) : ℂ))
  have hdisj : Disjoint (Ioo (0:ℝ) 1) (Ici 1) := by
    rw [Set.disjoint_left]; rintro t ⟨_, h1⟩ h2; exact absurd h2 (not_le.mpr h1)
  have hsplit : mellinWeight ker σ
      = (∫ t in Ioo (0:ℝ) 1, t ^ (σ - 1) * ‖ker t‖) + ∫ t in Ici (1:ℝ), t ^ (σ - 1) * ‖ker t‖ := by
    rw [mellinWeight, theSplitAtOne]
    exact setIntegral_union hdisj measurableSet_Ici
      (hconv.mono_set (by rw [theSplitAtOne]; exact Set.subset_union_left))
      (hconv.mono_set (by rw [theSplitAtOne]; exact Set.subset_union_right))
  rw [hsplit]
  gcongr ?_ + ?_
  · -- below one the exponent only helps
    refine setIntegral_mono_on (hconv.mono_set (by rw [theSplitAtOne]; exact Set.subset_union_left))
      ?_ measurableSet_Ioo (fun t ht => ?_)
    · have h1 : IntegrableOn (fun t : ℝ => t ^ ((1:ℝ) - 1) * ‖ker t‖) (Ioi 0) :=
        theWeightIntegrandIsIntegrable (theEvenKernelConverges (((1:ℝ) : ℝ) : ℂ))
      have h2 : IntegrableOn (fun t : ℝ => ‖ker t‖) (Ioi 0) := by
        refine MeasureTheory.IntegrableOn.congr_fun h1 (fun t ht => ?_) measurableSet_Ioi
        have htp : (0:ℝ) < t := ht
        rw [sub_self, Real.rpow_zero, one_mul]
      exact h2.mono_set (by rw [theSplitAtOne]; exact Set.subset_union_left)
    · have h1 : t ^ (σ - 1) ≤ 1 := Real.rpow_le_one ht.1.le ht.2.le (by linarith)
      have h2 : (0:ℝ) ≤ ‖ker t‖ := norm_nonneg _
      calc t ^ (σ - 1) * ‖ker t‖ ≤ 1 * ‖ker t‖ := by
            exact mul_le_mul_of_nonneg_right h1 h2
        _ = ‖ker t‖ := one_mul _
  · -- the tail is Euler's integral
    have hint : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * Real.exp (-(p * t))) (Ioi 0) := by
      have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := σ - 1) (b := p)
        (by linarith) (by norm_num) hp
      simpa using h
    have hsub : Ici (1:ℝ) ⊆ Ioi (0:ℝ) := by
      intro t ht
      simp only [Set.mem_Ici] at ht
      simp only [Set.mem_Ioi]
      linarith
    have hintC : IntegrableOn (fun t : ℝ => C * (t ^ (σ - 1) * Real.exp (-(p * t)))) (Ioi 0) :=
      hint.const_mul C
    calc ∫ t in Ici (1:ℝ), t ^ (σ - 1) * ‖ker t‖
        ≤ ∫ t in Ici (1:ℝ), C * (t ^ (σ - 1) * Real.exp (-(p * t))) := by
          have hleft : IntegrableOn (fun t : ℝ => t ^ (σ - 1) * ‖ker t‖) (Ici 1) :=
            hconv.mono_set (by rw [theSplitAtOne]; exact Set.subset_union_right)
          refine setIntegral_mono_on hleft (hintC.mono_set hsub) measurableSet_Ici
            (fun t ht => ?_)
          simp only [Set.mem_Ici] at ht
          have htp : (0:ℝ) < t := by linarith
          have hd := hdecay t ht
          have hrp : (0:ℝ) < t ^ (σ - 1) := Real.rpow_pos_of_pos htp _
          have hexp : Real.exp (-p * t) = Real.exp (-(p * t)) := by ring_nf
          rw [hexp] at hd
          nlinarith [hd, hrp]
      _ ≤ ∫ t in Ioi (0:ℝ), C * (t ^ (σ - 1) * Real.exp (-(p * t))) := by
          refine setIntegral_mono_set hintC ?_ (HasSubset.Subset.eventuallyLE hsub)
          filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
          have htp : (0:ℝ) < t := ht
          positivity
      _ = C * ((1 / p) ^ σ * Real.Gamma σ) := by
          rw [integral_const_mul, Real.integral_rpow_mul_exp_neg_mul_Ioi hσ0 hp]
      _ = C * (1 / p) ^ σ * Real.Gamma σ := by ring

/-! ## Hence order one -/

/-- **THE COMPLETED ZETA HAS ORDER-ONE GROWTH.**  `‖Λ₀(s)‖ ≤ W(Re s/2)`, and the weight is bounded
by a constant plus `C(1/p)^σΓ(σ)`.  So the whole growth of the completed zeta is the growth of a
Gamma function of half the abscissa — **and nothing at all in the height direction.** -/
theorem theCompletedZetaHasGammaGrowth :
    ∃ W₀ C p : ℝ, 0 < p ∧ 0 ≤ C ∧ 0 ≤ W₀ ∧
      ∀ s : ℂ, 2 ≤ s.re →
        ‖completedRiemannZeta₀ s‖ ≤ W₀ + C * (1 / p) ^ (s.re / 2) * Real.Gamma (s.re / 2) := by
  obtain ⟨W₀, C, p, hp, hC, hW, hbound⟩ := theWeightHasGammaGrowth
  refine ⟨W₀, C, p, hp, hC, hW, fun s hs => ?_⟩
  exact le_trans (theBoundAtAnyPoint s) (hbound (s.re / 2) (by linarith))

end Soma.Holonics.RH.Growth
