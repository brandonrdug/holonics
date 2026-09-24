import ElementaryHolonics.Millennium.NavierStokesYoungClosure

/-!
# The terminal-tail closure: the fourth moment is bounded by its value at the start of the tail

On the nonzero modes of the cube of radius `N`, the closure form of the fourth-moment Riccati has
a forcing paid by the eleventh moment over `(N+1)⁵`:

```text
M₄(F_N)' ≤ (3K(t)/(ν(2π)²)) · M₄(F_N) + ν (2π)² · W₁₁ / (N+1)⁵.
```

One Grönwall passage with constant forcing, then `N → ∞`, returns on every `[s, τ] ⊂ (0, T)`

```text
W₄(τ) ≤ W₄(s) · exp(b (τ − s))
```

whenever the closure drive is at most `b` and the eleventh moment is finite on `[s, τ]`.  The
premise is a bound on the closure drive along the terminal tail (the second moment and the zero
mode) together with interior finiteness; the conclusion is `WeightedTailEnergyControl`, hence
`StatementB`.
-/

noncomputable section

open Set Filter Topology MeasureTheory
open scoped Finset

namespace Soma.Holonics.Millennium.NavierStokesMomentClosure

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFullStrain
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionFiniteBandBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionPhysicalBridge
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionSourceModulus
open Soma.Holonics.Millennium.NavierStokesCoordinateJacobianFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesH2StorageDissipationPayment
open Soma.Holonics.Millennium.NavierStokesAlignedStrainBudget
open Soma.Holonics.Millennium.NavierStokesModalRiccati
open Soma.Holonics.Millennium.NavierStokesHalfRadiusReach
open Soma.Holonics.Millennium.NavierStokesMomentSwap
open Soma.Holonics.Millennium.NavierStokesMomentGap
open Soma.Holonics.Millennium.NavierStokesFourthMomentRiccati
open Soma.Holonics.Millennium.NavierStokesWeightedYoung
open Soma.Holonics.Millennium.NavierStokesMomentInterpolation
open Soma.Holonics.Millennium.NavierStokesSixthYoung
open Soma.Holonics.Millennium.NavierStokesYoungRiccati
open Soma.Holonics.Millennium.NavierStokesIncoherentBandMass
open Soma.Holonics.Millennium.NavierStokesWeightedTailEnergy
open Soma.Holonics.Millennium.NavierStokesYoungClosure

/-! ## Grönwall with a constant forcing -/

/-- **Grönwall with a constant forcing.**  `f' ≤ b f + G` on `[s, τ]` with `0 ≤ b`, `0 ≤ G`
returns `f τ ≤ (f s + G (τ − s)) exp(b (τ − s))`. -/
theorem le_exp_of_hasDerivAt_le {f : ℝ → ℝ} {b G s τ : ℝ} (hb : 0 ≤ b) (hG : 0 ≤ G) (hsτ : s ≤ τ)
    (hf : ∀ σ ∈ Icc s τ, ∃ D, HasDerivAt f D σ ∧ D ≤ b * f σ + G) :
    f τ ≤ (f s + G * (τ - s)) * Real.exp (b * (τ - s)) := by
  set h : ℝ → ℝ := fun σ ↦ f σ * Real.exp (-(b * (σ - s))) - G * σ with hh
  have hexp : ∀ σ : ℝ, HasDerivAt (fun σ ↦ Real.exp (-(b * (σ - s))))
      (-b * Real.exp (-(b * (σ - s)))) σ := by
    intro σ
    have h1 : HasDerivAt (fun σ ↦ -(b * (σ - s))) (-b) σ := by
      have h0 : HasDerivAt (fun σ ↦ b * (σ - s)) (b * 1) σ :=
        ((hasDerivAt_id σ).sub_const s).const_mul b
      exact h0.neg.congr_deriv (by ring)
    have h2 := h1.exp
    convert h2 using 1
    ring
  have hderivAt : ∀ σ ∈ Icc s τ, ∃ D, HasDerivAt h D σ ∧ D ≤ 0 := by
    intro σ hσ
    obtain ⟨D, hD, hle⟩ := hf σ hσ
    refine ⟨D * Real.exp (-(b * (σ - s))) + f σ * (-b * Real.exp (-(b * (σ - s)))) - G * 1,
      (hD.mul (hexp σ)).sub ((hasDerivAt_id σ).const_mul G), ?_⟩
    have hepos : 0 < Real.exp (-(b * (σ - s))) := Real.exp_pos _
    have he1 : Real.exp (-(b * (σ - s))) ≤ 1 := by
      have : Real.exp (-(b * (σ - s))) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr (by nlinarith [hσ.1])
      simpa using this
    have h1 : (D - b * f σ) * Real.exp (-(b * (σ - s))) ≤ G * Real.exp (-(b * (σ - s))) :=
      mul_le_mul_of_nonneg_right (by linarith) hepos.le
    have h2 : G * Real.exp (-(b * (σ - s))) ≤ G := mul_le_of_le_one_right hG he1
    nlinarith [h1, h2]
  have hanti : AntitoneOn h (Icc s τ) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc s τ) ?_ ?_ ?_
    · intro σ hσ
      obtain ⟨D, hD, _⟩ := hderivAt σ hσ
      exact hD.continuousAt.continuousWithinAt
    · intro σ hσ
      rw [interior_Icc] at hσ
      obtain ⟨D, hD, _⟩ := hderivAt σ (Ioo_subset_Icc_self hσ)
      exact hD.differentiableAt.differentiableWithinAt
    · intro σ hσ
      rw [interior_Icc] at hσ
      obtain ⟨D, hD, hD0⟩ := hderivAt σ (Ioo_subset_Icc_self hσ)
      rw [hD.deriv]
      exact hD0
  have hmono := hanti ⟨le_rfl, hsτ⟩ ⟨hsτ, le_rfl⟩ hsτ
  have hhs : h s = f s - G * s := by simp [hh]
  have hhτ : h τ = f τ * Real.exp (-(b * (τ - s))) - G * τ := rfl
  rw [hhs, hhτ] at hmono
  have hkey : f τ * Real.exp (-(b * (τ - s))) ≤ f s + G * (τ - s) := by linarith
  have hE : Real.exp (-(b * (τ - s))) * Real.exp (b * (τ - s)) = 1 := by
    rw [← Real.exp_add]; simp
  calc f τ = f τ * Real.exp (-(b * (τ - s))) * Real.exp (b * (τ - s)) := by
        rw [mul_assoc, hE, mul_one]
    _ ≤ (f s + G * (τ - s)) * Real.exp (b * (τ - s)) :=
        mul_le_mul_of_nonneg_right hkey (Real.exp_pos _).le

/-! ## The cube family -/

variable {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
  {pressure : PressureField}
  (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)

/-- The nonzero modes of the cube of radius `N`. -/
def cubeFamily (N : ℕ) : Finset SpatialFrequency := (frequencyCube N).erase 0

theorem one_le_frequencySup_of_mem_cubeFamily {N : ℕ} {k : SpatialFrequency}
    (hk : k ∈ cubeFamily N) : 1 ≤ frequencySup k :=
  one_le_frequencySup_of_ne_zero (Finset.ne_of_mem_erase hk)

theorem frequencySup_zero : frequencySup (0 : SpatialFrequency) = 0 :=
  le_antisymm (Finset.sup_le fun c _ ↦ by simp) (Nat.zero_le _)

theorem momentPop_zero (w : ℕ) (hw : 1 ≤ w) (τ : ℝ) :
    momentPop (velocity := velocity) w τ 0 = 0 := by
  unfold momentPop
  rw [frequencySup_zero]
  simp [Nat.pos_iff_ne_zero.mp (by omega : 0 < w)]

theorem momentEnergy_eq_sum (w : ℕ) (F : Finset SpatialFrequency) (τ : ℝ) :
    momentEnergy (velocity := velocity) w F τ = ∑ k ∈ F, momentPop (velocity := velocity) w τ k :=
  rfl

theorem momentEnergy_nonneg (w : ℕ) (F : Finset SpatialFrequency) (τ : ℝ) :
    0 ≤ momentEnergy (velocity := velocity) w F τ :=
  Finset.sum_nonneg fun k _ ↦ momentPop_nonneg w τ k

theorem momentEnergy_four_le_six (N : ℕ) (τ : ℝ) :
    momentEnergy (velocity := velocity) 4 (cubeFamily N) τ ≤
      momentEnergy (velocity := velocity) 6 (cubeFamily N) τ := by
  rw [momentEnergy_eq_sum, momentEnergy_eq_sum]
  exact Finset.sum_le_sum fun k _ ↦ momentPop_le (by norm_num) (by norm_num) τ k

/-- **The sixth moment beyond the cube family is paid by the eleventh moment over `(N+1)⁵`.** -/
theorem moment_six_le (N : ℕ) (τ : ℝ) (hsum : Summable (eleventhMoment (velocity := velocity) τ)) :
    moment (velocity := velocity) 6 τ ≤ momentEnergy (velocity := velocity) 6 (cubeFamily N) τ +
      moment (velocity := velocity) 11 τ / ((N : ℝ) + 1) ^ 5 := by
  have hpt : ∀ q, momentPop (velocity := velocity) 6 τ q ≤
      (if q ∈ cubeFamily N then momentPop (velocity := velocity) 6 τ q else 0) +
        momentPop (velocity := velocity) 11 τ q / ((N : ℝ) + 1) ^ 5 := by
    intro q
    by_cases hq : q ∈ cubeFamily N
    · rw [if_pos hq]
      have h11 := momentPop_nonneg (velocity := velocity) 11 τ q
      have : 0 ≤ momentPop (velocity := velocity) 11 τ q / ((N : ℝ) + 1) ^ 5 := by positivity
      linarith
    · rw [if_neg hq, zero_add]
      by_cases h0 : q = 0
      · subst h0
        rw [momentPop_zero 6 (by norm_num), momentPop_zero 11 (by norm_num)]
        simp
      · have hN : N + 1 ≤ frequencySup q := by
          by_contra hlt
          push Not at hlt
          exact hq (Finset.mem_erase.mpr
            ⟨h0, (mem_frequencyCube_iff_frequencySup_le N q).mpr (by omega)⟩)
        unfold momentPop
        have hN' : ((N : ℝ) + 1) ≤ ((frequencySup q : ℕ) : ℝ) := by exact_mod_cast hN
        have hE := modalEnergy_nonneg (velocity := velocity) q τ
        rw [le_div_iff₀ (by positivity)]
        have h5 : ((N : ℝ) + 1) ^ 5 ≤ ((frequencySup q : ℕ) : ℝ) ^ 5 :=
          pow_le_pow_left₀ (by positivity) hN' 5
        calc ((frequencySup q : ℕ) : ℝ) ^ 6 * modalEnergy (velocity := velocity) q τ *
              ((N : ℝ) + 1) ^ 5
            ≤ ((frequencySup q : ℕ) : ℝ) ^ 6 * modalEnergy (velocity := velocity) q τ *
              ((frequencySup q : ℕ) : ℝ) ^ 5 :=
              mul_le_mul_of_nonneg_left h5 (mul_nonneg (by positivity) hE)
          _ = _ := by ring
  have hsum6 := summable_momentPop (velocity := velocity) (by norm_num : 1 ≤ 6) (by norm_num) τ hsum
  have hsum11 :=
    summable_momentPop (velocity := velocity) (by norm_num : 1 ≤ 11) (by norm_num) τ hsum
  have hsumA : Summable fun q ↦
      (if q ∈ cubeFamily N then momentPop (velocity := velocity) 6 τ q else 0) :=
    summable_of_ne_finset_zero (s := cubeFamily N) fun q hq ↦ if_neg hq
  have hsumB : Summable fun q ↦ momentPop (velocity := velocity) 11 τ q / ((N : ℝ) + 1) ^ 5 :=
    hsum11.div_const _
  calc moment (velocity := velocity) 6 τ = ∑' q, momentPop (velocity := velocity) 6 τ q := rfl
    _ ≤ ∑' q, ((if q ∈ cubeFamily N then momentPop (velocity := velocity) 6 τ q else 0) +
          momentPop (velocity := velocity) 11 τ q / ((N : ℝ) + 1) ^ 5) :=
        hsum6.tsum_le_tsum hpt (hsumA.add hsumB)
    _ = (∑' q, (if q ∈ cubeFamily N then momentPop (velocity := velocity) 6 τ q else 0)) +
          ∑' q, momentPop (velocity := velocity) 11 τ q / ((N : ℝ) + 1) ^ 5 :=
        hsumA.tsum_add hsumB
    _ = _ := by
        rw [tsum_eq_sum (s := cubeFamily N) (fun q hq ↦ if_neg hq), tsum_div_const,
          momentEnergy_eq_sum]
        congr 1
        exact Finset.sum_congr rfl fun q hq ↦ if_pos hq

/-! ## The closure drive and the cube-family Riccati -/

/-- The closure drive: `3 K(t) / (ν (2π)²)`. -/
def closureDrive (t : Ioo 0 T) : ℝ :=
  3 * closureCoefficient (velocity := velocity) solution t t.1 / (nu * (2 * Real.pi) ^ 2)

/-- **The cube-family Riccati with vanishing forcing.** -/
theorem momentEnergy_cubeFamily_riccati (hnu : 0 < nu) (N : ℕ) (t : Ioo 0 T)
    (hsum : Summable (eleventhMoment (velocity := velocity) t.1)) :
    ∃ D : ℝ, HasDerivAt (momentEnergy (velocity := velocity) 4 (cubeFamily N)) D t.1 ∧
      D ≤ closureDrive solution t * momentEnergy (velocity := velocity) 4 (cubeFamily N) t.1 +
        nu * (2 * Real.pi) ^ 2 * moment (velocity := velocity) 11 t.1 / ((N : ℝ) + 1) ^ 5 := by
  obtain ⟨D, hD, hle⟩ := momentEnergy_riccati_closure solution t hnu
    (fun k hk ↦ one_le_frequencySup_of_mem_cubeFamily hk) hsum
  refine ⟨D, hD, hle.trans ?_⟩
  have h6 := moment_six_le (velocity := velocity) N t.1 hsum
  have h46 := momentEnergy_four_le_six (velocity := velocity) N t.1
  have hnpi : 0 < nu * (2 * Real.pi) ^ 2 := by positivity
  have hM4 := momentEnergy_nonneg (velocity := velocity) 4 (cubeFamily N) t.1
  have hM6 := momentEnergy_nonneg (velocity := velocity) 6 (cubeFamily N) t.1
  have hPW6 : nu * (2 * Real.pi) ^ 2 * moment (velocity := velocity) 6 t.1 ≤
      nu * (2 * Real.pi) ^ 2 * momentEnergy (velocity := velocity) 6 (cubeFamily N) t.1 +
        nu * (2 * Real.pi) ^ 2 * moment (velocity := velocity) 11 t.1 / ((N : ℝ) + 1) ^ 5 := by
    have := mul_le_mul_of_nonneg_left h6 hnpi.le
    rwa [mul_add, ← mul_div_assoc] at this
  have hPM6 : 0 ≤ nu * (2 * Real.pi) ^ 2 * momentEnergy (velocity := velocity) 6 (cubeFamily N) t.1 :=
    mul_nonneg hnpi.le hM6
  unfold closureDrive
  nlinarith [hPW6, hPM6]

/-- **Grönwall on the cube family.** -/
theorem momentEnergy_cubeFamily_le (hnu : 0 < nu) (N : ℕ) {s τ : ℝ} (hs : s ∈ Ioo 0 T)
    (hτ : τ ∈ Ioo 0 T) (hsτ : s ≤ τ) {b B : ℝ} (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hσ : ∀ σ (hσ : σ ∈ Ioo 0 T), σ ∈ Icc s τ →
      Summable (eleventhMoment (velocity := velocity) σ) ∧
        closureDrive solution ⟨σ, hσ⟩ ≤ b ∧ moment (velocity := velocity) 11 σ ≤ B) :
    momentEnergy (velocity := velocity) 4 (cubeFamily N) τ ≤
      (momentEnergy (velocity := velocity) 4 (cubeFamily N) s +
        nu * (2 * Real.pi) ^ 2 * B / ((N : ℝ) + 1) ^ 5 * (τ - s)) * Real.exp (b * (τ - s)) := by
  refine le_exp_of_hasDerivAt_le hb (by positivity) hsτ ?_
  intro σ hσI
  have hσT : σ ∈ Ioo 0 T := ⟨hs.1.trans_le hσI.1, hσI.2.trans_lt hτ.2⟩
  obtain ⟨hsum, hc, h11⟩ := hσ σ hσT hσI
  obtain ⟨D, hD, hle⟩ := momentEnergy_cubeFamily_riccati solution hnu N ⟨σ, hσT⟩ hsum
  dsimp only at hD hle
  refine ⟨D, hD, hle.trans ?_⟩
  have hM4 := momentEnergy_nonneg (velocity := velocity) 4 (cubeFamily N) σ
  have hnpi : 0 < nu * (2 * Real.pi) ^ 2 := by positivity
  have h1 : closureDrive solution ⟨σ, hσT⟩ * momentEnergy (velocity := velocity) 4 (cubeFamily N) σ ≤
      b * momentEnergy (velocity := velocity) 4 (cubeFamily N) σ :=
    mul_le_mul_of_nonneg_right hc hM4
  have h2 : nu * (2 * Real.pi) ^ 2 * moment (velocity := velocity) 11 σ / ((N : ℝ) + 1) ^ 5 ≤
      nu * (2 * Real.pi) ^ 2 * B / ((N : ℝ) + 1) ^ 5 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h11 hnpi.le) (by positivity)
  linarith

/-! ## The terminal-tail closure -/

/-- **The fourth moment at `τ` is paid by the fourth moment at `s` and the closure drive.** -/
theorem moment_four_le (hnu : 0 < nu) {s τ : ℝ} (hs : s ∈ Ioo 0 T) (hτ : τ ∈ Ioo 0 T)
    (hsτ : s ≤ τ) {b B : ℝ} (hb : 0 ≤ b) (hB : 0 ≤ B)
    (hσ : ∀ σ (hσ : σ ∈ Ioo 0 T), σ ∈ Icc s τ →
      Summable (eleventhMoment (velocity := velocity) σ) ∧
        closureDrive solution ⟨σ, hσ⟩ ≤ b ∧ moment (velocity := velocity) 11 σ ≤ B) :
    moment (velocity := velocity) 4 τ ≤
      moment (velocity := velocity) 4 s * Real.exp (b * (τ - s)) := by
  obtain ⟨hsums, -, -⟩ := hσ s hs ⟨le_rfl, hsτ⟩
  have hsum4s := summable_momentPop (velocity := velocity) (by norm_num : 1 ≤ 4) (by norm_num) s hsums
  refine Real.tsum_le_of_sum_le (momentPop_nonneg 4 τ) fun G ↦ ?_
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ k ∈ G, frequencySup k ≤ N :=
    ⟨G.sup frequencySup, fun k hk ↦ Finset.le_sup (f := frequencySup) hk⟩
  refine le_of_forall_pos_lt_add fun ε hε ↦ ?_
  have hts : 0 ≤ τ - s := sub_nonneg.mpr hsτ
  set C : ℝ := nu * (2 * Real.pi) ^ 2 * B * (τ - s) * Real.exp (b * (τ - s)) with hC
  have hC0 : 0 ≤ C :=
    mul_nonneg (mul_nonneg (mul_nonneg (by positivity) hB) hts) (Real.exp_pos _).le
  obtain ⟨M, hM⟩ := exists_nat_gt (C / ε)
  set N' : ℕ := max N M with hN'
  have hGsub : G ⊆ insert 0 (cubeFamily N') := by
    intro k hk
    rw [Finset.mem_insert]
    by_cases h0 : k = 0
    · exact Or.inl h0
    · right
      exact Finset.mem_erase.mpr ⟨h0, (mem_frequencyCube_iff_frequencySup_le N' k).mpr
        ((hN k hk).trans (le_max_left N M))⟩
  have hexp0 : 0 ≤ Real.exp (b * (τ - s)) := (Real.exp_pos _).le
  have hM4s : momentEnergy (velocity := velocity) 4 (cubeFamily N') s ≤
      moment (velocity := velocity) 4 s :=
    hsum4s.sum_le_tsum _ fun k _ ↦ momentPop_nonneg 4 s k
  have hpos5 : (0 : ℝ) < ((N' : ℝ) + 1) ^ 5 := by positivity
  have hCε : C / ((N' : ℝ) + 1) ^ 5 < ε := by
    rw [div_lt_iff₀ hpos5]
    have hCM : C < ε * M := by
      rw [div_lt_iff₀ hε] at hM
      linarith
    have hMN : (M : ℝ) ≤ (N' : ℝ) := by exact_mod_cast le_max_right N M
    have hN1 : (N' : ℝ) + 1 ≤ ((N' : ℝ) + 1) ^ 5 :=
      le_self_pow₀ (by linarith [(Nat.cast_nonneg N' : (0 : ℝ) ≤ N')]) (by norm_num)
    have : (M : ℝ) ≤ ((N' : ℝ) + 1) ^ 5 := by linarith
    calc C < ε * M := hCM
      _ ≤ ε * ((N' : ℝ) + 1) ^ 5 := mul_le_mul_of_nonneg_left this hε.le
  calc ∑ k ∈ G, momentPop (velocity := velocity) 4 τ k
      ≤ ∑ k ∈ insert 0 (cubeFamily N'), momentPop (velocity := velocity) 4 τ k :=
        Finset.sum_le_sum_of_subset_of_nonneg hGsub fun k _ _ ↦ momentPop_nonneg 4 τ k
    _ = momentEnergy (velocity := velocity) 4 (cubeFamily N') τ := by
        rw [Finset.sum_insert (by simp [cubeFamily]), momentPop_zero 4 (by norm_num), zero_add]
        rfl
    _ ≤ (momentEnergy (velocity := velocity) 4 (cubeFamily N') s +
          nu * (2 * Real.pi) ^ 2 * B / ((N' : ℝ) + 1) ^ 5 * (τ - s)) * Real.exp (b * (τ - s)) :=
        momentEnergy_cubeFamily_le solution hnu N' hs hτ hsτ hb hB hσ
    _ ≤ (moment (velocity := velocity) 4 s +
          nu * (2 * Real.pi) ^ 2 * B / ((N' : ℝ) + 1) ^ 5 * (τ - s)) * Real.exp (b * (τ - s)) :=
        mul_le_mul_of_nonneg_right (add_le_add hM4s le_rfl) hexp0
    _ = moment (velocity := velocity) 4 s * Real.exp (b * (τ - s)) + C / ((N' : ℝ) + 1) ^ 5 := by
        rw [hC]; ring
    _ < moment (velocity := velocity) 4 s * Real.exp (b * (τ - s)) + ε := by linarith

/-! ## The closure statement -/

/-- **Closure-drive control.**  Along a terminal tail `[s, T)` the eleventh moment is finite,
the closure drive `3K/(ν(2π)²)` is at most `b`, and the eleventh moment is bounded on every
compact `[s, τ]`, `τ < T`. -/
def ClosureDriveControl : Prop :=
  ∀ {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField},
    0 < nu →
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure) →
      ∃ (s b : ℝ), 0 < s ∧ s < T ∧ 0 ≤ b ∧
        (∀ σ (hσ : σ ∈ Ioo 0 T), s ≤ σ →
          Summable (eleventhMoment (velocity := velocity) σ) ∧
            closureDrive solution ⟨σ, hσ⟩ ≤ b) ∧
        (∀ τ ∈ Ioo s T, ∃ B : ℝ, ∀ σ ∈ Icc s τ, moment (velocity := velocity) 11 σ ≤ B)

/-- **Closure-drive control returns weighted tail energy control.** -/
theorem weightedTailEnergy_of_closureDrive (h : ClosureDriveControl) :
    WeightedTailEnergyControl := by
  intro T nu initial velocity pressure hnu solution
  obtain ⟨s, b, hs0, hsT, hb, htail, hcompact⟩ := h hnu solution
  have hs : s ∈ Ioo 0 T := ⟨hs0, hsT⟩
  refine ⟨1, s, moment (velocity := velocity) 4 s * Real.exp (b * (T - s)), le_rfl, hs0, hsT,
    fun τ hτ F hF ↦ ?_⟩
  obtain ⟨B, hB⟩ := hcompact τ hτ
  have hτT : τ ∈ Ioo 0 T := ⟨hs0.trans hτ.1, hτ.2⟩
  have hsτ : s ≤ τ := hτ.1.le
  obtain ⟨B', hB'0, hB'⟩ : ∃ B' : ℝ, 0 ≤ B' ∧
      ∀ σ ∈ Icc s τ, moment (velocity := velocity) 11 σ ≤ B' :=
    ⟨max B 0, le_max_right _ _, fun σ hσ ↦ (hB σ hσ).trans (le_max_left _ _)⟩
  have hσ : ∀ σ (hσ : σ ∈ Ioo 0 T), σ ∈ Icc s τ →
      Summable (eleventhMoment (velocity := velocity) σ) ∧
        closureDrive solution ⟨σ, hσ⟩ ≤ b ∧ moment (velocity := velocity) 11 σ ≤ B' :=
    fun σ hσT hσI ↦ ⟨(htail σ hσT hσI.1).1, (htail σ hσT hσI.1).2, hB' σ hσI⟩
  have hmain := moment_four_le solution hnu hs hτT hsτ hb hB'0 hσ
  obtain ⟨hsum, -⟩ := htail τ hτT hsτ
  have hsum4 := summable_momentPop (velocity := velocity) (by norm_num : 1 ≤ 4) (by norm_num) τ hsum
  have hFle : ∑ q ∈ F, ((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q τ ≤
      moment (velocity := velocity) 4 τ :=
    hsum4.sum_le_tsum F fun q _ ↦ momentPop_nonneg 4 τ q
  have hW4s := moment_nonneg (velocity := velocity) 4 s
  have hexp : Real.exp (b * (τ - s)) ≤ Real.exp (b * (T - s)) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by linarith [hτ.2]) hb)
  calc ∑ q ∈ F, ((frequencySup q : ℕ) : ℝ) ^ 4 * modalEnergy (velocity := velocity) q τ
      ≤ moment (velocity := velocity) 4 τ := hFle
    _ ≤ moment (velocity := velocity) 4 s * Real.exp (b * (τ - s)) := hmain
    _ ≤ moment (velocity := velocity) 4 s * Real.exp (b * (T - s)) :=
        mul_le_mul_of_nonneg_left hexp hW4s

/-- **Closure-drive control returns Statement B.** -/
theorem statementB_of_closureDrive (h : ClosureDriveControl) : StatementB :=
  statementB_of_weightedTailEnergy (weightedTailEnergy_of_closureDrive h)

theorem officialProblem_of_closureDrive (h : ClosureDriveControl) :
    TheOfficialNavierStokesProblem :=
  officialProblem_of_weightedTailEnergy (weightedTailEnergy_of_closureDrive h)

section Audit

#print axioms le_exp_of_hasDerivAt_le
#print axioms moment_four_le
#print axioms statementB_of_closureDrive

end Audit

end Soma.Holonics.Millennium.NavierStokesMomentClosure
