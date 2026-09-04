import ElementaryHolonics.RH.LandauLemma

/-!
# Every entire function has a zero factorization on every disc

For an entire `f` with `f z₀ ≠ 0`, Mathlib's zero extraction on the ball `U = ball z₀ r` returns
an analytic nonvanishing `g` with `f = (∏ (· − u)^{D u}) · g` on a codiscrete subset of `U`, where
`D` is the divisor of `f` on `U`.  Continuity upgrades the codiscrete equality to a pointwise
one.  Splitting the divisor's finite support into the half disc and the outer annulus, and
folding the annulus factors back into the unit, produces a `ZeroFactorization f z₀ r`.
-/

noncomputable section

namespace Soma.Holonics.RH.ZeroFactorizationExists

open Complex Metric Set Filter Topology
open Soma.Holonics.RH.LandauLemma

/-- The meromorphic order of a nonzero entire function is never `⊤`. -/
theorem meromorphicOrderAt_ne_top {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ}
    (hf₀ : f z₀ ≠ 0) (u : ℂ) : meromorphicOrderAt f u ≠ ⊤ := by
  have han : AnalyticAt ℂ f u := hf.analyticAt u
  rw [han.meromorphicOrderAt_eq]
  intro htop
  have hne : analyticOrderAt f u ≠ ⊤ := by
    intro h
    have := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero (z := u)
      (fun w => hf.analyticAt w)).mp h
    exact hf₀ (by rw [this]; rfl)
  cases h : analyticOrderAt f u with
  | top => exact hne h
  | coe n =>
    rw [h] at htop
    exact absurd htop (by simp)

/-- **A codiscrete equality of continuous functions on an open set is a pointwise one.** -/
theorem eq_of_codiscreteWithin {f g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hfg : f =ᶠ[codiscreteWithin U] g) {z : ℂ} (hz : z ∈ U)
    (hf : ContinuousAt f z) (hg : ContinuousAt g z) : f z = g z := by
  have hmem : {w | f w = g w} ∈ codiscreteWithin U := hfg
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hmem
  have h1 := hmem z hz
  have h2 : U ∈ 𝓝[≠] z := nhdsWithin_le_nhds (hU.mem_nhds hz)
  have hev : ∀ᶠ w in 𝓝[≠] z, f w = g w := by
    filter_upwards [h1, h2] with w hw hwU
    rcases hw with hw | hw
    · exact hw
    · exact absurd hwU hw
  have : (𝓝[≠] z).NeBot := NormedField.nhdsNE_neBot z
  exact tendsto_nhds_unique_of_eventuallyEq (hf.tendsto.mono_left nhdsWithin_le_nhds)
    (hg.tendsto.mono_left nhdsWithin_le_nhds) hev

/-- **Existence of the zero factorization** for an entire function not vanishing at the
centre, with the total multiplicity equal to the divisor mass of the closed half disc. -/
theorem exists_zeroFactorization_count {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hf₀ : f z₀ ≠ 0) :
    ∃ Z : ZeroFactorization f z₀ r,
      (Z.count : ℤ) = ∑ᶠ u, MeromorphicOn.divisor f (closedBall z₀ (r / 2)) u := by
  classical
  set U : Set ℂ := ball z₀ r with hUdef
  have hUo : IsOpen U := isOpen_ball
  have hmer : MeromorphicOn f U := fun u _ => (hf.analyticAt u).meromorphicAt
  have hord : ∀ u : U, meromorphicOrderAt f u ≠ ⊤ :=
    fun u => meromorphicOrderAt_ne_top hf hf₀ u
  set D := MeromorphicOn.divisor f U with hDdef
  -- the support of the divisor on the open ball is finite: it sits inside the closed ball's
  have hfinC : (Function.support (MeromorphicOn.divisor f (closedBall z₀ r))).Finite :=
    (MeromorphicOn.divisor f (closedBall z₀ r)).finiteSupport (isCompact_closedBall _ _)
  have hDsub : Function.support D ⊆ Function.support (MeromorphicOn.divisor f (closedBall z₀ r)) := by
    intro u hu
    rw [Function.mem_support] at hu ⊢
    have huU : u ∈ U := (MeromorphicOn.divisor f U).supportWithinDomain hu
    have huC : u ∈ closedBall z₀ r := ball_subset_closedBall huU
    rw [hDdef, MeromorphicOn.divisor_apply hmer huU] at hu
    rw [MeromorphicOn.divisor_apply (fun v _ => (hf.analyticAt v).meromorphicAt) huC]
    exact hu
  have hfin : (Function.support D).Finite := hfinC.subset hDsub
  obtain ⟨g, hg, hg0, hcod⟩ := MeromorphicOn.extract_zeros_poles hmer hord hfin
  have han : AnalyticOnNhd ℂ f U := hf.differentiableOn.analyticOnNhd hUo
  have hDnn : ∀ u, 0 ≤ D u := fun u => by
    first
      | exact (MeromorphicOn.AnalyticOnNhd.divisor_nonneg han) u
      | exact (AnalyticOnNhd.divisor_nonneg han) u
  -- the factorized rational as a finite product over the support
  set S : Finset ℂ := hfin.toFinset with hSdef
  have hφ : (∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) = ∏ u ∈ S, (· - u) ^ D u := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro u hu
    rw [Function.mem_mulSupport] at hu
    rw [hSdef, Set.Finite.coe_toFinset, Function.mem_support]
    intro h0
    apply hu
    rw [h0, zpow_zero]
  have hφeval : ∀ z, (∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) z = ∏ u ∈ S, (z - u) ^ (D u).toNat := by
    intro z
    rw [hφ, Finset.prod_apply]
    apply Finset.prod_congr rfl
    intro u _
    simp only [Pi.pow_apply]
    rw [← Int.toNat_of_nonneg (hDnn u), zpow_natCast, Int.toNat_of_nonneg (hDnn u)]
  -- pointwise factorization on the ball
  have hpt : ∀ z ∈ U, f z = (∏ u ∈ S, (z - u) ^ (D u).toNat) * g z := by
    intro z hz
    have hφan : AnalyticAt ℂ (∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) z :=
      Function.FactorizedRational.analyticAt (hDnn z)
    have hcont : ContinuousAt ((∏ᶠ u, (· - u) ^ D u : ℂ → ℂ) • g) z :=
      hφan.continuousAt.smul (hg z hz).continuousAt
    have := eq_of_codiscreteWithin hUo hcod hz (hf.continuous.continuousAt) hcont
    rw [this, Pi.smul_apply', smul_eq_mul, hφeval]
  -- split the support into the half disc and the annulus
  refine ⟨{ zeros := S.filter (fun ρ => ρ ∈ closedBall z₀ (r / 2))
            mult := fun ρ => (D ρ).toNat
            unit := fun z => (∏ ρ ∈ S.filter (fun ρ => ρ ∉ closedBall z₀ (r / 2)),
              (z - ρ) ^ (D ρ).toNat) * g z
            zeros_mem := ?_
            mult_pos := ?_
            unit_diff := ?_
            unit_ne := ?_
            factor := ?_ }, ?_⟩
  · intro ρ hρ
    exact (Finset.mem_filter.mp hρ).2
  · intro ρ hρ
    have hsupp := (Finset.mem_filter.mp hρ).1
    rw [hSdef, Set.Finite.mem_toFinset, Function.mem_support] at hsupp
    have := hDnn ρ
    omega
  · apply DifferentiableOn.mul
    · exact DifferentiableOn.fun_finsetProd (f := fun ρ z => (z - ρ) ^ (D ρ).toNat)
        (s := ball z₀ r) (fun ρ _ => by fun_prop)
    · exact hg.differentiableOn
  · intro z hz
    apply mul_ne_zero
    · rw [Finset.prod_ne_zero_iff]
      intro ρ hρ
      apply pow_ne_zero
      have hout := (Finset.mem_filter.mp hρ).2
      intro h0
      apply hout
      rw [sub_eq_zero] at h0
      rw [← h0]
      exact ball_subset_closedBall hz
    · exact hg0 ⟨z, ball_subset_ball (by linarith) hz⟩
  · intro z hz
    rw [hpt z hz, ← Finset.prod_filter_mul_prod_filter_not S (fun ρ => ρ ∈ closedBall z₀ (r / 2))]
    ring
  · -- the count is the divisor mass of the closed half disc
    set D' := MeromorphicOn.divisor f (closedBall z₀ (r / 2)) with hD'def
    have hmer' : MeromorphicOn f (closedBall z₀ (r / 2)) :=
      fun u _ => (hf.analyticAt u).meromorphicAt
    have hsub : closedBall z₀ (r / 2) ⊆ U := closedBall_subset_ball (by linarith)
    have hagree : ∀ u ∈ closedBall z₀ (r / 2), D' u = D u := by
      intro u hu
      rw [hD'def, hDdef, MeromorphicOn.divisor_apply hmer' hu,
        MeromorphicOn.divisor_apply hmer (hsub hu)]
    have hsupp : Function.support D' ⊆ ↑(S.filter (fun ρ => ρ ∈ closedBall z₀ (r / 2))) := by
      intro u hu
      rw [Function.mem_support] at hu
      have huC : u ∈ closedBall z₀ (r / 2) := D'.supportWithinDomain hu
      rw [Finset.mem_coe, Finset.mem_filter, hSdef, Set.Finite.mem_toFinset, Function.mem_support]
      refine ⟨?_, huC⟩
      rw [← hagree u huC]
      exact hu
    show ((∑ ρ ∈ S.filter (fun ρ => ρ ∈ closedBall z₀ (r / 2)), (D ρ).toNat : ℕ) : ℤ) =
      ∑ᶠ u, D' u
    rw [finsum_eq_sum_of_support_subset D' hsupp, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    rw [hagree ρ (Finset.mem_filter.mp hρ).2, Int.toNat_of_nonneg (hDnn ρ)]

/-- **Existence of the zero factorization** for an entire function not vanishing at the
centre. -/
theorem exists_zeroFactorization {f : ℂ → ℂ} (hf : Differentiable ℂ f) {z₀ : ℂ} {r : ℝ}
    (hr : 0 < r) (hf₀ : f z₀ ≠ 0) : Nonempty (ZeroFactorization f z₀ r) :=
  ⟨(exists_zeroFactorization_count hf hr hf₀).choose⟩

end Soma.Holonics.RH.ZeroFactorizationExists
