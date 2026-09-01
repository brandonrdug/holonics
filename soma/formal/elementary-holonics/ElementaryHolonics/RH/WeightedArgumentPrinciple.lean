import ElementaryHolonics.RH.ExplicitFormulaReceiver

/-!
# The weighted argument principle on every admissible xi contour

**[proved-derived; formal-checked]** `RH.ExplicitFormulaReceiver` left the first explicit-formula
port, `HasWeightedArgumentPrinciple`, as a named obligation.  This file discharges it for every
admissible contour and every Weil test: whenever the circle `C(c, R)` (with `0 < R`) meets no zero
of the entire Riemann xi function,

```text
(2πi)⁻¹ ∮_{C(c,R)} Φ(z) ξ'(z)/ξ(z) dz = Σ_{ξ(ρ)=0, |ρ-c| ≤ R} m_ρ Φ(ρ),
```

with the right-hand side literally the repository's `truncatedZeroReceiver`, so the divisor of
`ξ` on the closed disc, retained with multiplicity, is the returned population.

**Mechanism.** The finitely many zeros of `ξ` on the closed disc are extracted by Mathlib's
`MeromorphicOn.extract_zeros_poles`: `ξ = P · g` on a codiscrete subset of the disc, where `P` is
the factorized rational function of the divisor and `g` is analytic and nonvanishing on the disc.
The identity theorem upgrades that codiscrete equality to equality on an open connected
neighbourhood of the disc.  On the contour the logarithmic derivative therefore splits into
`Σ m_ρ/(z-ρ) + g'/g`; each simple pole returns `Φ(ρ)` by Cauchy's integral formula and the
analytic remainder returns zero by Cauchy--Goursat.

**Boundary.** This is the contour-to-divisor port only.  The second port,
`HasPrimeArchimedeanResidualIdentity`, which deforms the same contour onto the prime and
archimedean receivers, is not touched here and remains the named open obligation of
`RH.GlobalWeilFinishLine`.
-/

noncomputable section

namespace Soma.Holonics.RH.WeightedArgumentPrinciple

open Complex Metric Set Filter Topology
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.ExplicitFormulaReceiver

/-! ## The xi function is nowhere locally zero -/

/-- [proved-derived; formal-checked] The entire xi function does not vanish identically near any
point, because it is `1/2` at the origin. -/
theorem meromorphicOrderAt_riemannXi_ne_top (u : ℂ) :
    meromorphicOrderAt riemannXi u ≠ ⊤ := by
  rw [(analyticOn_riemannXi Set.univ u (Set.mem_univ u)).meromorphicOrderAt_eq]
  intro htop
  have hzero : analyticOrderAt riemannXi u = ⊤ := by
    cases hn : analyticOrderAt riemannXi u with
    | top => rfl
    | coe n =>
      rw [hn, ENat.map_natCast] at htop
      exact absurd htop (WithTop.coe_ne_top)
  rw [analyticOrderAt_eq_top] at hzero
  have hall : Set.EqOn riemannXi 0 Set.univ :=
    (analyticOn_riemannXi Set.univ).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (Set.mem_univ u) hzero
  have h0 := hall (Set.mem_univ (0 : ℂ))
  rw [riemannXi_zero_and_one.1] at h0
  norm_num at h0

/-- [proved-derived; formal-checked] The divisor of xi on a closed disc has finite support. -/
theorem divisor_riemannXi_closedBall_support_finite (c : ℂ) (R : ℝ) :
    (MeromorphicOn.divisor riemannXi (closedBall c R)).support.Finite :=
  (MeromorphicOn.divisor riemannXi (closedBall c R)).finiteSupport (isCompact_closedBall c R)

/-- [proved-derived; formal-checked] Off the zero set the xi divisor vanishes. -/
theorem divisor_riemannXi_eq_zero_of_ne_zero {c : ℂ} {R : ℝ} {z : ℂ}
    (hz : riemannXi z ≠ 0) :
    MeromorphicOn.divisor riemannXi (closedBall c R) z = 0 := by
  by_cases hmem : z ∈ closedBall c R
  · rw [MeromorphicOn.divisor_apply (meromorphicOn_riemannXi (closedBall c R)) hmem,
      (analyticOn_riemannXi (closedBall c R) z hmem).meromorphicOrderAt_eq,
      ((analyticOn_riemannXi (closedBall c R) z hmem).analyticOrderAt_eq_zero).2 hz]
    simp
  · exact Function.locallyFinsuppWithin.apply_eq_zero_of_notMem _ hmem

/-! ## A finite-sum circle integral -/

/-- [proved-derived; formal-checked] The circle integral of a finite sum of circle-integrable
functions is the sum of the circle integrals. -/
theorem circleIntegral_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℂ → ℂ) (c : ℂ) (R : ℝ)
    (hf : ∀ i ∈ s, CircleIntegrable (f i) c R) :
    (∮ z in C(c, R), ∑ i ∈ s, f i z) = ∑ i ∈ s, ∮ z in C(c, R), f i z := by
  simp only [circleIntegral, Finset.smul_sum]
  exact intervalIntegral.integral_finsetSum fun i hi => (circleIntegrable_iff R).1 (hf i hi)

/-! ## The weighted argument principle -/

/-- [proved-derived; formal-checked] **The weighted argument principle on an admissible xi
contour.**  For every Weil test `T` and every positively oriented circle meeting no zero of xi,
the logarithmic-derivative contour receiver equals the divisor-weighted zero receiver. -/
theorem hasWeightedArgumentPrinciple (T : WeilTestFunction) {c : ℂ} {R : ℝ}
    (hadm : AdmissibleXiContour c R) :
    HasWeightedArgumentPrinciple T c R := by
  classical
  refine ⟨hadm, ?_⟩
  have hR : 0 < R := hadm.radius_pos
  set U : Set ℂ := closedBall c R with hU
  set D := MeromorphicOn.divisor riemannXi U with hD
  -- the zero population is finite
  have hDfin : D.support.Finite := divisor_riemannXi_closedBall_support_finite c R
  have hDnonneg : ∀ z, 0 ≤ D z := fun z => (divisor_riemannXi_nonnegative U) z
  -- extract the zeros
  obtain ⟨g, hg_an, hg_ne, hg_eq⟩ :=
    (meromorphicOn_riemannXi U).extract_zeros_poles
      (fun u => meromorphicOrderAt_riemannXi_ne_top u) hDfin
  set P : ℂ → ℂ := ∏ᶠ u, (· - u) ^ D u with hP
  -- `P` is entire because the divisor is nonnegative
  have hP_an : ∀ z, AnalyticAt ℂ P z := fun z =>
    Function.FactorizedRational.analyticAt (hDnonneg z)
  -- the open set on which `g` is analytic and nonvanishing
  set W : Set ℂ := {z | AnalyticAt ℂ g z ∧ g z ≠ 0} with hW
  have hW_open : IsOpen W := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have h1 : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ g w := hz.1.eventually_analyticAt
    have h2 : ∀ᶠ w in 𝓝 z, g w ≠ 0 := hz.1.continuousAt.eventually_ne hz.2
    exact (h1.and h2)
  have hU_W : U ⊆ W := fun z hz => ⟨hg_an z hz, hg_ne ⟨z, hz⟩⟩
  have hc_U : c ∈ U := mem_closedBall_self hR.le
  set W₀ : Set ℂ := connectedComponentIn W c with hW₀
  have hW₀_open : IsOpen W₀ := hW_open.connectedComponentIn
  have hW₀_conn : IsPreconnected W₀ := isPreconnected_connectedComponentIn
  have hU_W₀ : U ⊆ W₀ :=
    (convex_closedBall c R).isPreconnected.subset_connectedComponentIn hc_U hU_W
  have hW₀_W : W₀ ⊆ W := connectedComponentIn_subset W c
  -- the codiscrete equality at the centre gives an eventual equality at the centre
  have hcentre : ∀ᶠ z in 𝓝 c, riemannXi z = P z * g z := by
    have hmem : {z | riemannXi z = (P • g) z} ∈ codiscreteWithin U := hg_eq
    rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at hmem
    have h1 := hmem c hc_U
    have h2 : U ∈ 𝓝[≠] c := nhdsWithin_le_nhds (closedBall_mem_nhds c hR)
    have h3 : ∀ᶠ z in 𝓝[≠] c, riemannXi z = P z * g z := by
      filter_upwards [h1, h2] with z hz hzU
      rcases hz with hz | hz
      · simpa [Pi.smul_apply', smul_eq_mul] using hz
      · exact absurd hzU hz
    exact ((analyticOn_riemannXi Set.univ c (Set.mem_univ c)).frequently_eq_iff_eventually_eq
      ((hP_an c).mul (hg_an c hc_U))).1 h3.frequently
  -- the identity theorem on the open connected neighbourhood
  have hPg_an : AnalyticOnNhd ℂ (fun z => P z * g z) W₀ := fun z hz =>
    (hP_an z).mul (hW₀_W hz).1
  have hEqOn : Set.EqOn riemannXi (fun z => P z * g z) W₀ :=
    (analyticOn_riemannXi W₀).eqOn_of_preconnected_of_eventuallyEq hPg_an hW₀_conn
      (hU_W₀ hc_U) hcentre
  have hnear : ∀ z ∈ U, riemannXi =ᶠ[𝓝 z] fun w => P w * g w := fun z hz =>
    eventuallyEq_of_mem (hW₀_open.mem_nhds (hU_W₀ hz)) hEqOn
  -- the finite support as a `Finset`, and the explicit product
  set S : Finset ℂ := hDfin.toFinset with hS
  have hmem_S : ∀ u, u ∈ S ↔ D u ≠ 0 := fun u => by
    rw [hS, Set.Finite.mem_toFinset, Function.mem_support]
  have hP_eq : P = fun z => ∏ u ∈ S, (z - u) ^ D u := by
    rw [hP, Function.FactorizedRational.finprod_eq_fun hDfin]
    funext z
    apply finprod_eq_prod_of_mulSupport_subset
    intro u hu
    rw [Finset.mem_coe, hmem_S]
    intro hu0
    apply hu
    simp [hu0]
  -- every zero lies in the open disc
  have hS_ball : ∀ u ∈ S, u ∈ ball c R := by
    intro u hu
    have hu0 : D u ≠ 0 := (hmem_S u).1 hu
    have huU : u ∈ U := D.supportWithinDomain hu0
    have hne : riemannXi u = 0 := by
      by_contra hne
      exact hu0 (divisor_riemannXi_eq_zero_of_ne_zero hne)
    rcases eq_or_lt_of_le (mem_closedBall.1 huU) with h | h
    · exact absurd hne (hadm.zero_free u (mem_sphere.2 h))
    · exact mem_ball.2 h
  -- on the contour the logarithmic derivative splits
  have hsplit : ∀ z ∈ sphere c R,
      T.spectralKernel z * (deriv riemannXi z / riemannXi z) =
        (∑ u ∈ S, (D u : ℂ) * (T.spectralKernel z * (z - u)⁻¹)) +
          T.spectralKernel z * (deriv g z / g z) := by
    intro z hz
    have hzU : z ∈ U := sphere_subset_closedBall hz
    have hz_ne : riemannXi z ≠ 0 := hadm.zero_free z hz
    have hz_S : ∀ u ∈ S, z ≠ u := by
      intro u hu hzu
      have hb := hS_ball u hu
      rw [← hzu, mem_ball] at hb
      rw [mem_sphere] at hz
      exact hb.ne hz
    have hfactor_ne : ∀ u ∈ S, (z - u) ^ D u ≠ 0 := fun u hu =>
      zpow_ne_zero _ (sub_ne_zero.2 (hz_S u hu))
    have hfactor_diff : ∀ u ∈ S, DifferentiableAt ℂ (fun w => (w - u) ^ D u) z := fun u _ =>
      (differentiableAt_id.sub_const u).zpow (Or.inr (hDnonneg u))
    have hP_ne : P z ≠ 0 := by
      rw [hP_eq]
      exact Finset.prod_ne_zero_iff.2 hfactor_ne
    have hg_z : g z ≠ 0 := hg_ne ⟨z, hzU⟩
    have hlog : deriv riemannXi z / riemannXi z = logDeriv (fun w => P w * g w) z := by
      rw [logDeriv_apply, (hnear z hzU).deriv_eq, (hnear z hzU).eq_of_nhds]
    have hlogPg : logDeriv (fun w => P w * g w) z = logDeriv P z + logDeriv g z :=
      logDeriv_mul z hP_ne hg_z (hP_an z).differentiableAt (hg_an z hzU).differentiableAt
    have hlogP : logDeriv P z = ∑ u ∈ S, (D u : ℂ) * (z - u)⁻¹ := by
      rw [hP_eq]
      rw [logDeriv_prod (f := fun u w => (w - u) ^ D u) (x := z) hfactor_ne hfactor_diff]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [logDeriv_fun_zpow (f := fun w => w - u) (x := z) (differentiableAt_id.sub_const u)]
      congr 1
      rw [logDeriv_apply]
      simp
    rw [hlog, hlogPg, hlogP, logDeriv_apply, mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun u _ => ?_
    ring
  -- the contour receiver as a sum of integrals
  have hint_S : ∀ u ∈ S,
      CircleIntegrable (fun z => (D u : ℂ) * (T.spectralKernel z * (z - u)⁻¹)) c R := by
    intro u hu
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine continuousOn_const.mul (T.spectralAnalytic.continuous.continuousOn.mul ?_)
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    intro z hz
    intro hzu
    have hzu' : z = u := sub_eq_zero.1 hzu
    have := hS_ball u hu
    rw [← hzu'] at this
    rw [mem_sphere] at hz
    rw [mem_ball] at this
    exact (ne_of_lt this) hz
  have hint_g : CircleIntegrable (fun z => T.spectralKernel z * (deriv g z / g z)) c R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine T.spectralAnalytic.continuous.continuousOn.mul ?_
    intro z hz
    have hzU : z ∈ U := sphere_subset_closedBall hz
    refine ContinuousAt.continuousWithinAt ?_
    exact ((hg_an z hzU).deriv.continuousAt).div (hg_an z hzU).continuousAt (hg_ne ⟨z, hzU⟩)
  have hint_sum : CircleIntegrable
      (fun z => ∑ u ∈ S, (D u : ℂ) * (T.spectralKernel z * (z - u)⁻¹)) c R := by
    refine ContinuousOn.circleIntegrable hR.le ?_
    refine continuousOn_finsetSum S fun u hu => ?_
    refine continuousOn_const.mul (T.spectralAnalytic.continuous.continuousOn.mul ?_)
    refine ContinuousOn.inv₀ (continuousOn_id.sub continuousOn_const) ?_
    intro z hz hzu
    have hzu' : z = u := sub_eq_zero.1 hzu
    have := hS_ball u hu
    rw [← hzu'] at this
    rw [mem_sphere] at hz
    rw [mem_ball] at this
    exact (ne_of_lt this) hz
  -- Cauchy's integral formula at each zero
  have hcauchy : ∀ u ∈ S,
      (∮ z in C(c, R), (D u : ℂ) * (T.spectralKernel z * (z - u)⁻¹)) =
        (D u : ℂ) * ((2 * Real.pi * I : ℂ) * T.spectralKernel u) := by
    intro u hu
    rw [circleIntegral.integral_const_mul]
    congr 1
    have hΦ : DifferentiableOn ℂ T.spectralKernel (closedBall c R) :=
      T.spectralAnalytic.differentiableOn
    have hcf := hΦ.circleIntegral_sub_inv_smul (hS_ball u hu)
    rw [smul_eq_mul] at hcf
    rw [← hcf]
    refine circleIntegral.integral_congr hR.le fun z _ => ?_
    simp only [smul_eq_mul]
    ring
  -- Cauchy--Goursat for the analytic remainder
  have hgoursat : (∮ z in C(c, R), T.spectralKernel z * (deriv g z / g z)) = 0 := by
    apply DiffContOnCl.circleIntegral_eq_zero hR.le
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball c hR.ne']
    intro z hz
    have hzW : z ∈ W := hU_W hz
    refine DifferentiableAt.differentiableWithinAt ?_
    exact T.spectralAnalytic.differentiableAt.mul
      ((hzW.1.deriv.differentiableAt).div hzW.1.differentiableAt hzW.2)
  -- assemble
  have h2πI : (2 * Real.pi * I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  have hcontour : contourReceiver T c R = ∑ u ∈ S, (D u : ℂ) * T.spectralKernel u := by
    unfold contourReceiver
    rw [circleIntegral.integral_congr hR.le hsplit, circleIntegral.integral_add hint_sum hint_g,
      hgoursat, add_zero, circleIntegral_finset_sum S _ c R hint_S, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u hu => ?_
    rw [hcauchy u hu]
    field_simp
  rw [hcontour]
  unfold truncatedZeroReceiver
  rw [abs_of_pos hR]
  rw [finsum_eq_sum_of_support_subset]
  intro u hu
  rw [Function.mem_support] at hu
  rw [Finset.mem_coe, hmem_S]
  intro hu0
  apply hu
  show ((D u : ℤ) : ℂ) * T.spectralKernel u = 0
  rw [hu0]
  simp

/-- [proved-derived; formal-checked] The argument-principle defect vanishes on every admissible
contour. -/
theorem argumentPrincipleDefect_eq_zero (T : WeilTestFunction) {c : ℂ} {R : ℝ}
    (hadm : AdmissibleXiContour c R) :
    argumentPrincipleDefect T c R = 0 :=
  (hasWeightedArgumentPrinciple_iff_defect_eq_zero hadm).1 (hasWeightedArgumentPrinciple T hadm)

section Audit

#print axioms meromorphicOrderAt_riemannXi_ne_top
#print axioms hasWeightedArgumentPrinciple
#print axioms argumentPrincipleDefect_eq_zero

end Audit

end Soma.Holonics.RH.WeightedArgumentPrinciple
