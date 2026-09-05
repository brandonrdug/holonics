import ElementaryHolonics.Millennium.NavierStokesSwirlCirculation
import ElementaryHolonics.Millennium.NavierStokesScalarHeatVolterra
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# A backward circulation history retains the required source magnitude

The actual meridional circulation law is L'=source-(alpha-beta)L. A bounded complete past
cannot carry a nonzero circulation with a smaller uniformly bounded source. The finite-history
bound keeps its incoming circulation term. Compactness is applied to the actual trajectory
and angular-momentum carrier; this owner does not postulate a global trajectory or construct
an exterior completion.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Soma.Holonics.Millennium.NavierStokesSwirlHistory

open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesSwirlCirculation

def weightedExcess (delta c : ℝ) (L : ℝ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (delta * t) * (L t - c)

theorem weightedExcess_hasDerivAt (delta c : ℝ) (L : ℝ → ℝ) (f t : ℝ)
    (hL : HasDerivAt L (f - delta * L t) t) :
    HasDerivAt (weightedExcess delta c L)
      (Real.exp (delta * t) * (f - delta * c)) t := by
  have he := ((hasDerivAt_id t).const_mul delta).exp
  convert he.mul (hL.sub_const c) using 1 <;>
    first | rfl | (simp only [id_eq] <;> ring)

theorem one_sided_finite_history (delta epsilon : ℝ) (hdelta : delta ≠ 0)
    (L source : ℝ → ℝ) {t : ℝ} (ht : t ≤ 0)
    (hL : ∀ s ∈ Icc t 0, HasDerivAt L (source s - delta * L s) s)
    (hsource : ∀ s ∈ Icc t 0, source s ≤ epsilon) :
    L 0 ≤ Real.exp (delta * t) * L t +
      (epsilon / delta) * (1 - Real.exp (delta * t)) := by
  have hcancel : delta * (epsilon / delta) = epsilon := mul_div_cancel₀ epsilon hdelta
  have hd : ∀ s ∈ Icc t 0,
      HasDerivAt (weightedExcess delta (epsilon / delta) L)
        (Real.exp (delta * s) * (source s - epsilon)) s := by
    intro s hs
    simpa only [hcancel] using
      weightedExcess_hasDerivAt delta (epsilon / delta) L (source s) s (hL s hs)
  have hanti : AntitoneOn (weightedExcess delta (epsilon / delta) L) (Icc t 0) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc t 0)
    · intro s hs
      exact (hd s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hd s (Ioo_subset_Icc_self hs)).differentiableAt.differentiableWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      rw [(hd s (Ioo_subset_Icc_self hs)).deriv]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le
        (sub_nonpos.mpr (hsource s (Ioo_subset_Icc_self hs)))
  have hmono := hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  simp only [weightedExcess, mul_zero, Real.exp_zero, one_mul] at hmono
  nlinarith

/-- The finite history keeps the incoming carrier; no complete-past hypothesis is hidden here. -/
theorem abs_finite_history_bound (delta epsilon M : ℝ) (hdelta : delta ≠ 0)
    (L source : ℝ → ℝ) {t : ℝ} (ht : t ≤ 0)
    (hL : ∀ s ∈ Icc t 0, HasDerivAt L (source s - delta * L s) s)
    (hsource : ∀ s ∈ Icc t 0, |source s| ≤ epsilon)
    (hbound : |L t| ≤ M) :
    |L 0| ≤ Real.exp (delta * t) * M +
      (epsilon / delta) * (1 - Real.exp (delta * t)) := by
  have hu := one_sided_finite_history delta epsilon hdelta L source ht hL
    (fun s hs ↦ (le_abs_self (source s)).trans (hsource s hs))
  have hnL : ∀ s ∈ Icc t 0, HasDerivAt (fun t ↦ -L t)
      (-source s - delta * (-L s)) s := by
    intro s hs
    convert (hL s hs).neg using 1 <;> first | rfl | ring
  have hl := one_sided_finite_history delta epsilon hdelta (fun t ↦ -L t)
    (fun t ↦ -source t) ht hnL
    (fun s hs ↦ (neg_le_abs (source s)).trans (hsource s hs))
  have hupper : L t ≤ M := (le_abs_self (L t)).trans hbound
  have hlower : -L t ≤ M := (neg_le_abs (L t)).trans hbound
  have he : 0 ≤ Real.exp (delta * t) := (Real.exp_pos _).le
  apply abs_le.mpr
  constructor <;> nlinarith

/-- A complete uniformly bounded past forces a source of at least delta times the current
circulation magnitude. The exponential incoming term vanishes only in this complete-past limit. -/
theorem source_threshold_of_bounded_past (delta epsilon M : ℝ) (hdelta : 0 < delta)
    (L source : ℝ → ℝ)
    (hL : ∀ t, t ≤ 0 → HasDerivAt L (source t - delta * L t) t)
    (hsource : ∀ t, t ≤ 0 → |source t| ≤ epsilon)
    (hbound : ∀ t, t ≤ 0 → |L t| ≤ M) :
    delta * |L 0| ≤ epsilon := by
  have he : Tendsto (fun T : ℝ ↦ Real.exp (-delta * T)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (tendsto_id.const_mul_atTop hdelta) using 1 <;>
      first | rfl | (simp only [Function.comp_def, id_eq] <;> ring_nf)
  have hb : Tendsto (fun T : ℝ ↦ Real.exp (-delta * T) * M +
      (epsilon / delta) * (1 - Real.exp (-delta * T))) atTop (𝓝 (epsilon / delta)) := by
    convert (he.mul_const M).add (tendsto_const_nhds.mul (tendsto_const_nhds.sub he)) using 1 <;>
      first | rfl | simp
  have hle : |L 0| ≤ epsilon / delta := by
    apply le_of_tendsto_of_tendsto tendsto_const_nhds hb
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
    simpa only [mul_neg, neg_mul] using abs_finite_history_bound delta epsilon M hdelta.ne'
      L source (neg_nonpos.mpr hT) (fun s hs ↦ hL s hs.2)
      (fun s hs ↦ hsource s hs.2) (hbound (-T) (neg_nonpos.mpr hT))
  simpa only [mul_comm] using (le_div_iff₀ hdelta).mp hle

/-- A compact actual meridional history supplies the uniform carrier bound. -/
theorem compact_history_source_threshold (alpha beta epsilon : ℝ)
    (hgap : beta < alpha) (V Omega W : MeridionalProfile)
    (hOmega : Differentiable ℝ Omega) (trajectory : ℝ → ℝ × ℝ)
    (htrajectory : ∀ t, t ≤ 0 → HasDerivAt trajectory
      (meridionalDrift beta V W (trajectory t)) t)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hinside : ∀ t, t ≤ 0 → trajectory t ∈ K)
    (hsource : ∀ t, t ≤ 0 →
      |(trajectory t).1 * swirlMomentum alpha beta V Omega W (trajectory t)| ≤ epsilon) :
    (alpha - beta) * |angularMomentum Omega (trajectory 0)| ≤ epsilon := by
  have hc : Continuous (angularMomentum Omega) := continuous_fst.mul hOmega.continuous
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  apply source_threshold_of_bounded_past (alpha - beta) epsilon M (sub_pos.mpr hgap)
    (fun t ↦ angularMomentum Omega (trajectory t))
    (fun t ↦ (trajectory t).1 * swirlMomentum alpha beta V Omega W (trajectory t))
  · intro t ht
    exact hasDerivAt_angularMomentum_along_meridionalDrift alpha beta V Omega W trajectory t
      (hOmega _) (htrajectory t ht)
  · exact hsource
  · intro t ht
    simpa only [Real.norm_eq_abs] using hM (trajectory t) (hinside t ht)

/-- Exact zero swirl residual and a compact complete past force the current angular momentum
to vanish. This is a source-bound obstruction to a proposed exterior completion. -/
theorem zero_circulation_of_compact_exact_history (alpha beta : ℝ)
    (hgap : beta < alpha) (V Omega W : MeridionalProfile)
    (hOmega : Differentiable ℝ Omega) (trajectory : ℝ → ℝ × ℝ)
    (htrajectory : ∀ t, t ≤ 0 → HasDerivAt trajectory
      (meridionalDrift beta V W (trajectory t)) t)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hinside : ∀ t, t ≤ 0 → trajectory t ∈ K)
    (hswirl : ∀ t, t ≤ 0 → swirlMomentum alpha beta V Omega W (trajectory t) = 0) :
    angularMomentum Omega (trajectory 0) = 0 := by
  have h := compact_history_source_threshold alpha beta 0 hgap V Omega W hOmega trajectory
    htrajectory hK hinside (by intro t ht; simp [hswirl t ht])
  have hz : |angularMomentum Omega (trajectory 0)| = 0 := by
    nlinarith [abs_nonneg (angularMomentum Omega (trajectory 0))]
  exact abs_eq_zero.mp hz

theorem nonzero_circulation_excludes_compact_exact_history (alpha beta : ℝ)
    (hgap : beta < alpha) (V Omega W : MeridionalProfile)
    (hOmega : Differentiable ℝ Omega) (p : ℝ × ℝ)
    (hp : angularMomentum Omega p ≠ 0) :
    ¬ ∃ (trajectory : ℝ → ℝ × ℝ) (K : Set (ℝ × ℝ)),
      trajectory 0 = p ∧ IsCompact K ∧
      (∀ t, t ≤ 0 → trajectory t ∈ K) ∧
      (∀ t, t ≤ 0 → HasDerivAt trajectory (meridionalDrift beta V W (trajectory t)) t) ∧
      (∀ t, t ≤ 0 → swirlMomentum alpha beta V Omega W (trajectory t) = 0) := by
  rintro ⟨trajectory, K, hpast, hK, hinside, htrajectory, hswirl⟩
  have h := zero_circulation_of_compact_exact_history alpha beta hgap V Omega W hOmega
    trajectory htrajectory hK hinside hswirl
  rw [hpast] at h
  exact hp h

#print axioms one_sided_finite_history
#print axioms abs_finite_history_bound
#print axioms source_threshold_of_bounded_past
#print axioms compact_history_source_threshold
#print axioms zero_circulation_of_compact_exact_history
#print axioms nonzero_circulation_excludes_compact_exact_history

end Soma.Holonics.Millennium.NavierStokesSwirlHistory
