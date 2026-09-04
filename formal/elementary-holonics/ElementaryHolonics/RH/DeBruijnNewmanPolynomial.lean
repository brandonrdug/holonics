import ElementaryHolonics.RH.HeatSemigroup

/-!
# The de Bruijn–Newman threshold of a real polynomial

`realRootedTimes p = {t | nonreal (heatR t p) = 0}` is an up-set of `ℝ` by the semigroup and
forward preservation.  Its infimum `lambda p` is the polynomial de Bruijn–Newman constant.  When
`p` carries a pair, every real-rooted time is non-negative, so `lambda p ≥ 0`; when `p` is already
real-rooted, `lambda p ≤ 0`.  Above `lambda p` the population is empty; strictly below it, the
population is non-empty.  This is exactly the shape `RH ⟺ Λ ≤ 0` at the polynomial face.
-/

open Polynomial Finset
open Soma.Holonics.RH.PolyaStep
open Soma.Holonics.RH.PairDescent
open Soma.Holonics.RH.ForwardPreservation
open Soma.Holonics.RH.HurwitzPolynomial
open Soma.Holonics.RH.HeatSemigroup

namespace Soma.Holonics.RH.DeBruijnNewmanPolynomial

/-- The times at which the flow of `p` has empty pair population. -/
def realRootedTimes (p : ℝ[X]) : Set ℝ := {t | nonreal (heatR t p) = 0}

theorem mem_realRootedTimes {p : ℝ[X]} {t : ℝ} :
    t ∈ realRootedTimes p ↔ nonreal (heatR t p) = 0 := Iff.rfl

/-- Real-rooted times form an up-set. -/
theorem mem_realRootedTimes_of_le {p : ℝ[X]} {t t' : ℝ} (h : t ≤ t') (ht : t ∈ realRootedTimes p) :
    t' ∈ realRootedTimes p :=
  nonreal_heatR_eq_zero_of_le h ht

/-- The polynomial de Bruijn–Newman threshold. -/
noncomputable def lambda (p : ℝ[X]) : ℝ := sInf (realRootedTimes p)

/-- Below the threshold of a polynomial with a pair, no time is real-rooted; hence every
real-rooted time is non-negative when `p` has a pair. -/
theorem nonneg_of_mem {p : ℝ[X]} (hp : nonreal p ≠ 0) {t : ℝ} (ht : t ∈ realRootedTimes p) :
    0 ≤ t := by
  by_contra h
  push Not at h
  have := mem_realRootedTimes_of_le h.le ht
  rw [mem_realRootedTimes, heatR_zero] at this
  exact hp this

theorem lambda_nonneg {p : ℝ[X]} (hp : nonreal p ≠ 0) : 0 ≤ lambda p :=
  Real.sInf_nonneg (fun _ ht => nonneg_of_mem hp ht)

theorem bddBelow_realRootedTimes {p : ℝ[X]} (hp : nonreal p ≠ 0) : BddBelow (realRootedTimes p) :=
  ⟨0, fun _ ht => nonneg_of_mem hp ht⟩

/-- Strictly above the threshold the population is empty, provided some time is real-rooted. -/
theorem mem_of_lambda_lt {p : ℝ[X]} (hne : (realRootedTimes p).Nonempty) {t : ℝ}
    (ht : lambda p < t) : t ∈ realRootedTimes p := by
  obtain ⟨s, hs, hst⟩ := exists_lt_of_csInf_lt hne ht
  exact mem_realRootedTimes_of_le hst.le hs

/-- Strictly below the threshold the population is non-empty, when `p` has a pair. -/
theorem not_mem_of_lt_lambda {p : ℝ[X]} (hp : nonreal p ≠ 0) {t : ℝ} (ht : t < lambda p) :
    t ∉ realRootedTimes p := fun h =>
  absurd (csInf_le (bddBelow_realRootedTimes hp) h) (not_le.mpr ht)

/-- A real-rooted polynomial has threshold at most zero. -/
theorem lambda_nonpos {p : ℝ[X]} (hp : nonreal p = 0) : lambda p ≤ 0 := by
  have h0 : (0 : ℝ) ∈ realRootedTimes p := by
    rw [mem_realRootedTimes, heatR_zero]
    exact hp
  by_cases hb : BddBelow (realRootedTimes p)
  · exact csInf_le hb h0
  · rw [lambda, Real.sInf_of_not_bddBelow hb]

/-- Each coefficient of `heatR t p` is continuous in `t`. -/
theorem continuous_coeff_heatR (p : ℝ[X]) (j : ℕ) : Continuous fun t : ℝ => (heatR t p).coeff j := by
  have : (fun t : ℝ => (heatR t p).coeff j) = fun t =>
      ∑ k ∈ range (p.natDegree + 1), ((-t) ^ k / (k.factorial : ℝ)) * (derivative^[2 * k] p).coeff j := by
    funext t
    unfold heatR
    rw [finsetSum_coeff]
    apply Finset.sum_congr rfl
    intro k _
    rw [coeff_C_mul]
  rw [this]
  apply continuous_finsetSum
  intro k _
  exact ((continuous_neg.pow k).div_const _).mul continuous_const

/-- The flow is continuous at `t = 0` in the sense of Hurwitz: real-rootedness for all `t > 0`
forces real-rootedness at `t = 0`. -/
theorem nonreal_eq_zero_of_forall_pos {p : ℝ[X]} (h : ∀ t : ℝ, 0 < t → nonreal (heatR t p) = 0) :
    nonreal p = 0 := by
  have hlim : ∀ j, Filter.Tendsto (fun N : ℕ => (heatR (1 / ((N : ℝ) + 1)) p).coeff j)
      Filter.atTop (nhds (p.coeff j)) := by
    intro j
    have := ((continuous_coeff_heatR p j).tendsto 0).comp tendsto_one_div_add_atTop_nhds_zero_nat
    simpa [Function.comp_def, heatR_zero] using this
  by_cases hp0 : p = 0
  · subst hp0
    simp [nonreal]
  have hle := nonreal_le_of_tendsto (n := p.natDegree) (fun N => natDegree_heatR_le _ _) le_rfl hlim hp0
  have hev : ∀ᶠ N : ℕ in Filter.atTop, nonreal (heatR (1 / ((N : ℝ) + 1)) p) = 0 :=
    Filter.Eventually.of_forall fun N => h _ (by positivity)
  obtain ⟨N, hN⟩ := (hle.and hev).exists
  omega

/-- The polynomial face of `RH ⟺ Λ ≤ 0`: given some real-rooted time, `p` is real-rooted iff its
de Bruijn–Newman threshold is at most zero. -/
theorem nonreal_eq_zero_iff_lambda_nonpos {p : ℝ[X]} (hne : (realRootedTimes p).Nonempty) :
    nonreal p = 0 ↔ lambda p ≤ 0 := by
  constructor
  · exact lambda_nonpos
  · intro hl
    apply nonreal_eq_zero_of_forall_pos
    intro t ht
    exact mem_of_lambda_lt hne (lt_of_le_of_lt hl ht)

end Soma.Holonics.RH.DeBruijnNewmanPolynomial
