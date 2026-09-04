import ElementaryHolonics.Mathematics.CopsonDeBruijnOrbitDichotomy
import ElementaryHolonics.Mathematics.CopsonDeBruijnHarmonicDrift
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Limit classification for normalized Copson--de Bruijn orbit basins

This file composes moving-root basin transport with rationalized harmonic drift.  Its first owner
classifies every already-convergent positive normalized orbit: the limit must be one of the two
roots `x ± sqrt (x²-1)`.  The proof does not obtain this from the pointwise limit of the normalized
step, which is tautological.  It uses the non-summable signed `1/(n+2)` current instead.

Global convergence still requires the exterior-basin switching dichotomy.  No convergence or
desired limit is stored in a structure or introduced as an axiom.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

open Set Filter Topology

/-- The autonomous limiting drift is continuous along a positive convergent orbit. -/
theorem tendsto_limitingNormalizedDrift {x limit : ℝ}
    {value : ℕ → ℝ} (hvalue : Tendsto value atTop (nhds limit))
    (hlimit : 0 < limit) :
    Tendsto (fun n ↦ limitingNormalizedDrift x (value n)) atTop
      (nhds (limitingNormalizedDrift x limit)) := by
  unfold limitingNormalizedDrift
  have hnum : Tendsto (fun n ↦ value n ^ 2 + 1) atTop (nhds (limit ^ 2 + 1)) :=
    (hvalue.pow 2).add_const 1
  have hden : Tendsto (fun n ↦ 2 * value n) atTop (nhds (2 * limit)) :=
    tendsto_const_nhds.mul hvalue
  exact tendsto_const_nhds.sub (hnum.div hden (by positivity))

/-- On a convergent positive normalized orbit, the compact drift approximation error vanishes. -/
theorem tendsto_abs_scaledDrift_sub_limitingDrift_zero {x limit : ℝ}
    (_hx : 1 < x) (recurrence : AdmissibleRealRecurrence x)
    (hvalue : Tendsto (normalizedRecurrenceValue x) atTop (nhds limit))
    (hlimit : 0 < limit) :
    Tendsto
      (fun n : ℕ ↦ |((n : ℝ) + 2) *
          (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) -
        limitingNormalizedDrift x (normalizedRecurrenceValue x n)|)
      atTop (nhds 0) := by
  let epsilon := limit / 2
  let bound := 2 * x
  let errorBound : ℕ → ℝ := fun n ↦
    (bound ^ 2 + 1) ^ 2 / (2 * epsilon ^ 3 * ((n : ℝ) + 2))
  have hepsilon : 0 < epsilon := half_pos hlimit
  have hbound : ∀ n, normalizedRecurrenceValue x n ≤ bound :=
    normalizedRecurrenceValue_le_two_mul recurrence
  have hlower : ∀ᶠ n : ℕ in atTop, epsilon ≤ normalizedRecurrenceValue x n :=
    hvalue.eventually (Ici_mem_nhds (by dsimp [epsilon]; linarith))
  have hnonneg : ∀ n : ℕ,
      0 ≤ |((n : ℝ) + 2) *
          (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) -
        limitingNormalizedDrift x (normalizedRecurrenceValue x n)| := fun _ ↦ abs_nonneg _
  have hle : ∀ᶠ n : ℕ in atTop,
      |((n : ℝ) + 2) *
          (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) -
        limitingNormalizedDrift x (normalizedRecurrenceValue x n)| ≤ errorBound n := by
    filter_upwards [hlower] with n hn
    exact abs_scaledDrift_sub_limitingDrift_le recurrence n hepsilon hn (hbound n)
  have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hboundLimit : Tendsto errorBound atTop (nhds 0) := by
    dsimp [errorBound]
    exact tendsto_const_nhds.div_atTop
      (hden.const_mul_atTop (by positivity : 0 < 2 * epsilon ^ 3))
  exact squeeze_zero' (Eventually.of_forall hnonneg) hle hboundLimit

/-- The scaled finite drift converges to the autonomous drift at every positive orbit limit. -/
theorem tendsto_scaledDrift {x limit : ℝ}
    (hx : 1 < x) (recurrence : AdmissibleRealRecurrence x)
    (hvalue : Tendsto (normalizedRecurrenceValue x) atTop (nhds limit))
    (hlimit : 0 < limit) :
    Tendsto
      (fun n : ℕ ↦ ((n : ℝ) + 2) *
        (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n))
      atTop (nhds (limitingNormalizedDrift x limit)) := by
  have habs := tendsto_abs_scaledDrift_sub_limitingDrift_zero hx recurrence hvalue hlimit
  have hdiff : Tendsto
      (fun n : ℕ ↦ ((n : ℝ) + 2) *
          (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) -
        limitingNormalizedDrift x (normalizedRecurrenceValue x n))
      atTop (nhds 0) := by
    rwa [tendsto_zero_iff_abs_tendsto_zero]
  have hlimiting := tendsto_limitingNormalizedDrift (x := x) hvalue hlimit
  convert hdiff.add hlimiting using 1
  · funext n
    ring
  · ring

theorem quarter_div_nat_succ_le_half_div_nat_add_two {d : ℝ} (hd : 0 ≤ d) (n : ℕ) :
    (d / 4) / ((n : ℝ) + 1) ≤ (d / 2) / ((n : ℝ) + 2) := by
  field_simp
  nlinarith

/-- Harmonic divergence forces the autonomous drift to vanish at every positive actual orbit
limit. -/
theorem limitingNormalizedDrift_eq_zero_of_tendsto {x limit : ℝ}
    (hx : 1 < x) (recurrence : AdmissibleRealRecurrence x)
    (hvalue : Tendsto (normalizedRecurrenceValue x) atTop (nhds limit))
    (hlimit : 0 < limit) :
    limitingNormalizedDrift x limit = 0 := by
  let drift := limitingNormalizedDrift x limit
  have hscaled := tendsto_scaledDrift hx recurrence hvalue hlimit
  apply le_antisymm
  · apply le_of_not_gt
    intro hdrift
    have hevent : ∀ᶠ n : ℕ in atTop,
        drift / 2 ≤ ((n : ℝ) + 2) *
          (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) :=
      hscaled.eventually (Ici_mem_nhds (half_lt_self hdrift))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    exfalso
    apply harmonic_positive_drift_impossible_of_upper N (show 0 < drift / 4 by positivity)
      (upper := 2 * x) (v := normalizedRecurrenceValue x)
    · intro n _hn
      exact normalizedRecurrenceValue_le_two_mul recurrence n
    · intro n hn
      have hscaledN := hN n hn
      have hdiv : drift / 2 / ((n : ℝ) + 2) ≤
          normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
        simpa [mul_comm] using hscaledN
      have hquarter := quarter_div_nat_succ_le_half_div_nat_add_two hdrift.le n
      linarith
  · apply le_of_not_gt
    intro hnegative
    have hnegDrift : 0 < -drift := neg_pos.mpr hnegative
    have hevent : ∀ᶠ n : ℕ in atTop,
        ((n : ℝ) + 2) *
          (normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) ≤ drift / 2 :=
      hscaled.eventually (Iic_mem_nhds (by linarith : drift < drift / 2))
    obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
    exfalso
    apply harmonic_negative_drift_impossible_of_lower N
      (show 0 < (-drift) / 4 by positivity) (lower := 0)
      (v := normalizedRecurrenceValue x)
    · intro n _hn
      exact (normalizedRecurrenceValue_pos recurrence n).le
    · intro n hn
      have hscaledN := hN n hn
      have hdiv : (-drift) / 2 / ((n : ℝ) + 2) ≤
          normalizedRecurrenceValue x n - normalizedRecurrenceValue x (n + 1) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
        nlinarith
      have hquarter := quarter_div_nat_succ_le_half_div_nat_add_two hnegDrift.le n
      linarith

/-- Every positive normalized-orbit limit is one of the two characteristic roots. -/
theorem limit_eq_lower_or_upper_of_tendsto {x limit : ℝ}
    (hx : 1 < x) (recurrence : AdmissibleRealRecurrence x)
    (hvalue : Tendsto (normalizedRecurrenceValue x) atTop (nhds limit))
    (hlimit : 0 < limit) :
    limit = lowerAsymptoticRoot x ∨ limit = upperAsymptoticRoot x := by
  have hdrift := limitingNormalizedDrift_eq_zero_of_tendsto hx recurrence hvalue hlimit
  have hquadratic : limit ^ 2 - 2 * x * limit + 1 = 0 := by
    unfold limitingNormalizedDrift at hdrift
    field_simp [hlimit.ne'] at hdrift
    nlinarith
  have hdisc : 0 ≤ x ^ 2 - 1 := by nlinarith
  have hfactor : (limit - lowerAsymptoticRoot x) *
      (limit - upperAsymptoticRoot x) = 0 := by
    unfold lowerAsymptoticRoot upperAsymptoticRoot
    have hsqrt := Real.sq_sqrt hdisc
    nlinarith
  rcases mul_eq_zero.mp hfactor with hlower | hupper
  · exact Or.inl (sub_eq_zero.mp hlower)
  · exact Or.inr (sub_eq_zero.mp hupper)

/-! The same classifier without a prior positive-limit hypothesis.  This version works directly
with the polynomial drift and the compact harmonic bound. -/

def limitingDriftQuadratic (x z : ℝ) : ℝ := z ^ 2 - 2 * x * z + 1

theorem tendsto_normalizedDriftQuadratic_of_tendsto {x L : ℝ}
    (hlim : Tendsto (normalizedRecurrenceValue x) atTop (nhds L)) :
    Tendsto
      (fun n : ℕ ↦ normalizedDriftQuadratic x n (normalizedRecurrenceValue x n))
      atTop (nhds (limitingDriftQuadratic x L)) := by
  have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun n : ℕ ↦ x ^ 2 / ((n : ℝ) + 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hbase : Tendsto
      (fun n : ℕ ↦ normalizedRecurrenceValue x n ^ 2 -
        2 * x * normalizedRecurrenceValue x n + 1)
      atTop (nhds (L ^ 2 - 2 * x * L + 1)) := by
    have hconst : Tendsto (fun _ : ℕ ↦ 2 * x) atTop (nhds (2 * x)) :=
      tendsto_const_nhds
    simpa [mul_assoc] using
      (((hlim.pow 2).sub (hconst.mul hlim)).add_const 1)
  unfold normalizedDriftQuadratic limitingDriftQuadratic
  simpa using hbase.add hsmall

theorem limitingDriftQuadratic_factor {x z : ℝ} (hx : 1 ≤ x) :
    limitingDriftQuadratic x z =
      (z - lowerAsymptoticRoot x) * (z - upperAsymptoticRoot x) := by
  have hdisc : 0 ≤ x ^ 2 - 1 := by nlinarith
  have hsqrt := Real.sq_sqrt hdisc
  unfold limitingDriftQuadratic lowerAsymptoticRoot upperAsymptoticRoot
  nlinarith

theorem half_div_nat_succ_le_div_nat_add_two {gamma : ℝ}
    (hgamma : 0 ≤ gamma) (n : ℕ) :
    (gamma / 2) / ((n : ℝ) + 1) ≤ gamma / ((n : ℝ) + 2) := by
  rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < n + 1)
    (by positivity : (0 : ℝ) < n + 2)]
  nlinarith

/-- Any actual finite limit of an admissible normalized orbit is a zero of the limiting drift. -/
theorem limitingDriftQuadratic_eq_zero_of_tendsto {x L : ℝ} (hx : 1 < x)
    (recurrence : AdmissibleRealRecurrence x)
    (hlim : Tendsto (normalizedRecurrenceValue x) atTop (nhds L)) :
    limitingDriftQuadratic x L = 0 := by
  let q := limitingDriftQuadratic x L
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hquad := tendsto_normalizedDriftQuadratic_of_tendsto hlim
  change Tendsto
    (fun n : ℕ ↦ normalizedDriftQuadratic x n (normalizedRecurrenceValue x n))
    atTop (nhds q) at hquad
  rcases lt_trichotomy q 0 with hqneg | hqzero | hqpos
  · have hhalf : q < q / 2 := by linarith
    have hqEventually : ∀ᶠ n : ℕ in atTop,
        normalizedDriftQuadratic x n (normalizedRecurrenceValue x n) < q / 2 :=
      hquad.eventually (Iio_mem_nhds hhalf)
    have hregion := eventually_normalized_dynamics_region hx recurrence
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hqEventually.and hregion)
    let gamma : ℝ := (-q) / (8 * x)
    have hgamma : 0 < gamma := by
      dsimp [gamma]
      exact div_pos (neg_pos.mpr hqneg) (mul_pos (by norm_num) hx0)
    exfalso
    apply harmonic_positive_drift_impossible_of_upper N (half_pos hgamma)
      (v := normalizedRecurrenceValue x) (upper := 2 * x)
    · intro n _hn
      exact normalizedRecurrenceValue_le_two_mul recurrence n
    · intro n hn
      have hdata := hN n hn
      have hQ : normalizedDriftQuadratic x n (normalizedRecurrenceValue x n) < 0 :=
        hdata.1.trans (by linarith [hqneg])
      have hdrift : normalizedRecurrenceValue x n < normalizedRecurrenceValue x (n + 1) :=
        (normalizedRecurrenceValue_drift_pos_iff_quadratic_neg recurrence n
          hdata.2.1).2 hQ
      have hcompact := normalizedDrift_compact_lower_bound hx recurrence n hdata.2.1
      have habQ : -q / 2 ≤
          |normalizedDriftQuadratic x n (normalizedRecurrenceValue x n)| := by
        rw [abs_of_neg hQ]
        linarith [hdata.1]
      have hmag : gamma / ((n : ℝ) + 2) ≤
          |normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n| := by
        calc
          gamma / ((n : ℝ) + 2) =
              (-q / 2) / (4 * x * ((n : ℝ) + 2)) := by
                dsimp [gamma]
                field_simp
                ring
          _ ≤ |normalizedDriftQuadratic x n (normalizedRecurrenceValue x n)| /
              (4 * x * ((n : ℝ) + 2)) :=
                div_le_div_of_nonneg_right habQ (by positivity)
          _ ≤ _ := hcompact
      have hclock := half_div_nat_succ_le_div_nat_add_two hgamma.le n
      have habDrift :
          |normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n| =
            normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n :=
        abs_of_pos (sub_pos.mpr hdrift)
      rw [habDrift] at hmag
      linarith [hclock.trans hmag]
  · exact hqzero
  · have hhalf : q / 2 < q := by linarith
    have hqEventually : ∀ᶠ n : ℕ in atTop,
        q / 2 < normalizedDriftQuadratic x n (normalizedRecurrenceValue x n) :=
      hquad.eventually (Ioi_mem_nhds hhalf)
    have hregion := eventually_normalized_dynamics_region hx recurrence
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hqEventually.and hregion)
    let gamma : ℝ := q / (8 * x)
    have hgamma : 0 < gamma := by
      dsimp [gamma]
      exact div_pos hqpos (mul_pos (by norm_num) hx0)
    exfalso
    apply harmonic_negative_drift_impossible_of_lower N (half_pos hgamma)
      (v := normalizedRecurrenceValue x) (lower := 0)
    · intro n _hn
      exact (normalizedRecurrenceValue_pos recurrence n).le
    · intro n hn
      have hdata := hN n hn
      have hQ : 0 < normalizedDriftQuadratic x n (normalizedRecurrenceValue x n) :=
        (half_pos hqpos).trans hdata.1
      have houtside :=
        (normalizedDriftQuadratic_pos_iff_outside hdata.2.2
          (normalizedRecurrenceValue x n)).1 hQ
      have hdrift : normalizedRecurrenceValue x (n + 1) < normalizedRecurrenceValue x n :=
        (normalizedRecurrenceValue_drift_neg_iff_outside recurrence n
          hdata.2.1 hdata.2.2).2 houtside
      have hcompact := normalizedDrift_compact_lower_bound hx recurrence n hdata.2.1
      have habQ : q / 2 ≤
          |normalizedDriftQuadratic x n (normalizedRecurrenceValue x n)| := by
        rw [abs_of_pos hQ]
        exact hdata.1.le
      have hmag : gamma / ((n : ℝ) + 2) ≤
          |normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n| := by
        calc
          gamma / ((n : ℝ) + 2) =
              (q / 2) / (4 * x * ((n : ℝ) + 2)) := by
                dsimp [gamma]
                field_simp
                ring
          _ ≤ |normalizedDriftQuadratic x n (normalizedRecurrenceValue x n)| /
              (4 * x * ((n : ℝ) + 2)) :=
                div_le_div_of_nonneg_right habQ (by positivity)
          _ ≤ _ := hcompact
      have hclock := half_div_nat_succ_le_div_nat_add_two hgamma.le n
      have habDrift :
          |normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n| =
            -(normalizedRecurrenceValue x (n + 1) - normalizedRecurrenceValue x n) :=
        abs_of_neg (sub_neg.mpr hdrift)
      rw [habDrift] at hmag
      linarith [hclock.trans hmag]

theorem tendsto_limit_eq_lower_or_upper {x L : ℝ} (hx : 1 < x)
    (recurrence : AdmissibleRealRecurrence x)
    (hlim : Tendsto (normalizedRecurrenceValue x) atTop (nhds L)) :
    L = lowerAsymptoticRoot x ∨ L = upperAsymptoticRoot x := by
  have hzero := limitingDriftQuadratic_eq_zero_of_tendsto hx recurrence hlim
  rw [limitingDriftQuadratic_factor hx.le] at hzero
  rcases mul_eq_zero.mp hzero with h | h
  · exact Or.inl (sub_eq_zero.mp h)
  · exact Or.inr (sub_eq_zero.mp h)

/-! ## Exterior basin transport and the exact eventual trichotomy -/

theorem normalizedRecurrenceValue_below_forward_or_interval {x : ℝ} (hx : 0 ≤ x)
    (recurrence : AdmissibleRealRecurrence x) {n : ℕ}
    (hoffsetOrbit : x / (n + 2 : ℝ) < normalizedRecurrenceValue x n)
    (hdisc : 0 < normalizedDiscriminant x n)
    (hoffsetRoot : x / (n + 2 : ℝ) ≤ lowerDriftRoot x n)
    (hbelow : normalizedRecurrenceValue x n < lowerDriftRoot x n) :
    normalizedRecurrenceValue x (n + 1) < normalizedRecurrenceValue x n ∧
      (normalizedRecurrenceValue x (n + 1) < lowerDriftRoot x (n + 1) ∨
        normalizedRecurrenceValue x (n + 1) ∈
          Set.Icc (lowerDriftRoot x (n + 1)) (upperDriftRoot x (n + 1))) := by
  have hdecrease :=
    (normalizedRecurrenceValue_drift_neg_iff_outside recurrence n hoffsetOrbit hdisc).2
      (Or.inl hbelow)
  have hrootNonnegative : 0 ≤ lowerDriftRoot x n :=
    (div_nonneg hx (by positivity)).trans hoffsetRoot
  have horbitNonnegative : 0 ≤ normalizedRecurrenceValue x n :=
    (normalizedRecurrenceValue_pos recurrence n).le
  have hnextLe : normalizedRecurrenceValue x (n + 1) ≤ lowerDriftRoot x n := by
    calc
      normalizedRecurrenceValue x (n + 1) =
          normalizedUpdate x n (normalizedRecurrenceValue x n) :=
        normalizedRecurrenceValue_succ_eq_update recurrence n
      _ ≤ normalizedUpdate x n (lowerDriftRoot x n) :=
        normalizedUpdate_monoOn_nonnegative x n horbitNonnegative hrootNonnegative hbelow.le
      _ = lowerDriftRoot x n := normalizedUpdate_lowerDriftRoot hdisc.le hoffsetRoot
  refine ⟨hdecrease, ?_⟩
  by_cases hnextBelow :
      normalizedRecurrenceValue x (n + 1) < lowerDriftRoot x (n + 1)
  · exact Or.inl hnextBelow
  · right
    refine ⟨le_of_not_gt hnextBelow, ?_⟩
    exact hnextLe.trans <|
      (lowerDriftRoot_le_upperDriftRoot x n).trans
        (upperDriftRoot_monotone x (Nat.le_succ n))

theorem normalizedRecurrenceValue_above_forward_or_interval {x : ℝ} (hx : 0 ≤ x)
    (recurrence : AdmissibleRealRecurrence x) {n : ℕ}
    (hoffsetOrbit : x / (n + 2 : ℝ) < normalizedRecurrenceValue x n)
    (hdisc : 0 < normalizedDiscriminant x n)
    (hoffsetRoot : x / (n + 2 : ℝ) ≤ lowerDriftRoot x n)
    (habove : upperDriftRoot x n < normalizedRecurrenceValue x n) :
    normalizedRecurrenceValue x (n + 1) < normalizedRecurrenceValue x n ∧
      (upperDriftRoot x (n + 1) < normalizedRecurrenceValue x (n + 1) ∨
        normalizedRecurrenceValue x (n + 1) ∈
          Set.Icc (lowerDriftRoot x (n + 1)) (upperDriftRoot x (n + 1))) := by
  have hdecrease :=
    (normalizedRecurrenceValue_drift_neg_iff_outside recurrence n hoffsetOrbit hdisc).2
      (Or.inr habove)
  have hlowerNonnegative : 0 ≤ lowerDriftRoot x n :=
    (div_nonneg hx (by positivity)).trans hoffsetRoot
  have hupperNonnegative : 0 ≤ upperDriftRoot x n :=
    hlowerNonnegative.trans (lowerDriftRoot_le_upperDriftRoot x n)
  have horbitNonnegative : 0 ≤ normalizedRecurrenceValue x n :=
    (normalizedRecurrenceValue_pos recurrence n).le
  have hupperLeNext : upperDriftRoot x n ≤ normalizedRecurrenceValue x (n + 1) := by
    calc
      upperDriftRoot x n = normalizedUpdate x n (upperDriftRoot x n) :=
        (normalizedUpdate_upperDriftRoot hdisc.le hoffsetRoot).symm
      _ ≤ normalizedUpdate x n (normalizedRecurrenceValue x n) :=
        normalizedUpdate_monoOn_nonnegative x n hupperNonnegative horbitNonnegative habove.le
      _ = normalizedRecurrenceValue x (n + 1) :=
        (normalizedRecurrenceValue_succ_eq_update recurrence n).symm
  refine ⟨hdecrease, ?_⟩
  by_cases hnextAbove :
      upperDriftRoot x (n + 1) < normalizedRecurrenceValue x (n + 1)
  · exact Or.inl hnextAbove
  · right
    refine ⟨?_, le_of_not_gt hnextAbove⟩
    exact (lowerDriftRoot_antitone x (Nat.le_succ n)).trans <|
      (lowerDriftRoot_le_upperDriftRoot x n).trans hupperLeNext

theorem normalizedRecurrenceValue_below_of_no_interval_entry {x : ℝ} (hx : 0 ≤ x)
    (recurrence : AdmissibleRealRecurrence x) {N : ℕ}
    (region : ∀ n, N ≤ n →
      x / (n + 2 : ℝ) < normalizedRecurrenceValue x n ∧
        0 < normalizedDiscriminant x n ∧
          x / (n + 2 : ℝ) ≤ lowerDriftRoot x n)
    (initial : normalizedRecurrenceValue x N < lowerDriftRoot x N)
    (noEntry : ∀ k, ¬ normalizedRecurrenceValue x (N + k) ∈
      Set.Icc (lowerDriftRoot x (N + k)) (upperDriftRoot x (N + k))) :
    ∀ k, normalizedRecurrenceValue x (N + k) < lowerDriftRoot x (N + k) := by
  intro k
  induction k with
  | zero => simpa using initial
  | succ k ih =>
      have hregion := region (N + k) (Nat.le_add_right N k)
      have hforward := normalizedRecurrenceValue_below_forward_or_interval hx recurrence
        hregion.1 hregion.2.1 hregion.2.2 ih
      rcases hforward.2 with hbelow | hentry
      · simpa [Nat.add_assoc] using hbelow
      · exact False.elim <| noEntry (k + 1) (by simpa [Nat.add_assoc] using hentry)

theorem normalizedRecurrenceValue_above_of_no_interval_entry {x : ℝ} (hx : 0 ≤ x)
    (recurrence : AdmissibleRealRecurrence x) {N : ℕ}
    (region : ∀ n, N ≤ n →
      x / (n + 2 : ℝ) < normalizedRecurrenceValue x n ∧
        0 < normalizedDiscriminant x n ∧
          x / (n + 2 : ℝ) ≤ lowerDriftRoot x n)
    (initial : upperDriftRoot x N < normalizedRecurrenceValue x N)
    (noEntry : ∀ k, ¬ normalizedRecurrenceValue x (N + k) ∈
      Set.Icc (lowerDriftRoot x (N + k)) (upperDriftRoot x (N + k))) :
    ∀ k, upperDriftRoot x (N + k) < normalizedRecurrenceValue x (N + k) := by
  intro k
  induction k with
  | zero => simpa using initial
  | succ k ih =>
      have hregion := region (N + k) (Nat.le_add_right N k)
      have hforward := normalizedRecurrenceValue_above_forward_or_interval hx recurrence
        hregion.1 hregion.2.1 hregion.2.2 ih
      rcases hforward.2 with habove | hentry
      · simpa [Nat.add_assoc] using habove
      · exact False.elim <| noEntry (k + 1) (by simpa [Nat.add_assoc] using hentry)

theorem normalizedRecurrenceValue_strictAnti_tail_of_below_no_entry {x : ℝ} (hx : 0 ≤ x)
    (recurrence : AdmissibleRealRecurrence x) {N : ℕ}
    (region : ∀ n, N ≤ n →
      x / (n + 2 : ℝ) < normalizedRecurrenceValue x n ∧
        0 < normalizedDiscriminant x n ∧
          x / (n + 2 : ℝ) ≤ lowerDriftRoot x n)
    (initial : normalizedRecurrenceValue x N < lowerDriftRoot x N)
    (noEntry : ∀ k, ¬ normalizedRecurrenceValue x (N + k) ∈
      Set.Icc (lowerDriftRoot x (N + k)) (upperDriftRoot x (N + k))) :
    StrictAnti (fun k ↦ normalizedRecurrenceValue x (N + k)) := by
  apply strictAnti_nat_of_succ_lt
  intro k
  have hbelow := normalizedRecurrenceValue_below_of_no_interval_entry hx recurrence
    region initial noEntry k
  have hregion := region (N + k) (Nat.le_add_right N k)
  have hdecrease := (normalizedRecurrenceValue_below_forward_or_interval hx recurrence
    hregion.1 hregion.2.1 hregion.2.2 hbelow).1
  simpa [Nat.add_assoc] using hdecrease

theorem normalizedRecurrenceValue_strictAnti_tail_of_above_no_entry {x : ℝ} (hx : 0 ≤ x)
    (recurrence : AdmissibleRealRecurrence x) {N : ℕ}
    (region : ∀ n, N ≤ n →
      x / (n + 2 : ℝ) < normalizedRecurrenceValue x n ∧
        0 < normalizedDiscriminant x n ∧
          x / (n + 2 : ℝ) ≤ lowerDriftRoot x n)
    (initial : upperDriftRoot x N < normalizedRecurrenceValue x N)
    (noEntry : ∀ k, ¬ normalizedRecurrenceValue x (N + k) ∈
      Set.Icc (lowerDriftRoot x (N + k)) (upperDriftRoot x (N + k))) :
    StrictAnti (fun k ↦ normalizedRecurrenceValue x (N + k)) := by
  apply strictAnti_nat_of_succ_lt
  intro k
  have habove := normalizedRecurrenceValue_above_of_no_interval_entry hx recurrence
    region initial noEntry k
  have hregion := region (N + k) (Nat.le_add_right N k)
  have hdecrease := (normalizedRecurrenceValue_above_forward_or_interval hx recurrence
    hregion.1 hregion.2.1 hregion.2.2 habove).1
  simpa [Nat.add_assoc] using hdecrease

theorem normalizedRecurrenceValue_eventual_basin_trichotomy {x : ℝ} (hx : 0 ≤ x)
    (recurrence : AdmissibleRealRecurrence x) {N : ℕ}
    (region : ∀ n, N ≤ n →
      x / (n + 2 : ℝ) < normalizedRecurrenceValue x n ∧
        0 < normalizedDiscriminant x n ∧
          x / (n + 2 : ℝ) ≤ lowerDriftRoot x n) :
    ((∀ k, normalizedRecurrenceValue x (N + k) < lowerDriftRoot x (N + k)) ∧
        StrictAnti (fun k ↦ normalizedRecurrenceValue x (N + k))) ∨
      (∃ k,
        normalizedRecurrenceValue x (N + k) ∈
          Set.Icc (lowerDriftRoot x (N + k)) (upperDriftRoot x (N + k)) ∧
        Monotone (fun j ↦ normalizedRecurrenceValue x ((N + k) + j)) ∧
        ∀ j, normalizedRecurrenceValue x ((N + k) + j) ∈
          Set.Icc (lowerDriftRoot x ((N + k) + j))
            (upperDriftRoot x ((N + k) + j))) ∨
      ((∀ k, upperDriftRoot x (N + k) < normalizedRecurrenceValue x (N + k)) ∧
        StrictAnti (fun k ↦ normalizedRecurrenceValue x (N + k))) := by
  by_cases entryExists : ∃ k, normalizedRecurrenceValue x (N + k) ∈
      Set.Icc (lowerDriftRoot x (N + k)) (upperDriftRoot x (N + k))
  · right
    left
    obtain ⟨k, hentry⟩ := entryExists
    have region' : ∀ n, N + k ≤ n →
        x / (n + 2 : ℝ) < normalizedRecurrenceValue x n ∧
          0 < normalizedDiscriminant x n ∧
            x / (n + 2 : ℝ) ≤ lowerDriftRoot x n := by
      intro n hn
      exact region n ((Nat.le_add_right N k).trans hn)
    refine ⟨k, hentry,
      normalizedRecurrenceValue_monotone_tail_of_entry hx recurrence region' hentry, ?_⟩
    exact normalizedRecurrenceValue_mem_interval_of_entry hx recurrence region' hentry
  · have noEntry : ∀ k, ¬ normalizedRecurrenceValue x (N + k) ∈
        Set.Icc (lowerDriftRoot x (N + k)) (upperDriftRoot x (N + k)) := by
      exact not_exists.mp entryExists
    by_cases hlower : lowerDriftRoot x N ≤ normalizedRecurrenceValue x N
    · right
      right
      have habove : upperDriftRoot x N < normalizedRecurrenceValue x N := by
        apply lt_of_not_ge
        intro hupper
        exact noEntry 0 (by simpa using And.intro hlower hupper)
      exact ⟨normalizedRecurrenceValue_above_of_no_interval_entry hx recurrence
          region habove noEntry,
        normalizedRecurrenceValue_strictAnti_tail_of_above_no_entry hx recurrence
          region habove noEntry⟩
    · left
      have hbelow : normalizedRecurrenceValue x N < lowerDriftRoot x N :=
        lt_of_not_ge hlower
      exact ⟨normalizedRecurrenceValue_below_of_no_interval_entry hx recurrence
          region hbelow noEntry,
        normalizedRecurrenceValue_strictAnti_tail_of_below_no_entry hx recurrence
          region hbelow noEntry⟩

/-! ## Monotone basin limits and branch selection -/

theorem lowerAsymptoticRoot_lt_lowerDriftRoot {x : ℝ} (hx : 1 < x) (n : ℕ) :
    lowerAsymptoticRoot x < lowerDriftRoot x n := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hfinite : normalizedDiscriminant x n < x ^ 2 - 1 := by
    unfold normalizedDiscriminant
    have : 0 < x ^ 2 / (n + 2 : ℝ) := div_pos (sq_pos_of_pos hx0) (by positivity)
    linarith
  by_cases hdisc : 0 ≤ normalizedDiscriminant x n
  · have hsqrt := Real.sqrt_lt_sqrt hdisc hfinite
    unfold lowerAsymptoticRoot lowerDriftRoot
    linarith
  · unfold lowerDriftRoot lowerAsymptoticRoot
    rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hdisc)]
    have hsqrt : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith)
    linarith

theorem upperDriftRoot_lt_upperAsymptoticRoot {x : ℝ} (hx : 1 < x) (n : ℕ) :
    upperDriftRoot x n < upperAsymptoticRoot x := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hfinite : normalizedDiscriminant x n < x ^ 2 - 1 := by
    unfold normalizedDiscriminant
    have : 0 < x ^ 2 / (n + 2 : ℝ) := div_pos (sq_pos_of_pos hx0) (by positivity)
    linarith
  by_cases hdisc : 0 ≤ normalizedDiscriminant x n
  · have hsqrt := Real.sqrt_lt_sqrt hdisc hfinite
    unfold upperDriftRoot upperAsymptoticRoot
    linarith
  · unfold upperDriftRoot upperAsymptoticRoot
    rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hdisc)]
    have hsqrt : 0 < Real.sqrt (x ^ 2 - 1) := Real.sqrt_pos.2 (by nlinarith)
    linarith

theorem tendsto_of_tendsto_nat_add {f : ℕ → ℝ} {L : ℝ} (N : ℕ)
    (h : Tendsto (fun k ↦ f (N + k)) atTop (nhds L)) :
    Tendsto f atTop (nhds L) := by
  apply (tendsto_add_atTop_iff_nat N).mp
  simpa [add_comm] using h

theorem exists_tendsto_root_of_monotone_add_tail {x : ℝ} (hx : 1 < x)
    (recurrence : AdmissibleRealRecurrence x) (N : ℕ)
    (hmono : Monotone (fun k ↦ normalizedRecurrenceValue x (N + k))) :
    ∃ L : ℝ,
      Tendsto (fun k ↦ normalizedRecurrenceValue x (N + k)) atTop (nhds L) ∧
      Tendsto (normalizedRecurrenceValue x) atTop (nhds L) ∧
        (L = lowerAsymptoticRoot x ∨ L = upperAsymptoticRoot x) := by
  have hbdd : BddAbove (Set.range (fun k ↦ normalizedRecurrenceValue x (N + k))) := by
    refine ⟨2 * x, ?_⟩
    rintro y ⟨k, rfl⟩
    exact normalizedRecurrenceValue_le_two_mul recurrence (N + k)
  let L := ⨆ k, normalizedRecurrenceValue x (N + k)
  have htail : Tendsto (fun k ↦ normalizedRecurrenceValue x (N + k)) atTop (nhds L) :=
    tendsto_atTop_ciSup hmono hbdd
  have hfull := tendsto_of_tendsto_nat_add N htail
  exact ⟨L, htail, hfull, tendsto_limit_eq_lower_or_upper hx recurrence hfull⟩

theorem exists_tendsto_root_of_antitone_add_tail {x : ℝ} (hx : 1 < x)
    (recurrence : AdmissibleRealRecurrence x) (N : ℕ)
    (hanti : Antitone (fun k ↦ normalizedRecurrenceValue x (N + k))) :
    ∃ L : ℝ,
      Tendsto (fun k ↦ normalizedRecurrenceValue x (N + k)) atTop (nhds L) ∧
      Tendsto (normalizedRecurrenceValue x) atTop (nhds L) ∧
        (L = lowerAsymptoticRoot x ∨ L = upperAsymptoticRoot x) := by
  have hbdd : BddBelow (Set.range (fun k ↦ normalizedRecurrenceValue x (N + k))) := by
    refine ⟨0, ?_⟩
    rintro y ⟨k, rfl⟩
    exact (normalizedRecurrenceValue_pos recurrence (N + k)).le
  let L := ⨅ k, normalizedRecurrenceValue x (N + k)
  have htail : Tendsto (fun k ↦ normalizedRecurrenceValue x (N + k)) atTop (nhds L) :=
    tendsto_atTop_ciInf hanti hbdd
  have hfull := tendsto_of_tendsto_nat_add N htail
  exact ⟨L, htail, hfull, tendsto_limit_eq_lower_or_upper hx recurrence hfull⟩

/-- Every admissible normalized Copson--de Bruijn orbit above one converges to exactly one of the
two asymptotic roots.  Which branch occurs is selected later by threshold minimality. -/
theorem normalizedRecurrenceValue_tendsto_asymptoticRoot {x : ℝ} (hx : 1 < x)
    (recurrence : AdmissibleRealRecurrence x) :
    Tendsto (normalizedRecurrenceValue x) atTop (nhds (lowerAsymptoticRoot x)) ∨
      Tendsto (normalizedRecurrenceValue x) atTop (nhds (upperAsymptoticRoot x)) := by
  have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
  have hevent := (eventually_normalized_dynamics_region hx recurrence).and
    (eventually_sourceOffset_lt_lowerDriftRoot hx)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hevent
  have region : ∀ n, N ≤ n →
      x / (n + 2 : ℝ) < normalizedRecurrenceValue x n ∧
        0 < normalizedDiscriminant x n ∧
          x / (n + 2 : ℝ) ≤ lowerDriftRoot x n := by
    intro n hn
    have data := hN n hn
    exact ⟨data.1.1, data.1.2, data.2.le⟩
  rcases normalizedRecurrenceValue_eventual_basin_trichotomy hx0 recurrence region with
      hbelow | hmiddle | habove
  · obtain ⟨L, htail, hfull, hroot⟩ :=
      exists_tendsto_root_of_antitone_add_tail hx recurrence N hbelow.2.antitone
    have hrootTail : Tendsto (fun k ↦ lowerDriftRoot x (N + k)) atTop
        (nhds (lowerAsymptoticRoot x)) := by
      have hshift := (tendsto_add_atTop_iff_nat N).mpr (tendsto_lowerDriftRoot x)
      simpa [add_comm] using hshift
    have hlimitLe : L ≤ lowerAsymptoticRoot x :=
      le_of_tendsto_of_tendsto htail hrootTail
        (Eventually.of_forall fun k ↦ (hbelow.1 k).le)
    rcases hroot with hlower | hupper
    · left
      simpa [hlower] using hfull
    · exfalso
      rw [hupper] at hlimitLe
      exact (not_le_of_gt (lowerAsymptoticRoot_lt_upperAsymptoticRoot hx)) hlimitLe
  · rcases hmiddle with ⟨k, hentry, hmono, _hstay⟩
    let K := N + k
    obtain ⟨L, htail, hfull, hroot⟩ :=
      exists_tendsto_root_of_monotone_add_tail hx recurrence K hmono
    have hfirstLe : normalizedRecurrenceValue x K ≤ L :=
      hmono.ge_of_tendsto htail 0
    have hstrict : lowerAsymptoticRoot x < normalizedRecurrenceValue x K :=
      (lowerAsymptoticRoot_lt_lowerDriftRoot hx K).trans_le hentry.1
    rcases hroot with hlower | hupper
    · exfalso
      rw [hlower] at hfirstLe
      exact (not_le_of_gt hstrict) hfirstLe
    · right
      simpa [hupper] using hfull
  · obtain ⟨L, htail, hfull, hroot⟩ :=
      exists_tendsto_root_of_antitone_add_tail hx recurrence N habove.2.antitone
    have hrootTail : Tendsto (fun k ↦ upperDriftRoot x (N + k)) atTop
        (nhds (upperAsymptoticRoot x)) := by
      have hshift := (tendsto_add_atTop_iff_nat N).mpr (tendsto_upperDriftRoot x)
      simpa [add_comm] using hshift
    have hlimitGe : upperAsymptoticRoot x ≤ L :=
      le_of_tendsto_of_tendsto hrootTail htail
        (Eventually.of_forall fun k ↦ (habove.1 k).le)
    rcases hroot with hlower | hupper
    · exfalso
      rw [hlower] at hlimitGe
      exact (not_le_of_gt (lowerAsymptoticRoot_lt_upperAsymptoticRoot hx)) hlimitGe
    · right
      simpa [hupper] using hfull

section Audit

#print axioms limitingNormalizedDrift_eq_zero_of_tendsto
#print axioms limitingDriftQuadratic_eq_zero_of_tendsto
#print axioms tendsto_limit_eq_lower_or_upper
#print axioms normalizedRecurrenceValue_eventual_basin_trichotomy
#print axioms normalizedRecurrenceValue_tendsto_asymptoticRoot

end Audit

end Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail
