import ElementaryHolonics.Mathematics.CopsonDeBruijnOrbitConvergence

/-!
# Moving-root basin transport for the normalized Copson--de Bruijn orbit

This owner isolates the deterministic basin geometry preceding the harmonic-divergence argument.
The normalized update is monotone on the nonnegative ray; both moving roots are exact fixed points
once they lie beyond the source offset; and the expanding closed interval between them is forward
invariant for the actual admissible orbit.

The first remaining theorem is the signed harmonic-drift exclusion for a convergent monotone basin.
Plain passage to the limit in the squared normalized step is tautological and is deliberately not
used as a substitute for that summation theorem.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

open Set Filter Topology

/-- One normalized update at aperture `n`. -/
def normalizedUpdate (x : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  x / (n + 2 : ℝ) +
    Real.sqrt (((n + 1 : ℝ) * z ^ 2 - 1) / (n + 2 : ℝ))

theorem normalizedRecurrenceValue_succ_eq_update {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) (n : ℕ) :
    normalizedRecurrenceValue x (n + 1) =
      normalizedUpdate x n (normalizedRecurrenceValue x n) := by
  exact normalizedRecurrenceValue_succ recurrence n

/-- The normalized update is monotone on the nonnegative ray. -/
theorem normalizedUpdate_monoOn_nonnegative (x : ℝ) (n : ℕ) :
    MonotoneOn (normalizedUpdate x n) (Set.Ici 0) := by
  intro left hleft right hright hlr
  unfold normalizedUpdate
  have hsquare : left ^ 2 ≤ right ^ 2 := (sq_le_sq₀ hleft (hleft.trans hlr)).2 hlr
  exact add_le_add le_rfl (Real.sqrt_le_sqrt
    (div_le_div_of_nonneg_right (by nlinarith) (by positivity)))

/-- A zero of the finite drift polynomial beyond the source offset is an exact fixed point of the
principal normalized update. -/
theorem normalizedUpdate_eq_self_of_quadratic_eq_zero {x z : ℝ} {n : ℕ}
    (hoffset : x / (n + 2 : ℝ) ≤ z)
    (hquadratic : normalizedDriftQuadratic x n z = 0) :
    normalizedUpdate x n z = z := by
  have hscale : 0 < (n + 2 : ℝ) := by positivity
  have hradicand : (((n + 1 : ℝ) * z ^ 2 - 1) / (n + 2 : ℝ)) =
      (z - x / (n + 2 : ℝ)) ^ 2 := by
    unfold normalizedDriftQuadratic at hquadratic
    field_simp [hscale.ne'] at hquadratic ⊢
    nlinarith
  unfold normalizedUpdate
  rw [hradicand, Real.sqrt_sq (sub_nonneg.mpr hoffset)]
  ring

theorem normalizedDriftQuadratic_lowerDriftRoot_eq_zero {x : ℝ} {n : ℕ}
    (hdisc : 0 ≤ normalizedDiscriminant x n) :
    normalizedDriftQuadratic x n (lowerDriftRoot x n) = 0 := by
  rw [normalizedDriftQuadratic_factor hdisc]
  simp

theorem normalizedDriftQuadratic_upperDriftRoot_eq_zero {x : ℝ} {n : ℕ}
    (hdisc : 0 ≤ normalizedDiscriminant x n) :
    normalizedDriftQuadratic x n (upperDriftRoot x n) = 0 := by
  rw [normalizedDriftQuadratic_factor hdisc]
  simp

theorem normalizedUpdate_lowerDriftRoot {x : ℝ} {n : ℕ}
    (hdisc : 0 ≤ normalizedDiscriminant x n)
    (hoffset : x / (n + 2 : ℝ) ≤ lowerDriftRoot x n) :
    normalizedUpdate x n (lowerDriftRoot x n) = lowerDriftRoot x n :=
  normalizedUpdate_eq_self_of_quadratic_eq_zero hoffset
    (normalizedDriftQuadratic_lowerDriftRoot_eq_zero hdisc)

theorem normalizedUpdate_upperDriftRoot {x : ℝ} {n : ℕ}
    (hdisc : 0 ≤ normalizedDiscriminant x n)
    (hoffset : x / (n + 2 : ℝ) ≤ lowerDriftRoot x n) :
    normalizedUpdate x n (upperDriftRoot x n) = upperDriftRoot x n := by
  apply normalizedUpdate_eq_self_of_quadratic_eq_zero
  · exact hoffset.trans (lowerDriftRoot_le_upperDriftRoot x n)
  · exact normalizedDriftQuadratic_upperDriftRoot_eq_zero hdisc

theorem lowerAsymptoticRoot_pos {x : ℝ} (hx : 1 < x) :
    0 < lowerAsymptoticRoot x := by
  have hx0 : 0 ≤ x := (zero_lt_one.trans hx).le
  have hdisc : 0 ≤ x ^ 2 - 1 := by nlinarith
  have hsqrtLt : Real.sqrt (x ^ 2 - 1) < x := by
    have h := Real.sqrt_lt_sqrt hdisc (show x ^ 2 - 1 < x ^ 2 by linarith)
    simpa [Real.sqrt_sq hx0] using h
  unfold lowerAsymptoticRoot
  linarith

/-- Eventually both moving roots lie strictly beyond the vanishing source offset. -/
theorem eventually_sourceOffset_lt_lowerDriftRoot {x : ℝ} (hx : 1 < x) :
    ∀ᶠ n : ℕ in atTop, x / ((n : ℝ) + 2) < lowerDriftRoot x n := by
  let lower := lowerAsymptoticRoot x
  have hlower : 0 < lower := lowerAsymptoticRoot_pos hx
  have hden : Tendsto (fun n : ℕ ↦ (n : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hsource : Tendsto (fun n : ℕ ↦ x / ((n : ℝ) + 2)) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop hden
  have hsourceSmall : ∀ᶠ n : ℕ in atTop, x / ((n : ℝ) + 2) < lower / 2 :=
    hsource.eventually (Iio_mem_nhds (half_pos hlower))
  have hrootLarge : ∀ᶠ n : ℕ in atTop, lower / 2 < lowerDriftRoot x n :=
    (tendsto_lowerDriftRoot x).eventually (Ioi_mem_nhds (half_lt_self hlower))
  filter_upwards [hsourceSmall, hrootLarge] with n hsourceN hrootN
  exact hsourceN.trans hrootN

/-- The closed moving-root interval is carried into itself by one normalized update. -/
theorem normalizedUpdate_mem_movingRootInterval {x z : ℝ} {n : ℕ}
    (hx : 0 ≤ x) (hdisc : 0 ≤ normalizedDiscriminant x n)
    (hoffset : x / (n + 2 : ℝ) ≤ lowerDriftRoot x n)
    (hz : z ∈ Set.Icc (lowerDriftRoot x n) (upperDriftRoot x n)) :
    normalizedUpdate x n z ∈ Set.Icc (lowerDriftRoot x n) (upperDriftRoot x n) := by
  have hlowerNonnegative : 0 ≤ lowerDriftRoot x n :=
    (div_nonneg hx (by positivity)).trans hoffset
  have hzNonnegative : 0 ≤ z := hlowerNonnegative.trans hz.1
  have hupperNonnegative : 0 ≤ upperDriftRoot x n := hzNonnegative.trans hz.2
  constructor
  · rw [← normalizedUpdate_lowerDriftRoot hdisc hoffset]
    exact normalizedUpdate_monoOn_nonnegative x n hlowerNonnegative hzNonnegative hz.1
  · rw [← normalizedUpdate_upperDriftRoot hdisc hoffset]
    exact normalizedUpdate_monoOn_nonnegative x n hzNonnegative hupperNonnegative hz.2

/-- Inside the closed moving-root interval, the actual normalized orbit does not decrease. -/
theorem normalizedRecurrenceValue_nondec_of_mem_movingRootInterval {x : ℝ}
    (recurrence : AdmissibleRealRecurrence x) {n : ℕ}
    (hoffset : x / (n + 2 : ℝ) < normalizedRecurrenceValue x n)
    (hoffsetRoot : x / (n + 2 : ℝ) ≤ lowerDriftRoot x n)
    (hdisc : 0 < normalizedDiscriminant x n)
    (hz : normalizedRecurrenceValue x n ∈
      Set.Icc (lowerDriftRoot x n) (upperDriftRoot x n)) :
    normalizedRecurrenceValue x n ≤ normalizedRecurrenceValue x (n + 1) := by
  rcases lt_or_eq_of_le hz.1 with hlower | hlower
  · rcases lt_or_eq_of_le hz.2 with hupper | hupper
    · exact (normalizedRecurrenceValue_drift_pos_iff_between recurrence n hoffset hdisc).2
        ⟨hlower, hupper⟩ |>.le
    · have heq : normalizedRecurrenceValue x n = normalizedRecurrenceValue x (n + 1) := by
        calc
          normalizedRecurrenceValue x n = upperDriftRoot x n := hupper
          _ = normalizedUpdate x n (upperDriftRoot x n) :=
            (normalizedUpdate_upperDriftRoot hdisc.le hoffsetRoot).symm
          _ = normalizedUpdate x n (normalizedRecurrenceValue x n) := by rw [hupper]
          _ = normalizedRecurrenceValue x (n + 1) :=
            (normalizedRecurrenceValue_succ_eq_update recurrence n).symm
      exact heq.le
  · have heq : normalizedRecurrenceValue x n = normalizedRecurrenceValue x (n + 1) := by
      calc
        normalizedRecurrenceValue x n = lowerDriftRoot x n := hlower.symm
        _ = normalizedUpdate x n (lowerDriftRoot x n) :=
          (normalizedUpdate_lowerDriftRoot hdisc.le hoffsetRoot).symm
        _ = normalizedUpdate x n (normalizedRecurrenceValue x n) := by rw [← hlower]
        _ = normalizedRecurrenceValue x (n + 1) :=
          (normalizedRecurrenceValue_succ_eq_update recurrence n).symm
    exact heq.le

/-- Once the actual orbit enters the moving-root interval, one step remains in the expanded next
interval and moves weakly upward. -/
theorem normalizedRecurrenceValue_interval_forward {x : ℝ} (hx : 0 ≤ x)
    (recurrence : AdmissibleRealRecurrence x) {n : ℕ}
    (hoffsetOrbit : x / (n + 2 : ℝ) < normalizedRecurrenceValue x n)
    (hdisc : 0 < normalizedDiscriminant x n)
    (hoffsetRoot : x / (n + 2 : ℝ) ≤ lowerDriftRoot x n)
    (hz : normalizedRecurrenceValue x n ∈
      Set.Icc (lowerDriftRoot x n) (upperDriftRoot x n)) :
    normalizedRecurrenceValue x n ≤ normalizedRecurrenceValue x (n + 1) ∧
      normalizedRecurrenceValue x (n + 1) ∈
        Set.Icc (lowerDriftRoot x (n + 1)) (upperDriftRoot x (n + 1)) := by
  have hstay := normalizedUpdate_mem_movingRootInterval hx hdisc.le hoffsetRoot hz
  rw [← normalizedRecurrenceValue_succ_eq_update recurrence] at hstay
  refine ⟨normalizedRecurrenceValue_nondec_of_mem_movingRootInterval recurrence
    hoffsetOrbit hoffsetRoot hdisc hz, ?_⟩
  exact ⟨(lowerDriftRoot_antitone x (Nat.le_succ n)).trans hstay.1,
    hstay.2.trans (upperDriftRoot_monotone x (Nat.le_succ n))⟩

/-- An entered moving-root interval remains entered at every later aperture. -/
theorem normalizedRecurrenceValue_mem_interval_of_entry {x : ℝ} (hx : 0 ≤ x)
    (recurrence : AdmissibleRealRecurrence x) {N : ℕ}
    (region : ∀ n, N ≤ n →
      x / (n + 2 : ℝ) < normalizedRecurrenceValue x n ∧
        0 < normalizedDiscriminant x n ∧
          x / (n + 2 : ℝ) ≤ lowerDriftRoot x n)
    (entry : normalizedRecurrenceValue x N ∈
      Set.Icc (lowerDriftRoot x N) (upperDriftRoot x N)) :
    ∀ k, normalizedRecurrenceValue x (N + k) ∈
      Set.Icc (lowerDriftRoot x (N + k)) (upperDriftRoot x (N + k)) := by
  intro k
  induction k with
  | zero => simpa using entry
  | succ k ih =>
      have hregion := region (N + k) (Nat.le_add_right N k)
      have hforward := normalizedRecurrenceValue_interval_forward hx recurrence
        hregion.1 hregion.2.1 hregion.2.2 ih
      simpa [Nat.add_assoc] using hforward.2

/-- After interval entry, the normalized orbit is a monotone tail. -/
theorem normalizedRecurrenceValue_monotone_tail_of_entry {x : ℝ} (hx : 0 ≤ x)
    (recurrence : AdmissibleRealRecurrence x) {N : ℕ}
    (region : ∀ n, N ≤ n →
      x / (n + 2 : ℝ) < normalizedRecurrenceValue x n ∧
        0 < normalizedDiscriminant x n ∧
          x / (n + 2 : ℝ) ≤ lowerDriftRoot x n)
    (entry : normalizedRecurrenceValue x N ∈
      Set.Icc (lowerDriftRoot x N) (upperDriftRoot x N)) :
    Monotone (fun k ↦ normalizedRecurrenceValue x (N + k)) := by
  apply monotone_nat_of_le_succ
  intro k
  have hregion := region (N + k) (Nat.le_add_right N k)
  have hmem := normalizedRecurrenceValue_mem_interval_of_entry hx recurrence region entry k
  have hforward := normalizedRecurrenceValue_interval_forward hx recurrence
    hregion.1 hregion.2.1 hregion.2.2 hmem
  simpa [Nat.add_assoc] using hforward.1

/-!
The next atomic owner must iterate `normalizedRecurrenceValue_interval_forward` and its two exterior
analogues, then prove the signed harmonic-drift exclusion.  The latter is the first missing theorem:
an eventually monotone bounded orbit with `|normalizedDriftQuadratic x n z_n|` bounded below by a
positive constant contradicts `tendsto_sum_range_one_div_nat_succ_atTop` through
`normalizedDrift_compact_lower_bound`.
-/

section Audit

#print axioms normalizedUpdate_monoOn_nonnegative
#print axioms normalizedUpdate_eq_self_of_quadratic_eq_zero
#print axioms normalizedUpdate_lowerDriftRoot
#print axioms normalizedUpdate_upperDriftRoot
#print axioms eventually_sourceOffset_lt_lowerDriftRoot
#print axioms normalizedUpdate_mem_movingRootInterval
#print axioms normalizedRecurrenceValue_interval_forward
#print axioms normalizedRecurrenceValue_mem_interval_of_entry
#print axioms normalizedRecurrenceValue_monotone_tail_of_entry

end Audit

end Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail
