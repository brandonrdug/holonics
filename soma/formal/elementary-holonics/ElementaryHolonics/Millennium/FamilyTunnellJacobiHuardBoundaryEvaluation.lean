import ElementaryHolonics.Millennium.FamilyTunnellJacobiHuardSpecialization

/-!
# Exact evaluation of the specialized Huard boundary

This file evaluates the finite divisor-boundary receiver returned by the
Huard source specialization.  Every sum is finite: the boundary product is
flattened into divisor rows, the two interior divisibility faces cancel by
reflection, and the remaining scale faces are transported through explicit
divisor bijections.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiHuardBoundaryEvaluation

open Finset
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiDivisorConvolutionReduction
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardLevelTwoSource
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardSpecialization

/-- Flatten the boundary product into its exact divisor rows. -/
theorem sum_boundaryPairs_eq_rows
    {n : ℕ} (hn : 0 < n) (F : ℕ × ℕ → ℤ) :
    (∑ dt ∈ huardBoundaryPairs n, F dt) =
      ∑ d ∈ n.divisors, ∑ t ∈ Finset.Ico 1 d, F (d, t) := by
  rw [huardBoundaryPairs, Finset.sum_filter]
  calc
    _ = ∑ d ∈ n.divisors, ∑ t ∈ Finset.range n,
        if 0 < t ∧ t < d then F (d, t) else 0 :=
      Finset.sum_product n.divisors (Finset.range n)
        (fun dt => if 0 < dt.2 ∧ dt.2 < dt.1 then F dt else 0)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext t
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
        have hdvd := (Nat.mem_divisors.mp hd).1
        have hdle : d ≤ n := Nat.le_of_dvd hn hdvd
        omega
      · intro t ht
        rfl

/-- The six displayed boundary faces reduce pointwise to one polynomial
face, two scale-indicator faces, and one reflected indicator difference. -/
theorem specializedBoundaryExpansion_pointwise
    (k n d t : ℕ) :
    specializedBoundaryExpansion k n (d, t) =
      2 * ((n / d : ℕ) : ℤ) ^ 2 * divisibilityIndicator k (d : ℤ) -
        4 * (d : ℤ) * ((d : ℤ) - (t : ℤ)) *
          divisibilityIndicator k ((n / d : ℕ) : ℤ) +
        (d : ℤ) ^ 2 - 2 * (t : ℤ) ^ 2 -
        ((n / d : ℕ) : ℤ) ^ 2 * divisibilityIndicator k (t : ℤ) +
        ((n / d : ℕ) : ℤ) ^ 2 *
          divisibilityIndicator k ((d : ℤ) - (t : ℤ)) := by
  simp only [specializedBoundaryExpansion]
  have hzero : divisibilityIndicator k 0 = 1 := by
    simp [divisibilityIndicator]
  rw [hzero]
  ring

/-- Cleared sum of the squares on a finite initial interval. -/
theorem six_mul_sum_range_sq (d : ℕ) :
    6 * (∑ t ∈ Finset.range d, (t : ℤ) ^ 2) =
      (d : ℤ) * ((d : ℤ) - 1) * (2 * (d : ℤ) - 1) := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [Finset.sum_range_succ]
      push_cast
      rw [mul_add, ih]
      ring

/-- Removing the zero endpoint does not change a sum of first powers. -/
theorem sum_Ico_one_eq_sum_range_id (d : ℕ) :
    (∑ t ∈ Finset.Ico 1 d, (t : ℤ)) =
      ∑ t ∈ Finset.range d, (t : ℤ) := by
  by_cases hd : 1 ≤ d
  · rw [Finset.sum_Ico_eq_sub (fun t => (t : ℤ)) hd]
    simp
  · have hd0 : d = 0 := by omega
    subst d
    simp

/-- Removing the zero endpoint does not change a sum of squares. -/
theorem sum_Ico_one_eq_sum_range_sq (d : ℕ) :
    (∑ t ∈ Finset.Ico 1 d, (t : ℤ) ^ 2) =
      ∑ t ∈ Finset.range d, (t : ℤ) ^ 2 := by
  by_cases hd : 1 ≤ d
  · rw [Finset.sum_Ico_eq_sub (fun t => (t : ℤ) ^ 2) hd]
    simp
  · have hd0 : d = 0 := by omega
    subst d
    simp

/-- Exact reflection of the interior divisibility face. -/
theorem sum_indicator_reflect (k d : ℕ) :
    (∑ t ∈ Finset.Ico 1 d,
        divisibilityIndicator k ((d : ℤ) - (t : ℤ))) =
      ∑ t ∈ Finset.Ico 1 d, divisibilityIndicator k (t : ℤ) := by
  calc
    _ = ∑ t ∈ Finset.Ico 1 d,
        divisibilityIndicator k ((d - t : ℕ) : ℤ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Int.ofNat_sub (Nat.le_of_lt (Finset.mem_Ico.mp ht).2)]
    _ = _ := by
      simpa using Finset.sum_Ico_reflect
        (fun t : ℕ => divisibilityIndicator k (t : ℤ)) 1
        (m := d) (n := d) (Nat.le_succ d)

/-- The reflected distance row has the exact cleared Gauss sum. -/
theorem two_mul_sum_Ico_reflected (d : ℕ) :
    2 * (∑ t ∈ Finset.Ico 1 d, ((d : ℤ) - (t : ℤ))) =
      (d : ℤ) * ((d : ℤ) - 1) := by
  have hreflect :
      (∑ t ∈ Finset.Ico 1 d, ((d : ℤ) - (t : ℤ))) =
        ∑ t ∈ Finset.Ico 1 d, (t : ℤ) := by
    calc
      _ = ∑ t ∈ Finset.Ico 1 d, ((d - t : ℕ) : ℤ) := by
        apply Finset.sum_congr rfl
        intro t ht
        rw [Int.ofNat_sub (Nat.le_of_lt (Finset.mem_Ico.mp ht).2)]
      _ = _ := by
        simpa using Finset.sum_Ico_reflect (fun t : ℕ => (t : ℤ)) 1
          (m := d) (n := d) (Nat.le_succ d)
  rw [hreflect]
  by_cases hd0 : d = 0
  · subst d
    simp
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
  have hnat := Finset.sum_range_id_mul_two d
  have hIcoNat := sum_Ico_one_eq_sum_range_id d
  rw [hIcoNat]
  have hcast :
      (∑ t ∈ Finset.range d, (t : ℤ)) * 2 =
        (d : ℤ) * ((d : ℤ) - 1) := by
    have hz := congrArg (fun z : ℕ => (z : ℤ)) hnat
    push_cast at hz
    rw [Int.ofNat_sub hd] at hz
    simpa using hz
  linarith

/-- Each divisor row returns one cubic-minus-linear face and its two scale
indicator faces. -/
theorem three_mul_boundaryRow (k n d : ℕ) (hd : 0 < d) :
    3 * (∑ t ∈ Finset.Ico 1 d,
      specializedBoundaryExpansion k n (d, t)) =
      (d : ℤ) ^ 3 - (d : ℤ) +
        6 * ((n / d : ℕ) : ℤ) ^ 2 * ((d : ℤ) - 1) *
          divisibilityIndicator k (d : ℤ) -
        6 * (d : ℤ) ^ 2 * ((d : ℤ) - 1) *
          divisibilityIndicator k ((n / d : ℕ) : ℤ) := by
  simp_rw [specializedBoundaryExpansion_pointwise]
  have hreflect := sum_indicator_reflect k d
  have hlinear := two_mul_sum_Ico_reflected d
  have hsquare := six_mul_sum_range_sq d
  have hsquareIco :
      6 * (∑ t ∈ Finset.Ico 1 d, (t : ℤ) ^ 2) =
        (d : ℤ) * ((d : ℤ) - 1) * (2 * (d : ℤ) - 1) := by
    rw [sum_Ico_one_eq_sum_range_sq]
    exact hsquare
  have hcard : ((Finset.Ico 1 d).card : ℤ) = (d : ℤ) - 1 := by
    rw [Nat.card_Ico]
    rw [Int.ofNat_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd))]
    norm_num
  have hcollect :
      (∑ t ∈ Finset.Ico 1 d,
          (2 * ((n / d : ℕ) : ℤ) ^ 2 * divisibilityIndicator k (d : ℤ) -
              4 * (d : ℤ) * ((d : ℤ) - (t : ℤ)) *
                divisibilityIndicator k ((n / d : ℕ) : ℤ) +
              (d : ℤ) ^ 2 - 2 * (t : ℤ) ^ 2 -
              ((n / d : ℕ) : ℤ) ^ 2 * divisibilityIndicator k (t : ℤ) +
              ((n / d : ℕ) : ℤ) ^ 2 *
                divisibilityIndicator k ((d : ℤ) - (t : ℤ)))) =
        ((Finset.Ico 1 d).card : ℤ) *
            (2 * ((n / d : ℕ) : ℤ) ^ 2 *
                divisibilityIndicator k (d : ℤ) + (d : ℤ) ^ 2) -
          4 * (d : ℤ) * divisibilityIndicator k ((n / d : ℕ) : ℤ) *
            (∑ t ∈ Finset.Ico 1 d, ((d : ℤ) - (t : ℤ))) -
          2 * (∑ t ∈ Finset.Ico 1 d, (t : ℤ) ^ 2) -
          ((n / d : ℕ) : ℤ) ^ 2 *
            (∑ t ∈ Finset.Ico 1 d, divisibilityIndicator k (t : ℤ)) +
          ((n / d : ℕ) : ℤ) ^ 2 *
            (∑ t ∈ Finset.Ico 1 d,
              divisibilityIndicator k ((d : ℤ) - (t : ℤ))) := by
    have hgeneral : ∀ s : Finset ℕ,
        (∑ t ∈ s,
            (2 * ((n / d : ℕ) : ℤ) ^ 2 * divisibilityIndicator k (d : ℤ) -
                4 * (d : ℤ) * ((d : ℤ) - (t : ℤ)) *
                  divisibilityIndicator k ((n / d : ℕ) : ℤ) +
                (d : ℤ) ^ 2 - 2 * (t : ℤ) ^ 2 -
                ((n / d : ℕ) : ℤ) ^ 2 * divisibilityIndicator k (t : ℤ) +
                ((n / d : ℕ) : ℤ) ^ 2 *
                  divisibilityIndicator k ((d : ℤ) - (t : ℤ)))) =
          (s.card : ℤ) *
              (2 * ((n / d : ℕ) : ℤ) ^ 2 *
                  divisibilityIndicator k (d : ℤ) + (d : ℤ) ^ 2) -
            4 * (d : ℤ) * divisibilityIndicator k ((n / d : ℕ) : ℤ) *
              (∑ t ∈ s, ((d : ℤ) - (t : ℤ))) -
            2 * (∑ t ∈ s, (t : ℤ) ^ 2) -
            ((n / d : ℕ) : ℤ) ^ 2 *
              (∑ t ∈ s, divisibilityIndicator k (t : ℤ)) +
            ((n / d : ℕ) : ℤ) ^ 2 *
              (∑ t ∈ s,
                divisibilityIndicator k ((d : ℤ) - (t : ℤ))) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simp
      | @insert x s hx ih =>
          simp only [Finset.sum_insert, hx, not_false_eq_true]
          rw [ih]
          have hcardInsert : (insert x s).card = s.card + 1 := by
            simp [hx]
          rw [hcardInsert]
          push_cast
          ring
    exact hgeneral (Finset.Ico 1 d)
  rw [hcollect, hcard]
  linear_combination
    (-6 * (d : ℤ) * divisibilityIndicator k ((n / d : ℕ) : ℤ)) * hlinear +
      (-1) * hsquareIco +
      (3 * ((n / d : ℕ) : ℤ) ^ 2) * hreflect

/-! ## Exact scale-fibre reindexing -/

private def timesKEmbedding (k : ℕ) (hk : 0 < k) : ℕ ↪ ℕ where
  toFun d := k * d
  inj' := by
    intro a b hab
    exact mul_left_cancel₀ (Nat.ne_of_gt hk) hab

/-- Multiplication by `k` identifies the divisor population of `m` with the
`k`-divisible divisor fibre of `k*m`. -/
theorem divisors_filter_dvd_mul
    {k m : ℕ} (hk : 0 < k) (hm : m ≠ 0) :
    (k * m).divisors.filter (fun d => k ∣ d) =
      m.divisors.map (timesKEmbedding k hk) := by
  have hkm : k * m ≠ 0 := mul_ne_zero (Nat.ne_of_gt hk) hm
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_map]
  constructor
  · rintro ⟨⟨hdvd, _⟩, hkd⟩
    rcases hkd with ⟨e, rfl⟩
    refine ⟨e, ⟨?_, hm⟩, rfl⟩
    exact (Nat.mul_dvd_mul_iff_left hk).mp hdvd
  · rintro ⟨e, ⟨he, _⟩, rfl⟩
    refine ⟨⟨?_, hkm⟩, dvd_mul_right k e⟩
    exact mul_dvd_mul_left k he

/-- The two scale-indicator faces in a divisor row. -/
def boundaryScaleCurrent (k n d : ℕ) : ℤ :=
  6 * ((n / d : ℕ) : ℤ) ^ 2 * ((d : ℤ) - 1) *
      divisibilityIndicator k (d : ℤ) -
    6 * (d : ℤ) ^ 2 * ((d : ℤ) - 1) *
      divisibilityIndicator k ((n / d : ℕ) : ℤ)

/-- Reflecting the second scale face through `d ↦ n/d` places both
indicators on the same divisor address. -/
theorem sum_boundaryScaleCurrent_eq_reflected
    {k n : ℕ} (hn : 0 < n) :
    (∑ d ∈ n.divisors, boundaryScaleCurrent k n d) =
      ∑ d ∈ n.divisors,
        6 * ((n / d : ℕ) : ℤ) ^ 2 *
          ((d : ℤ) - ((n / d : ℕ) : ℤ)) *
          divisibilityIndicator k (d : ℤ) := by
  let f : ℕ → ℤ := fun d =>
    6 * ((n / d : ℕ) : ℤ) ^ 2 *
      (((n / d : ℕ) : ℤ) - 1) * divisibilityIndicator k (d : ℤ)
  have hcomp := Nat.sum_div_divisors n f
  have hleft :
      (∑ d ∈ n.divisors, f (n / d)) =
        ∑ d ∈ n.divisors,
          6 * (d : ℤ) ^ 2 * ((d : ℤ) - 1) *
            divisibilityIndicator k ((n / d : ℕ) : ℤ) := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    simp only [f]
    rw [Nat.div_div_self hdvd (Nat.ne_of_gt hn)]
  rw [hleft] at hcomp
  simp only [boundaryScaleCurrent]
  rw [Finset.sum_sub_distrib, hcomp]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- On the exact multiple chart `n=k*m`, the reflected scale sum is the
ordinary-minus-cubic divisor current. -/
theorem sum_reflected_scale_mul
    {k m : ℕ} (hk : 0 < k) (hm : 0 < m) :
    (∑ d ∈ (k * m).divisors,
        6 * (((k * m) / d : ℕ) : ℤ) ^ 2 *
          ((d : ℤ) - (((k * m) / d : ℕ) : ℤ)) *
          divisibilityIndicator k (d : ℤ)) =
      6 * ((k * m : ℕ) : ℤ) * ordinaryDivisorCurrent m -
        6 * cubicDivisorCurrent m := by
  have hindicator :
      (∑ d ∈ (k * m).divisors,
          6 * (((k * m) / d : ℕ) : ℤ) ^ 2 *
            ((d : ℤ) - (((k * m) / d : ℕ) : ℤ)) *
            divisibilityIndicator k (d : ℤ)) =
        ∑ d ∈ (k * m).divisors.filter (fun d => k ∣ d),
          6 * (((k * m) / d : ℕ) : ℤ) ^ 2 *
            ((d : ℤ) - (((k * m) / d : ℕ) : ℤ)) := by
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [divisibilityIndicator]
    by_cases hkd : k ∣ d
    · have hkdi : (k : ℤ) ∣ (d : ℤ) := Int.ofNat_dvd.mpr hkd
      simp [hkd, hkdi]
    · have hkdi : ¬(k : ℤ) ∣ (d : ℤ) := by
        exact fun h => hkd (Int.ofNat_dvd.mp h)
      simp [hkd, hkdi]
  rw [hindicator, divisors_filter_dvd_mul hk (Nat.ne_of_gt hm),
    Finset.sum_map]
  change
    (∑ e ∈ m.divisors,
        6 * (((k * m) / (k * e) : ℕ) : ℤ) ^ 2 *
          (((k * e : ℕ) : ℤ) - (((k * m) / (k * e) : ℕ) : ℤ))) =
      6 * ((k * m : ℕ) : ℤ) * ordinaryDivisorCurrent m -
        6 * cubicDivisorCurrent m
  have hscaled :
      (∑ e ∈ m.divisors,
          6 * (((k * m) / (k * e) : ℕ) : ℤ) ^ 2 *
            (((k * e : ℕ) : ℤ) - (((k * m) / (k * e) : ℕ) : ℤ))) =
        ∑ e ∈ m.divisors,
          6 * ((m / e : ℕ) : ℤ) ^ 2 *
            (((k * e : ℕ) : ℤ) - ((m / e : ℕ) : ℤ)) := by
    apply Finset.sum_congr rfl
    intro e he
    rw [Nat.mul_div_mul_left m e hk]
  rw [hscaled]
  let f : ℕ → ℤ := fun r =>
    6 * (r : ℤ) ^ 2 *
      (((k * (m / r) : ℕ) : ℤ) - (r : ℤ))
  have hcomp := Nat.sum_div_divisors m f
  have hleft :
      (∑ e ∈ m.divisors, f (m / e)) =
        ∑ e ∈ m.divisors,
          6 * ((m / e : ℕ) : ℤ) ^ 2 *
            (((k * e : ℕ) : ℤ) - ((m / e : ℕ) : ℤ)) := by
    apply Finset.sum_congr rfl
    intro e he
    have hedvd := (Nat.mem_divisors.mp he).1
    simp only [f]
    rw [Nat.div_div_self hedvd (Nat.ne_of_gt hm)]
  rw [hleft] at hcomp
  rw [hcomp]
  have hpointwise : ∀ e ∈ m.divisors,
      f e = 6 * ((k * m : ℕ) : ℤ) * (e : ℤ) - 6 * (e : ℤ) ^ 3 := by
    intro e he
    have hedvd := (Nat.mem_divisors.mp he).1
    have heprodNat := Nat.mul_div_cancel' hedvd
    have heprod :
        (e : ℤ) * ((m / e : ℕ) : ℤ) = (m : ℤ) := by
      exact_mod_cast heprodNat
    simp only [f]
    simp only [Nat.cast_mul]
    linear_combination (6 * (k : ℤ) * (e : ℤ)) * heprod
  apply Eq.trans (Finset.sum_congr rfl hpointwise)
  rw [ordinaryDivisorCurrent, cubicDivisorCurrent]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]

/-- The scale fibre is present exactly when the modulus divides the boundary
address `n`; there is no contribution at a nondivisible address. -/
theorem sum_boundaryScaleCurrent_eq_if
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    (∑ d ∈ n.divisors, boundaryScaleCurrent k n d) =
      if k ∣ n then
        6 * (n : ℤ) * ordinaryDivisorCurrent (n / k) -
          6 * cubicDivisorCurrent (n / k)
      else 0 := by
  rw [sum_boundaryScaleCurrent_eq_reflected hn]
  by_cases hkn : k ∣ n
  · rcases hkn with ⟨m, rfl⟩
    have hm : 0 < m := by
      exact Nat.pos_of_mul_pos_left hn
    rw [if_pos (dvd_mul_right k m)]
    rw [Nat.mul_div_cancel_left m hk]
    exact sum_reflected_scale_mul hk hm
  · rw [if_neg hkn]
    apply Finset.sum_eq_zero
    intro d hd
    have hdvd := (Nat.mem_divisors.mp hd).1
    have hnkd : ¬(k : ℤ) ∣ (d : ℤ) := by
      intro hkdi
      have hkd : k ∣ d := Int.ofNat_dvd.mp hkdi
      exact hkn (dvd_trans hkd hdvd)
    simp [divisibilityIndicator, hnkd]

/-- Exact evaluation of the complete specialized Huard boundary.  The first
two terms are the unscaled cubic/ordinary divisor faces; the conditional term
is the transported `k`-divisible fibre. -/
theorem three_mul_sum_specializedBoundaryExpansion
    {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    3 * (∑ dt ∈ huardBoundaryPairs n,
      specializedBoundaryExpansion k n dt) =
      cubicDivisorCurrent n - ordinaryDivisorCurrent n +
        if k ∣ n then
          6 * (n : ℤ) * ordinaryDivisorCurrent (n / k) -
            6 * cubicDivisorCurrent (n / k)
        else 0 := by
  rw [sum_boundaryPairs_eq_rows hn, Finset.mul_sum]
  calc
    (∑ d ∈ n.divisors,
        3 * ∑ t ∈ Finset.Ico 1 d,
          specializedBoundaryExpansion k n (d, t)) =
      ∑ d ∈ n.divisors,
        ((d : ℤ) ^ 3 - (d : ℤ) + boundaryScaleCurrent k n d) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hdpos : 0 < d := Nat.pos_of_dvd_of_pos
            (Nat.dvd_of_mem_divisors hd) hn
          rw [three_mul_boundaryRow k n d hdpos]
          simp only [boundaryScaleCurrent]
          ring
    _ = cubicDivisorCurrent n - ordinaryDivisorCurrent n +
          ∑ d ∈ n.divisors, boundaryScaleCurrent k n d := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
            cubicDivisorCurrent, ordinaryDivisorCurrent]
    _ = _ := by
      rw [sum_boundaryScaleCurrent_eq_if hk hn]
