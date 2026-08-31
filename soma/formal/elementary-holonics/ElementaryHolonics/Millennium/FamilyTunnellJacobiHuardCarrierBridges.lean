import ElementaryHolonics.Millennium.FamilyTunnellJacobiHuardSpecialization

/-!
# Exact bridges from the Huard quadruple carrier to divisor currents

The source carrier keeps factor and cofactor occurrences `(a,b,x,y)`.
The named Huard currents are its receiver shadow, indexed instead by
`m = a*x`, `n-m = b*y`.  This file proves that passage by finite sigma
reindexing; no multiplicity or quotient is discarded.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FamilyTunnellJacobiHuardCarrierBridges

open Finset
open Soma.Holonics.Millennium.FamilyTunnellJacobiDivisorConvolutionReduction
open Soma.Holonics.Millennium.FamilyTunnellJacobiFourSquareLambert
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardLevelTwoSource
open Soma.Holonics.Millennium.FamilyTunnellJacobiHuardSpecialization

private def carrierSigma (n : ℕ) :=
  (Finset.range n).sigma (fun m =>
    m.divisors.sigma (fun _a => (n - m).divisors))

private def sigmaQuad (n : ℕ)
    (z : Sigma (fun m : ℕ => Sigma (fun _a : ℕ => ℕ))) :
    (ℕ × ℕ) × (ℕ × ℕ) :=
  ((z.2.1, z.2.2), (z.1 / z.2.1, (n - z.1) / z.2.2))

private theorem sigmaQuad_mem (n : ℕ) {z : Sigma (fun m : ℕ => Sigma (fun _a : ℕ => ℕ))}
    (hz : z ∈ carrierSigma n) :
    sigmaQuad n z ∈ huardPositiveQuadruples n := by
  have hz' : z.1 ∈ Finset.range n ∧
      z.2 ∈ z.1.divisors.sigma (fun _a => (n - z.1).divisors) := by
    exact Finset.mem_sigma.mp (show z ∈ carrierSigma n from hz)
  have hz'' : z.2.1 ∈ z.1.divisors ∧ z.2.2 ∈ (n - z.1).divisors := by
    exact Finset.mem_sigma.mp hz'.2
  have hm : z.1 < n := Finset.mem_range.mp hz'.1
  have ha : z.2.1 ∣ z.1 ∧ z.1 ≠ 0 := Nat.mem_divisors.mp hz''.1
  have hb : z.2.2 ∣ n - z.1 ∧ n - z.1 ≠ 0 := Nat.mem_divisors.mp hz''.2
  have hmn : 0 < n - z.1 := Nat.pos_of_ne_zero hb.2
  have hax : z.2.1 * (z.1 / z.2.1) = z.1 := by
    rw [Nat.mul_comm, Nat.div_mul_cancel ha.1]
  have hby : z.2.2 * ((n - z.1) / z.2.2) = n - z.1 := by
    rw [Nat.mul_comm, Nat.div_mul_cancel hb.1]
  apply mem_huardPositiveQuadruples.mpr
  have ha0 : 0 < z.2.1 := Nat.pos_of_dvd_of_pos ha.1 (Nat.pos_of_ne_zero ha.2)
  have hb0 : 0 < z.2.2 := Nat.pos_of_dvd_of_pos hb.1 hmn
  have hx0 : 0 < z.1 / z.2.1 :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero ha.2) ha.1) ha0
  have hy0 : 0 < (n - z.1) / z.2.2 :=
    Nat.div_pos (Nat.le_of_dvd hmn hb.1) hb0
  have ha_le : z.2.1 ≤ z.1 := by
    rw [← hax]
    exact Nat.le_mul_of_pos_right _ hx0
  have hb_le : z.2.2 ≤ n - z.1 := by
    rw [← hby]
    exact Nat.le_mul_of_pos_right _ hy0
  have hx_le : z.1 / z.2.1 ≤ z.1 := by
    exact Nat.div_le_self _ _
  have hy_le : (n - z.1) / z.2.2 ≤ n - z.1 := by
    exact Nat.div_le_self _ _
  exact ⟨by omega, by omega, by omega, by omega,
    by omega, by omega, by omega, by omega, by omega⟩

private theorem sigmaQuad_factor (n : ℕ)
    (z : Sigma (fun m : ℕ => Sigma (fun _a : ℕ => ℕ)))
    (hz : z ∈ carrierSigma n) :
    z.2.1 * (z.1 / z.2.1) = z.1 := by
  have hz' := Finset.mem_sigma.mp (show z ∈ carrierSigma n from hz)
  have hz'' := Finset.mem_sigma.mp hz'.2
  rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.mem_divisors.mp hz''.1).1]

private theorem sigmaQuad_cofactor (n : ℕ)
    (z : Sigma (fun m : ℕ => Sigma (fun _a : ℕ => ℕ)))
    (hz : z ∈ carrierSigma n) :
    z.2.2 * ((n - z.1) / z.2.2) = n - z.1 := by
  have hz' := Finset.mem_sigma.mp (show z ∈ carrierSigma n from hz)
  have hz'' := Finset.mem_sigma.mp hz'.2
  rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.mem_divisors.mp hz''.2).1]

private theorem carrierSigma_sum (n : ℕ)
    (H : (ℕ × ℕ) × (ℕ × ℕ) → ℤ) :
    (∑ q ∈ huardPositiveQuadruples n, H q) =
      ∑ z ∈ carrierSigma n, H (sigmaQuad n z) := by
  refine Finset.sum_bij (s := huardPositiveQuadruples n) (t := carrierSigma n)
    (f := H) (g := fun z => H (sigmaQuad n z)) (fun q hq =>
    (Sigma.mk (q.1.1 * q.2.1)
      (Sigma.mk q.1.1 q.1.2))) ?_ ?_ ?_ ?_
  · intro q hq
    dsimp
    rw [carrierSigma, Finset.mem_sigma]
    rw [Finset.mem_range]
    have hq' := mem_huardPositiveQuadruples.mp hq
    rcases hq' with ⟨ha1, haN, hb1, hbN, hx1, hxN, hy1, hyN, heq⟩
    have hapos : 0 < q.1.1 := lt_of_lt_of_le Nat.zero_lt_one ha1
    have hbpos : 0 < q.1.2 := lt_of_lt_of_le Nat.zero_lt_one hb1
    have hxpos : 0 < q.2.1 := lt_of_lt_of_le Nat.zero_lt_one hx1
    have hypos : 0 < q.2.2 := lt_of_lt_of_le Nat.zero_lt_one hy1
    have hmpos : 0 < q.1.1 * q.2.1 := Nat.mul_pos hapos hxpos
    have hbypos : 0 < q.1.2 * q.2.2 := Nat.mul_pos hbpos hypos
    have hsub : n - q.1.1 * q.2.1 = q.1.2 * q.2.2 := by
      calc
        n - q.1.1 * q.2.1 =
            (q.1.1 * q.2.1 + q.1.2 * q.2.2) - q.1.1 * q.2.1 := by rw [heq]
        _ = q.1.2 * q.2.2 := Nat.add_sub_cancel_left _ _
    have hnmp : 0 < n - q.1.1 * q.2.1 := by rw [hsub]; exact hbypos
    have hdiva : q.1.1 ∈ (q.1.1 * q.2.1).divisors :=
      Nat.mem_divisors.mpr ⟨dvd_mul_right _ _, hmpos.ne'⟩
    have hdivb : q.1.2 ∈ (n - q.1.1 * q.2.1).divisors := by
      rw [Nat.mem_divisors]
      exact ⟨hsub ▸ dvd_mul_right _ _, hnmp.ne'⟩
    refine ⟨?_, ?_⟩
    · dsimp
      omega
    · dsimp
      rw [Finset.mem_sigma]
      constructor
      · exact hdiva
      · exact hdivb
  · intro q₁ hq₁ q₂ hq₂ heq
    rcases q₁ with ⟨⟨a₁, b₁⟩, ⟨x₁, y₁⟩⟩
    rcases q₂ with ⟨⟨a₂, b₂⟩, ⟨x₂, y₂⟩⟩
    have hq₁' := mem_huardPositiveQuadruples.mp hq₁
    have hq₂' := mem_huardPositiveQuadruples.mp hq₂
    have heq' := Sigma.mk.inj_iff.mp heq
    rcases heq' with ⟨hm, hinner⟩
    have hinner' : (Sigma.mk a₁ b₁ : Sigma (fun _ : ℕ => ℕ)) =
        Sigma.mk a₂ b₂ := eq_of_heq hinner
    have hab := Sigma.mk.inj_iff.mp hinner'
    rcases hab with ⟨ha, hb⟩
    cases ha
    cases hb
    have ha₁ : 0 < a₁ := by omega
    have hb₁ : 0 < b₁ := by omega
    have hx : x₁ = x₂ := Nat.mul_left_cancel ha₁ (by omega)
    cases hx
    have hy : y₁ = y₂ := Nat.mul_left_cancel hb₁ (by omega)
    cases hy
    rfl
  · intro z hz
    rcases z with ⟨m, ⟨a, b⟩⟩
    have hz' : m ∈ Finset.range n ∧
        a ∈ m.divisors ∧ b ∈ (n - m).divisors := by
      have h := Finset.mem_sigma.mp (show (⟨m, ⟨a, b⟩⟩ : Sigma
          (fun m : ℕ => Sigma (fun _a : ℕ => ℕ))) ∈ carrierSigma n from hz)
      exact ⟨h.1, (Finset.mem_sigma.mp h.2).1,
        (Finset.mem_sigma.mp h.2).2⟩
    refine ⟨((a, b), (m / a, (n - m) / b)),
      sigmaQuad_mem n hz, ?_⟩
    have ha : a ∣ m := (Nat.mem_divisors.mp hz'.2.1).1
    have ham : a * (m / a) = m := by
      rw [Nat.mul_comm, Nat.div_mul_cancel ha]
    simp [sigmaQuad, ham]
  · intro q hq
    have hq' := mem_huardPositiveQuadruples.mp hq
    rcases hq' with ⟨ha1, haN, hb1, hbN, hx1, hxN, hy1, hyN, heq⟩
    have ha0 : 0 < q.1.1 := lt_of_lt_of_le Nat.zero_lt_one ha1
    have hb0 : 0 < q.1.2 := lt_of_lt_of_le Nat.zero_lt_one hb1
    have hax : q.1.1 * q.2.1 / q.1.1 = q.2.1 := by
      rw [Nat.mul_div_cancel_left q.2.1 ha0]
    have hby : (n - q.1.1 * q.2.1) / q.1.2 = q.2.2 := by
      have hsub : n - q.1.1 * q.2.1 = q.1.2 * q.2.2 := by
        calc
          n - q.1.1 * q.2.1 =
              (q.1.1 * q.2.1 + q.1.2 * q.2.2) - q.1.1 * q.2.1 := by rw [heq]
          _ = q.1.2 * q.2.2 := Nat.add_sub_cancel_left _ _
      rw [hsub, Nat.mul_div_cancel_left q.2.2 hb0]
    change H q = H ((q.1.1, q.1.2),
      (q.1.1 * q.2.1 / q.1.1,
        (n - q.1.1 * q.2.1) / q.1.2))
    rw [hax, hby]

private theorem nested_sum_eq_sigma (n : ℕ)
    (H : (ℕ × ℕ) × (ℕ × ℕ) → ℤ) :
    (∑ m ∈ Finset.range n,
      ∑ a ∈ m.divisors,
        ∑ b ∈ (n - m).divisors,
          H ((a, b), (m / a, (n - m) / b))) =
      ∑ z ∈ carrierSigma n, H (sigmaQuad n z) := by
  calc
    _ = ∑ m ∈ Finset.range n,
        ∑ z ∈ m.divisors.sigma (fun _a => (n - m).divisors),
          H ((z.1, z.2), (m / z.1, (n - m) / z.2)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_sigma']
    _ = ∑ z ∈ carrierSigma n, H (sigmaQuad n z) := by
      rw [carrierSigma, Finset.sum_sigma']
      simp [sigmaQuad]

private theorem divisibilityIndicator_nat (k x : ℕ) :
    divisibilityIndicator k (x : ℤ) = if x % k = 0 then 1 else 0 := by
  by_cases h : (k : ℤ) ∣ (x : ℤ)
  · have h' : k ∣ x := Int.natCast_dvd_natCast.mp h
    simp [divisibilityIndicator, h, Nat.dvd_iff_mod_eq_zero.mp h']
  · have h' : ¬ k ∣ x := fun hx => h (Int.natCast_dvd_natCast.mpr hx)
    have hmod : ¬ x % k = 0 := fun hx => h' (Nat.dvd_iff_mod_eq_zero.mpr hx)
    simp [divisibilityIndicator, h, hmod]

private theorem divisibilityIndicator_nat_sub (k x y : ℕ) :
    divisibilityIndicator k ((y : ℤ) - (x : ℤ)) =
      if x % k = y % k then 1 else 0 := by
  have hiff : ((k : ℤ) ∣ (y : ℤ) - (x : ℤ)) ↔ x % k = y % k := by
    rw [← Nat.modEq_iff_dvd]
    rfl
  by_cases h : (k : ℤ) ∣ (y : ℤ) - (x : ℤ)
  · simp [divisibilityIndicator, h, hiff.mp h]
  · simp [divisibilityIndicator, h, hiff.not.mp h]

theorem qMinusCarrier_eq_huardMinusCurrent (k n : ℕ) :
    qMinusCarrier k n = huardMinusCurrent k n := by
  let H : (ℕ × ℕ) × (ℕ × ℕ) → ℤ := fun q =>
    (q.1.1 : ℤ) * (q.1.2 : ℤ) *
      divisibilityIndicator k ((q.2.1 : ℤ) + (q.2.2 : ℤ))
  calc
    qMinusCarrier k n = ∑ q ∈ huardPositiveQuadruples n, H q := by rfl
    _ = ∑ z ∈ carrierSigma n, H (sigmaQuad n z) := carrierSigma_sum n H
    _ = ∑ m ∈ Finset.range n,
        ∑ a ∈ m.divisors,
          ∑ b ∈ (n - m).divisors,
            H ((a, b), (m / a, (n - m) / b)) :=
      (nested_sum_eq_sigma n H).symm
    _ = huardMinusCurrent k n := by
      simp only [huardMinusCurrent, H]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      have hi := divisibilityIndicator_nat k (m / a + (n - m) / b)
      rw [show ((m / a : ℕ) : ℤ) + (((n - m) / b : ℕ) : ℤ) =
          ((m / a + (n - m) / b : ℕ) : ℤ) by norm_num, hi]
      split_ifs <;> ring

theorem qPlusCarrier_eq_huardPlusCurrent (k n : ℕ) :
    qPlusCarrier k n = huardPlusCurrent k n := by
  let H : (ℕ × ℕ) × (ℕ × ℕ) → ℤ := fun q =>
    (q.1.1 : ℤ) * (q.1.2 : ℤ) *
      divisibilityIndicator k ((q.2.2 : ℤ) - (q.2.1 : ℤ))
  calc
    qPlusCarrier k n = ∑ q ∈ huardPositiveQuadruples n, H q := by rfl
    _ = ∑ z ∈ carrierSigma n, H (sigmaQuad n z) := carrierSigma_sum n H
    _ = ∑ m ∈ Finset.range n,
        ∑ a ∈ m.divisors,
          ∑ b ∈ (n - m).divisors,
            H ((a, b), (m / a, (n - m) / b)) :=
      (nested_sum_eq_sigma n H).symm
    _ = huardPlusCurrent k n := by
      simp only [huardPlusCurrent, H]
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [divisibilityIndicator_nat_sub]
      split_ifs <;> ring

private def scaleSigma (k n : ℕ) :=
  (Finset.range n).sigma (fun m =>
    m.divisors.sigma (fun _a => (n - k * m).divisors))

private def scaleIndex (k : ℕ)
    (q : (ℕ × ℕ) × (ℕ × ℕ)) : Sigma (fun m : ℕ => Sigma (fun _a : ℕ => ℕ)) :=
  Sigma.mk (q.1.1 * (q.2.1 / k)) (Sigma.mk q.1.1 q.1.2)

private theorem scaleIndex_mem (hk : 0 < k) {q : (ℕ × ℕ) × (ℕ × ℕ)}
    (hq : q ∈ huardPositiveQuadruples n)
    (hdiv : k ∣ q.2.1) : scaleIndex k q ∈ scaleSigma k n := by
  have hq' := mem_huardPositiveQuadruples.mp hq
  rcases hq' with ⟨ha1, haN, hb1, hbN, hx1, hxN, hy1, hyN, heq⟩
  have ha0 : 0 < q.1.1 := lt_of_lt_of_le Nat.zero_lt_one ha1
  have hb0 : 0 < q.1.2 := lt_of_lt_of_le Nat.zero_lt_one hb1
  have hx0 : 0 < q.2.1 := lt_of_lt_of_le Nat.zero_lt_one hx1
  have hy0 : 0 < q.2.2 := lt_of_lt_of_le Nat.zero_lt_one hy1
  have hr0 : 0 < q.2.1 / k :=
    Nat.div_pos (Nat.le_of_dvd hx0 hdiv) hk
  have hkr : k * (q.2.1 / k) = q.2.1 := by
    rw [Nat.mul_comm, Nat.div_mul_cancel hdiv]
  have hm0 : 0 < q.1.1 * (q.2.1 / k) := Nat.mul_pos ha0 hr0
  have hby0 : 0 < q.1.2 * q.2.2 := Nat.mul_pos hb0 hy0
  have hmk : k * (q.1.1 * (q.2.1 / k)) +
      q.1.2 * q.2.2 = n := by
    calc
      k * (q.1.1 * (q.2.1 / k)) + q.1.2 * q.2.2 =
          q.1.1 * (k * (q.2.1 / k)) + q.1.2 * q.2.2 := by ring
      _ = q.1.1 * q.2.1 + q.1.2 * q.2.2 := by rw [hkr]
      _ = n := heq
  have hnsub : 0 < n - k * (q.1.1 * (q.2.1 / k)) := by omega
  have ham : q.1.1 ∣ q.1.1 * (q.2.1 / k) := dvd_mul_right _ _
  have hbm : q.1.2 ∣ n - k * (q.1.1 * (q.2.1 / k)) := by
    refine ⟨q.2.2, ?_⟩
    omega
  dsimp [scaleIndex, scaleSigma]
  rw [Finset.mem_sigma, Finset.mem_range]
  refine ⟨?_, ?_⟩
  · have hkm : q.1.1 * (q.2.1 / k) ≤
        k * (q.1.1 * (q.2.1 / k)) := Nat.le_mul_of_pos_left _ hk
    have hmlt : q.1.1 * (q.2.1 / k) < n := by omega
    simpa using hmlt
  · rw [Finset.mem_sigma]
    exact ⟨Nat.mem_divisors.mpr ⟨ham, hm0.ne'⟩,
      Nat.mem_divisors.mpr ⟨hbm, hnsub.ne'⟩⟩

private theorem scaleCarrier_sum_reindex (hk : 0 < k) (n : ℕ) :
    (∑ q ∈ (huardPositiveQuadruples n).filter (fun q => k ∣ q.2.1),
      (q.1.1 : ℤ) * (q.1.2 : ℤ)) =
      ∑ z ∈ scaleSigma k n, (z.2.1 : ℤ) * (z.2.2 : ℤ) := by
  refine Finset.sum_bij (s := (huardPositiveQuadruples n).filter
      (fun q => k ∣ q.2.1)) (t := scaleSigma k n)
      (f := fun q => (q.1.1 : ℤ) * (q.1.2 : ℤ))
      (g := fun z => (z.2.1 : ℤ) * (z.2.2 : ℤ))
      (fun q hq => scaleIndex k q) ?_ ?_ ?_ ?_
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    exact scaleIndex_mem hk hq'.1 hq'.2
  · intro q₁ hq₁ q₂ hq₂ heq
    have hq₁filter := Finset.mem_filter.mp hq₁
    have hq₂filter := Finset.mem_filter.mp hq₂
    have heq' := Sigma.mk.inj_iff.mp heq
    rcases heq' with ⟨hm, hinner⟩
    have hinner' : (Sigma.mk q₁.1.1 q₁.1.2 : Sigma (fun _ : ℕ => ℕ)) =
        Sigma.mk q₂.1.1 q₂.1.2 := eq_of_heq hinner
    have hab := Sigma.mk.inj_iff.mp hinner'
    rcases hab with ⟨ha, hb⟩
    have hq₁' := mem_huardPositiveQuadruples.mp hq₁filter.1
    have hq₂' := mem_huardPositiveQuadruples.mp hq₂filter.1
    have ha0 : 0 < q₁.1.1 := lt_of_lt_of_le Nat.zero_lt_one hq₁'.1
    have hkr₁ : k * (q₁.2.1 / k) = q₁.2.1 := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hq₁filter.2]
    have hkr₂ : k * (q₂.2.1 / k) = q₂.2.1 := by
      rw [Nat.mul_comm, Nat.div_mul_cancel hq₂filter.2]
    have hxm₁ : q₁.1.1 * (q₁.2.1 / k) =
        q₂.1.1 * (q₂.2.1 / k) := hm
    have hr : q₁.2.1 / k = q₂.2.1 / k := by
      apply Nat.mul_left_cancel ha0
      simpa [ha] using hm
    have hx : q₁.2.1 = q₂.2.1 := by
      calc
        q₁.2.1 = k * (q₁.2.1 / k) := hkr₁.symm
        _ = k * (q₂.2.1 / k) := by rw [hr]
        _ = q₂.2.1 := hkr₂
    have hy : q₁.2.2 = q₂.2.2 := by
      have e₁ := (mem_huardPositiveQuadruples.mp hq₁filter.1)
      have e₂ := (mem_huardPositiveQuadruples.mp hq₂filter.1)
      rcases e₁ with ⟨_, _, _, _, _, _, _, _, e₁⟩
      rcases e₂ with ⟨_, _, _, _, _, _, _, _, e₂⟩
      have hb' : q₁.1.2 = q₂.1.2 := eq_of_heq hb
      have hp : q₁.1.1 * q₁.2.1 + q₁.1.2 * q₁.2.2 =
          q₁.1.1 * q₁.2.1 + q₁.1.2 * q₂.2.2 := by
        calc
          q₁.1.1 * q₁.2.1 + q₁.1.2 * q₁.2.2 = n := e₁
          _ = q₂.1.1 * q₂.2.1 + q₂.1.2 * q₂.2.2 := e₂.symm
          _ = q₁.1.1 * q₁.2.1 + q₁.1.2 * q₂.2.2 := by rw [← ha, ← hb', ← hx]
      have hp' : q₁.1.2 * q₁.2.2 = q₁.1.2 * q₂.2.2 :=
        Nat.add_left_cancel hp
      have hb0 : 0 < q₁.1.2 := lt_of_lt_of_le Nat.zero_lt_one hq₁'.2.2.1
      exact Nat.mul_left_cancel hb0 hp'
    have hb' : q₁.1.2 = q₂.1.2 := eq_of_heq hb
    exact Prod.ext (Prod.ext ha hb') (Prod.ext hx hy)
  · intro z hz
    have hz' := Finset.mem_sigma.mp (show z ∈ scaleSigma k n from hz)
    have hz'' := Finset.mem_sigma.mp hz'.2
    have hm0 : 0 < z.1 := by
      have := (Nat.mem_divisors.mp hz''.1).2
      omega
    have hnsub0 : 0 < n - k * z.1 := by
      have := (Nat.mem_divisors.mp hz''.2).2
      omega
    refine ⟨((z.2.1, z.2.2),
        (k * (z.1 / z.2.1), (n - k * z.1) / z.2.2)), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      constructor
      · apply mem_huardPositiveQuadruples.mpr
        have ha0 : 0 < z.2.1 :=
          Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hz''.1).1 hm0
        have hb0 : 0 < z.2.2 :=
          Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hz''.2).1 hnsub0
        have hx0 : 0 < k * (z.1 / z.2.1) :=
          Nat.mul_pos hk (Nat.div_pos
            (Nat.le_of_dvd hm0 (Nat.mem_divisors.mp hz''.1).1) ha0)
        have hy0 : 0 < (n - k * z.1) / z.2.2 :=
          Nat.div_pos
            (Nat.le_of_dvd hnsub0 (Nat.mem_divisors.mp hz''.2).1) hb0
        have ham : z.2.1 * (z.1 / z.2.1) = z.1 := by
          rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.mem_divisors.mp hz''.1).1]
        have hbm : z.2.2 * ((n - k * z.1) / z.2.2) = n - k * z.1 := by
          rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.mem_divisors.mp hz''.2).1]
        have hsum : z.2.1 * (k * (z.1 / z.2.1)) +
            z.2.2 * ((n - k * z.1) / z.2.2) = n := by
          calc
            z.2.1 * (k * (z.1 / z.2.1)) +
                z.2.2 * ((n - k * z.1) / z.2.2) =
                k * (z.2.1 * (z.1 / z.2.1)) + (n - k * z.1) := by
                  rw [hbm]
                  ring
            _ = n := by rw [ham]; omega
        have ha0 : 0 < z.2.1 :=
          Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hz''.1).1 hm0
        have hb0 : 0 < z.2.2 :=
          Nat.pos_of_dvd_of_pos (Nat.mem_divisors.mp hz''.2).1 hnsub0
        have hxa : k * (z.1 / z.2.1) ≤
            z.2.1 * (k * (z.1 / z.2.1)) :=
          Nat.le_mul_of_pos_left _ ha0
        have hyb : (n - k * z.1) / z.2.2 ≤
            z.2.2 * ((n - k * z.1) / z.2.2) :=
          Nat.le_mul_of_pos_left _ hb0
        have hpart1 : z.2.1 * (k * (z.1 / z.2.1)) ≤ n := by
          exact le_trans (Nat.le_add_right _ _) hsum.le
        have hpart2 : z.2.2 * ((n - k * z.1) / z.2.2) ≤ n := by
          exact le_trans (Nat.le_add_left _ _) hsum.le
        have hx0 : 0 < k * (z.1 / z.2.1) :=
          Nat.mul_pos hk (Nat.div_pos
            (Nat.le_of_dvd hm0 (Nat.mem_divisors.mp hz''.1).1) ha0)
        have hy0 : 0 < (n - k * z.1) / z.2.2 :=
          Nat.div_pos
            (Nat.le_of_dvd hnsub0 (Nat.mem_divisors.mp hz''.2).1) hb0
        have hxab : z.2.1 ≤ n := le_trans
          (Nat.le_mul_of_pos_right _ hx0) hpart1
        have hyab : z.2.2 ≤ n := le_trans
          (Nat.le_mul_of_pos_right _ hy0) hpart2
        have hxle : k * (z.1 / z.2.1) ≤ n := le_trans
          (Nat.le_mul_of_pos_left _ ha0) hpart1
        have hyle : (n - k * z.1) / z.2.2 ≤ n := le_trans
          (Nat.le_mul_of_pos_left _ hb0) hpart2
        exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt ha0), hxab,
          Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hb0), hyab,
          Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hx0), hxle,
          Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hy0), hyle, hsum⟩
      · exact ⟨z.1 / z.2.1, by simp⟩
    change scaleIndex k ((z.2.1, z.2.2),
      k * (z.1 / z.2.1), (n - k * z.1) / z.2.2) = z
    apply Sigma.ext
    · dsimp [scaleIndex]
      have hdivk : k * (z.1 / z.2.1) / k = z.1 / z.2.1 :=
        Nat.mul_div_cancel_left _ hk
      have hdiva : z.2.1 * (z.1 / z.2.1) = z.1 := by
        rw [Nat.mul_comm, Nat.div_mul_cancel (Nat.mem_divisors.mp hz''.1).1]
      rw [hdivk, hdiva]
    · exact heq_of_eq (Sigma.eta z.2)
  · intro q hq
    have hqfilter := Finset.mem_filter.mp hq
    have hq' := mem_huardPositiveQuadruples.mp hqfilter.1
    have ha0 : 0 < q.1.1 := lt_of_lt_of_le Nat.zero_lt_one hq'.1
    have ham : q.1.1 * (q.2.1 / k) =
        q.1.1 * (q.2.1 / k) := rfl
    change (q.1.1 : ℤ) * (q.1.2 : ℤ) =
      (q.1.1 : ℤ) * (q.1.2 : ℤ)
    rfl

theorem qScaleCarrier_eq_scaledDivisorConvolution (k n : ℕ) (hk : 0 < k) :
    qScaleCarrier k n = scaledDivisorConvolution k n := by
  have hpoint : ∀ q : (ℕ × ℕ) × (ℕ × ℕ),
      (q.1.1 : ℤ) * (q.1.2 : ℤ) * divisibilityIndicator k (q.2.1 : ℤ) =
        if k ∣ q.2.1 then (q.1.1 : ℤ) * (q.1.2 : ℤ) else 0 := by
    intro q
    by_cases h : k ∣ q.2.1
    · have hi : divisibilityIndicator k (q.2.1 : ℤ) = 1 := by
        simp [divisibilityIndicator, Int.natCast_dvd_natCast, h]
      simp [h, hi]
    · have hi : divisibilityIndicator k (q.2.1 : ℤ) = 0 := by
        simp [divisibilityIndicator, Int.natCast_dvd_natCast, h]
      simp [h, hi]
  calc
    qScaleCarrier k n =
        ∑ q ∈ huardPositiveQuadruples n,
          if k ∣ q.2.1 then (q.1.1 : ℤ) * (q.1.2 : ℤ) else 0 := by
      unfold qScaleCarrier
      apply Finset.sum_congr rfl
      intro q hq
      exact hpoint q
    _ = ∑ q ∈ (huardPositiveQuadruples n).filter
          (fun q => k ∣ q.2.1),
          (q.1.1 : ℤ) * (q.1.2 : ℤ) := by
      rw [Finset.sum_filter]
    _ = ∑ z ∈ scaleSigma k n, (z.2.1 : ℤ) * (z.2.2 : ℤ) :=
      scaleCarrier_sum_reindex hk n
    _ = scaledDivisorConvolution k n := by
      unfold scaledDivisorConvolution
      simp only [ordinaryDivisorCurrent, Finset.sum_mul, Finset.mul_sum]
      conv_lhs =>
        rw [scaleSigma, Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.sum_sigma, Finset.sum_comm]

#print axioms qMinusCarrier_eq_huardMinusCurrent
#print axioms qPlusCarrier_eq_huardPlusCurrent
#print axioms qScaleCarrier_eq_scaledDivisorConvolution

end Soma.Holonics.Millennium.FamilyTunnellJacobiHuardCarrierBridges
