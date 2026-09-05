import ElementaryHolonics.Millennium.NavierStokesAxisJetPerturbation

/-!
# A tail-preserving viscous axis shape family

The family below is an actual smooth positive function.  The two bounded even weights provide a
low-order shape parameter and a first changed high-order parameter while preserving the algebraic
tail.  This file makes no PDE or recurrence claim.
-/

noncomputable section

open ContDiff Set Filter

namespace Soma.Holonics.Millennium.NavierStokesViscousAxisShape

open Soma.Holonics.Millennium.NavierStokesAlgebraicAxis
open Soma.Holonics.Millennium.NavierStokesAxisJetPerturbation

def chi (z : ℝ) : ℝ := z ^ 2 / (1 + 2 * z ^ 2) ^ 2

def eta (z : ℝ) : ℝ := z ^ 28 / (1 + 2 * z ^ 2) ^ 15

def shapeProfile (p a A B E mu z : ℝ) : ℝ :=
  a * algebraicProfile p z * (1 + mu * (A + B * chi z + E * eta z))

theorem chi_nonneg (z : ℝ) : 0 ≤ chi z := by
  unfold chi
  positivity

theorem chi_le (z : ℝ) : chi z ≤ 1 / 8 := by
  have h : 0 ≤ (2 * z ^ 2 - 1) ^ 2 := sq_nonneg _
  have hd : 0 < (1 + 2 * z ^ 2) ^ 2 := by positivity
  unfold chi
  apply (div_le_iff₀ hd).mpr
  nlinarith

theorem eta_nonneg (z : ℝ) : 0 ≤ eta z := by
  unfold eta
  positivity

theorem eta_le (z : ℝ) : eta z ≤ 1 / 16384 := by
  have hbase : 0 < 1 + 2 * z ^ 2 := by positivity
  have hpow : (2 * z ^ 2) ^ 14 ≤ (1 + 2 * z ^ 2) ^ 14 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 14
  have hmul : (1 + 2 * z ^ 2) ^ 14 ≤ (1 + 2 * z ^ 2) ^ 15 := by
    calc
      (1 + 2 * z ^ 2) ^ 14 = (1 + 2 * z ^ 2) ^ 14 * 1 := by ring
      _ ≤ (1 + 2 * z ^ 2) ^ 14 * (1 + 2 * z ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg z]) (pow_nonneg hbase.le 14)
      _ = (1 + 2 * z ^ 2) ^ 15 := (pow_succ _ 14).symm
  have hbound : 16384 * z ^ 28 ≤ (1 + 2 * z ^ 2) ^ 15 := by
    have he : (2 * z ^ 2) ^ 14 = 16384 * z ^ 28 := by
      rw [mul_pow, ← pow_mul]
      norm_num
    exact he ▸ hpow.trans hmul
  unfold eta
  apply (div_le_iff₀ (pow_pos hbase 15)).mpr
  nlinarith

theorem chi_contDiff : ContDiff ℝ ∞ chi := by
  unfold chi
  apply ContDiff.div (by fun_prop) (by fun_prop)
  intro z
  positivity

theorem eta_contDiff : ContDiff ℝ ∞ eta := by
  unfold eta
  apply ContDiff.div (by fun_prop) (by fun_prop)
  intro z
  positivity

theorem chi_even (z : ℝ) : chi (-z) = chi z := by
  unfold chi
  simp only [Even.neg_pow (by decide : Even 2)]

theorem eta_even (z : ℝ) : eta (-z) = eta z := by
  unfold eta
  simp only [Even.neg_pow (by decide : Even 28), Even.neg_pow (by decide : Even 2)]

theorem chi_tendsto_zero : Tendsto chi atTop (nhds 0) := by
  have hi : Tendsto (fun z : ℝ ↦ z⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hlim : Tendsto (fun z : ℝ ↦ (z⁻¹) ^ 2 / (2 + (z⁻¹) ^ 2) ^ 2)
      atTop (nhds 0) := by
    have hd : Tendsto (fun z : ℝ ↦ (2 + (z⁻¹) ^ 2) ^ 2) atTop (nhds ((2 : ℝ) ^ 2)) := by
      convert (tendsto_const_nhds.add (hi.pow 2)).pow 2 using 1 <;> norm_num
    convert (hi.pow 2).div hd (by norm_num) using 1 <;>
      first | rfl | norm_num | (funext z; simp [Pi.div_apply, inv_pow])
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
  have hz0 : z ≠ 0 := by linarith
  unfold chi
  field_simp [hz0]
  ring

theorem eta_tendsto_zero : Tendsto eta atTop (nhds 0) := by
  have hi : Tendsto (fun z : ℝ ↦ z⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hlim : Tendsto (fun z : ℝ ↦ (z⁻¹) ^ 2 / (2 + (z⁻¹) ^ 2) ^ 15)
      atTop (nhds 0) := by
    have hd : Tendsto (fun z : ℝ ↦ (2 + (z⁻¹) ^ 2) ^ 15) atTop
        (nhds ((2 : ℝ) ^ 15)) := by
      convert (tendsto_const_nhds.add (hi.pow 2)).pow 15 using 1 <;> norm_num
    convert (hi.pow 2).div hd (by norm_num) using 1 <;>
      first | rfl | norm_num | (funext z; simp [Pi.div_apply, inv_pow])
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
  have hz0 : z ≠ 0 := by linarith
  unfold eta
  field_simp [hz0]
  ring

theorem shapeProfile_positive
    {p a A B E mu z : ℝ} (ha : 0 < a) (hmu : 0 ≤ mu)
    (hlower : 0 < 1 + mu * A - mu * (|B| / 8 + |E| / 16384)) :
    0 < shapeProfile p a A B E mu z := by
  apply mul_pos (mul_pos ha (algebraicProfile_positive p z))
  have hB : -|B| / 8 ≤ B * chi z := by
    by_cases hB0 : 0 ≤ B
    · have : 0 ≤ B * chi z := mul_nonneg hB0 (chi_nonneg z)
      linarith [abs_of_nonneg hB0]
    · have hB' : B * (1 / 8) ≤ B * chi z :=
        mul_le_mul_of_nonpos_left (chi_le z) (le_of_not_ge hB0)
      rw [abs_of_neg (lt_of_not_ge hB0)]
      convert hB' using 1 <;> ring
  have hE : -|E| / 16384 ≤ E * eta z := by
    by_cases hE0 : 0 ≤ E
    · have : 0 ≤ E * eta z := mul_nonneg hE0 (eta_nonneg z)
      linarith [abs_of_nonneg hE0]
    · have hE' : E * (1 / 16384) ≤ E * eta z :=
        mul_le_mul_of_nonpos_left (eta_le z) (le_of_not_ge hE0)
      rw [abs_of_neg (lt_of_not_ge hE0)]
      convert hE' using 1 <;> ring
  nlinarith

theorem shapeProfile_contDiff (p a A B E mu : ℝ) :
    ContDiff ℝ ∞ (shapeProfile p a A B E mu) := by
  have hinside : ContDiff ℝ ∞
      (fun z : ℝ ↦ 1 + mu * (A + B * chi z + E * eta z)) := by
    have hinner : ContDiff ℝ ∞ (fun z : ℝ ↦ A + B * chi z + E * eta z) := by
      have hA : ContDiff ℝ ∞ (fun _ : ℝ => A) := contDiff_const
      have hB : ContDiff ℝ ∞ (fun _ : ℝ => B) := contDiff_const
      have hE : ContDiff ℝ ∞ (fun _ : ℝ => E) := contDiff_const
      simpa [add_assoc] using hA.add ((hB.mul chi_contDiff).add (hE.mul eta_contDiff))
    have hmu : ContDiff ℝ ∞ (fun _ : ℝ => mu) := contDiff_const
    have hone : ContDiff ℝ ∞ (fun _ : ℝ => (1 : ℝ)) := contDiff_const
    exact hone.add (hmu.mul hinner)
  exact ((contDiff_const : ContDiff ℝ ∞ (fun _ : ℝ => a)).mul
    (algebraicProfile_contDiff p)).mul hinside

@[simp] theorem shapeProfile_zero (p a A B E mu : ℝ) :
    shapeProfile p a A B E mu 0 = a * (1 + mu * A) := by
  simp [shapeProfile, chi, eta, algebraicProfile]

theorem shapeProfile_relative_tail (p a A B E mu : ℝ) (ha : a ≠ 0) :
    Tendsto (fun z ↦ shapeProfile p a A B E mu z / (a * algebraicProfile p z))
      atTop (nhds (1 + mu * A)) := by
  have hEq : (fun z ↦ shapeProfile p a A B E mu z / (a * algebraicProfile p z)) =
      (fun z ↦ 1 + mu * (A + B * chi z + E * eta z)) := by
    funext z
    unfold shapeProfile
    field_simp [ha, (algebraicProfile_positive p z).ne']
  rw [hEq]
  have hchi := chi_tendsto_zero.const_mul B
  have heta := eta_tendsto_zero.const_mul E
  have hsum : Tendsto (fun z ↦ B * chi z + E * eta z) atTop (nhds 0) :=
    by simpa using hchi.add heta
  have hbase : Tendsto (fun _ : ℝ ↦ 1 + mu * A) atTop (nhds (1 + mu * A)) :=
    tendsto_const_nhds
  convert hbase.add (hsum.const_mul mu) using 1 <;>
    simp [mul_add, add_comm, add_left_comm, add_assoc]

theorem chi_low_jets :
    iteratedDeriv 1 chi 0 = 0 ∧ iteratedDeriv 2 chi 0 = 2 := by
  have hfactor : ContDiff ℝ ∞ (fun z : ℝ ↦ 1 / (1 + 2 * z ^ 2) ^ 2) := by
    apply ContDiff.div (by fun_prop) (by fun_prop)
    intro z
    positivity
  have hchi : chi = fun z : ℝ ↦ z ^ 2 * (1 / (1 + 2 * z ^ 2) ^ 2) := by
    funext z
    unfold chi
    field_simp
  constructor
  · rw [hchi]
    exact iteratedDeriv_monomial_mul_zero_of_lt 1 2 (by decide) _ hfactor
  · rw [hchi, iteratedDeriv_monomial_mul_at_order 2 _ hfactor]
    norm_num

theorem eta_low_jets :
    iteratedDeriv 0 eta 0 = 0 ∧ iteratedDeriv 1 eta 0 = 0 ∧ iteratedDeriv 2 eta 0 = 0 := by
  have hfactor : ContDiff ℝ ∞ (fun z : ℝ ↦ 1 / (1 + 2 * z ^ 2) ^ 15) := by
    apply ContDiff.div (by fun_prop) (by fun_prop)
    intro z
    positivity
  have heta : eta = fun z : ℝ ↦ z ^ 28 * (1 / (1 + 2 * z ^ 2) ^ 15) := by
    funext z
    unfold eta
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · rw [heta]
    simp
  · rw [heta]
    exact iteratedDeriv_monomial_mul_zero_of_lt 1 28 (by decide) _ hfactor
  · rw [heta]
    exact iteratedDeriv_monomial_mul_zero_of_lt 2 28 (by decide) _ hfactor

theorem shapeProfile_second_iteratedDeriv_zero
    (p a A B E mu : ℝ) :
    iteratedDeriv 2 (shapeProfile p a A B E mu) 0 =
      a * (-p * (1 + mu * A) + 2 * mu * B) := by
  have hG0 : iteratedDeriv 0 (algebraicProfile p) 0 = 1 := by simp
  have hG1 : iteratedDeriv 1 (algebraicProfile p) 0 = 0 := by
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
      (algebraicProfile_deriv_zero p)
  have hG2 : iteratedDeriv 2 (algebraicProfile p) 0 = -p := by
    simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
      (algebraicProfile_second_jet_zero p).deriv
  have hC0 : iteratedDeriv 0 (fun _ : ℝ ↦ 1 + mu * A) 0 = 1 + mu * A := by simp
  have hC1 : iteratedDeriv 1 (fun _ : ℝ ↦ 1 + mu * A) 0 = 0 := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  have hC2 : iteratedDeriv 2 (fun _ : ℝ ↦ 1 + mu * A) 0 = 0 := by
    simp [iteratedDeriv_succ, iteratedDeriv_zero]
  have hQ0 : iteratedDeriv 0 (fun z : ℝ ↦ B * chi z + E * eta z) 0 = 0 := by
    simp [iteratedDeriv_zero, chi, eta]
  have hQ1 : iteratedDeriv 1 (fun z : ℝ ↦ B * chi z + E * eta z) 0 = 0 := by
    have hc : ContDiff ℝ 1 chi := chi_contDiff.of_le
      (WithTop.coe_le_coe.mpr (by norm_num))
    have he : ContDiff ℝ 1 eta := eta_contDiff.of_le
      (WithTop.coe_le_coe.mpr (by norm_num))
    have hBchi : ContDiffAt ℝ 1 (fun z : ℝ ↦ B * chi z) 0 :=
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => B)).mul hc).contDiffAt
    have hEeta : ContDiffAt ℝ 1 (fun z : ℝ ↦ E * eta z) 0 :=
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => E)).mul he).contDiffAt
    rw [iteratedDeriv_fun_add hBchi hEeta]
    rw [iteratedDeriv_fun_mul
      ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => B)).contDiffAt) hc.contDiffAt,
      iteratedDeriv_fun_mul
        ((contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => E)).contDiffAt) he.contDiffAt]
    simp [Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero, chi_low_jets,
      eta_low_jets]
  have hQ2 : iteratedDeriv 2 (fun z : ℝ ↦ B * chi z + E * eta z) 0 = 2 * B := by
    have hc : ContDiff ℝ 2 chi := chi_contDiff.of_le
      (WithTop.coe_le_coe.mpr (by norm_num))
    have he : ContDiff ℝ 2 eta := eta_contDiff.of_le
      (WithTop.coe_le_coe.mpr (by norm_num))
    have hBchi : ContDiffAt ℝ 2 (fun z : ℝ ↦ B * chi z) 0 :=
      ((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => B)).mul hc).contDiffAt
    have hEeta : ContDiffAt ℝ 2 (fun z : ℝ ↦ E * eta z) 0 :=
      ((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => E)).mul he).contDiffAt
    rw [iteratedDeriv_fun_add hBchi hEeta]
    rw [iteratedDeriv_fun_mul
      ((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => B)).contDiffAt) hc.contDiffAt,
      iteratedDeriv_fun_mul
        ((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => E)).contDiffAt) he.contDiffAt]
    simp [Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero, chi_low_jets,
      eta_low_jets]
    ring
  let G : ℝ → ℝ := algebraicProfile p
  let C : ℝ → ℝ := fun _ ↦ 1 + mu * A
  let R : ℝ → ℝ := fun z ↦ mu * (B * chi z + E * eta z)
  have hG : ContDiff ℝ 2 G := (algebraicProfile_contDiff p).of_le
    (WithTop.coe_le_coe.mpr (by norm_num))
  have hC : ContDiff ℝ 2 C := contDiff_const
  have hR : ContDiff ℝ 2 R := by
    have hchi : ContDiff ℝ 2 chi := chi_contDiff.of_le
      (WithTop.coe_le_coe.mpr (by norm_num))
    have heta : ContDiff ℝ 2 eta := eta_contDiff.of_le
      (WithTop.coe_le_coe.mpr (by norm_num))
    have hB : ContDiff ℝ 2 (fun z : ℝ ↦ B * chi z) :=
      (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => B)).mul hchi
    have hE : ContDiff ℝ 2 (fun z : ℝ ↦ E * eta z) :=
      (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => E)).mul heta
    have hsum : ContDiff ℝ 2 (fun z : ℝ ↦ B * chi z + E * eta z) := hB.add hE
    exact (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => mu)).mul hsum
  have hshape : shapeProfile p a A B E mu =
      (fun z ↦ a * G z * C z) + (fun z ↦ a * G z * R z) := by
    funext z
    dsimp [shapeProfile, G, C, R]
    ring
  have hA0 : ContDiffAt ℝ 2 (fun _ : ℝ => a) 0 := by
    exact (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => a)).contDiffAt
  have hAG := iteratedDeriv_fun_mul hA0 hG.contDiffAt
  have hQ : ContDiffAt ℝ 2 (fun z : ℝ ↦ B * chi z + E * eta z) 0 := by
    have hchi : ContDiff ℝ 2 chi := chi_contDiff.of_le
      (WithTop.coe_le_coe.mpr (by norm_num))
    have heta : ContDiff ℝ 2 eta := eta_contDiff.of_le
      (WithTop.coe_le_coe.mpr (by norm_num))
    exact (((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => B)).mul hchi).add
      ((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => E)).mul heta)).contDiffAt
  have hmu : ContDiffAt ℝ 2 (fun _ : ℝ => mu) 0 := by
    exact (contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => mu)).contDiffAt
  have hRjets := iteratedDeriv_fun_mul hmu hQ
  rw [hshape]
  change iteratedDeriv 2 (fun z ↦ a * G z * C z + a * G z * R z) 0 = _
  have hA : ContDiffAt ℝ 2 (fun z : ℝ ↦ a * G z) 0 :=
    ((contDiff_const : ContDiff ℝ 2 (fun _ : ℝ => a)).mul hG).contDiffAt
  have hAC := iteratedDeriv_fun_mul hA hC.contDiffAt
  have hAR := iteratedDeriv_fun_mul hA hR.contDiffAt
  rw [iteratedDeriv_fun_add (hA.mul hC.contDiffAt) (hA.mul hR.contDiffAt), hAC, hAR]
  simp [G, C, R, hAG, hRjets, hG0, hG1, hG2, hC0, hC1, hC2, hQ0, hQ1, hQ2,
    Finset.sum_range_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  ring

theorem shapeProfile_second_deriv_zero
    (p a A B E mu : ℝ) :
    deriv (deriv (shapeProfile p a A B E mu)) 0 =
      a * (-p * (1 + mu * A) + 2 * mu * B) := by
  simpa [iteratedDeriv_succ, iteratedDeriv_zero] using
    shapeProfile_second_iteratedDeriv_zero p a A B E mu

theorem eta_jets_below_28 (n : ℕ) (hn : n < 28) : iteratedDeriv n eta 0 = 0 := by
  have hfactor : ContDiff ℝ ∞ (fun z : ℝ ↦ 1 / (1 + 2 * z ^ 2) ^ 15) := by
    apply ContDiff.div (by fun_prop) (by fun_prop)
    intro z
    positivity
  have heq : eta = fun z : ℝ ↦ z ^ 28 * (1 / (1 + 2 * z ^ 2) ^ 15) := by
    funext z
    unfold eta
    ring
  rw [heq]
  exact iteratedDeriv_monomial_mul_zero_of_lt n 28 hn _ hfactor

theorem shapeProfile_time_hasDerivAt (p a A B E mu0 delta t z : ℝ) :
    HasDerivAt (fun τ ↦ shapeProfile p a A B E (mu0 * Real.exp (-delta * τ)) z)
      (-delta * (mu0 * Real.exp (-delta * t)) * a * algebraicProfile p z *
        (A + B * chi z + E * eta z)) t := by
  have hm := (((hasDerivAt_id t).const_mul (-delta)).exp).const_mul mu0
  have h := (((hm.mul_const (A + B * chi z + E * eta z)).const_add 1).const_mul
    (a * algebraicProfile p z))
  convert h using 1 <;> first | rfl | (simp only [id_eq] <;> ring)

#print axioms chi_le
#print axioms eta_le
#print axioms chi_contDiff
#print axioms eta_contDiff
#print axioms chi_tendsto_zero
#print axioms eta_tendsto_zero
#print axioms shapeProfile_positive
#print axioms shapeProfile_contDiff
#print axioms shapeProfile_relative_tail
#print axioms shapeProfile_second_iteratedDeriv_zero
#print axioms shapeProfile_second_deriv_zero
#print axioms eta_jets_below_28
#print axioms shapeProfile_time_hasDerivAt

end Soma.Holonics.Millennium.NavierStokesViscousAxisShape
