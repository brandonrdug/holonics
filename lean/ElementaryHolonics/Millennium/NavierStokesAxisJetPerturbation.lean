import ElementaryHolonics.Millennium.NavierStokesAlgebraicAxis
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# A positive axial perturbation with a specified first changed jet

The correction `z^30/(1+2z²)^16` leaves every axial jet below order thirty unchanged. Its
global bound provides positivity for a declared negative correction coefficient. These are
actual smooth functions; the finite radial compatibility calculation remains a separate receiver.
-/

noncomputable section

open ContDiff Filter
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesAxisJetPerturbation

open Soma.Holonics.Millennium.NavierStokesAlgebraicAxis
open Soma.Holonics.Millennium.NavierStokesAxialPrimitive

def correctionWeight (z : ℝ) : ℝ := z ^ 30 / (1 + 2 * z ^ 2) ^ 16

theorem correctionWeight_nonneg (z : ℝ) : 0 ≤ correctionWeight z := by
  unfold correctionWeight
  positivity

theorem correctionWeight_le (z : ℝ) : correctionWeight z ≤ 1 / 32768 := by
  have hbase : 0 < 1 + 2 * z ^ 2 := by positivity
  have hpow : (2 * z ^ 2) ^ 15 ≤ (1 + 2 * z ^ 2) ^ 15 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 15
  have hmul : (1 + 2 * z ^ 2) ^ 15 ≤ (1 + 2 * z ^ 2) ^ 16 := by
    calc
      (1 + 2 * z ^ 2) ^ 15 = (1 + 2 * z ^ 2) ^ 15 * 1 := by ring
      _ ≤ (1 + 2 * z ^ 2) ^ 15 * (1 + 2 * z ^ 2) :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg z]) (pow_nonneg hbase.le 15)
      _ = (1 + 2 * z ^ 2) ^ 16 := (pow_succ _ 15).symm
  have hbound : 32768 * z ^ 30 ≤ (1 + 2 * z ^ 2) ^ 16 := by
    have he : (2 * z ^ 2) ^ 15 = 32768 * z ^ 30 := by
      rw [mul_pow, ← pow_mul]
      norm_num
    exact he ▸ hpow.trans hmul
  unfold correctionWeight
  apply (div_le_iff₀ (pow_pos hbase 16)).mpr
  nlinarith

theorem correctionWeight_contDiff : ContDiff ℝ ∞ correctionWeight := by
  unfold correctionWeight
  apply ContDiff.div (by fun_prop) (by fun_prop)
  intro z
  positivity

theorem correctionWeight_inverse_chart (z : ℝ) (hz : z ≠ 0) :
    correctionWeight z = (z⁻¹) ^ 2 / (2 + (z⁻¹) ^ 2) ^ 16 := by
  unfold correctionWeight
  have hd : 1 + 2 * z ^ 2 ≠ 0 := by positivity
  have hi : 2 + (z⁻¹) ^ 2 ≠ 0 := by positivity
  field_simp [hz, hd, hi]
  ring

theorem correctionWeight_tendsto_zero : Tendsto correctionWeight atTop (nhds 0) := by
  have hi : Tendsto (fun z : ℝ ↦ z⁻¹) atTop (nhds 0) := tendsto_inv_atTop_zero
  have hd : Tendsto (fun z : ℝ ↦ (2 + (z⁻¹) ^ 2) ^ 16) atTop (nhds ((2 : ℝ) ^ 16)) := by
    convert (tendsto_const_nhds.add (hi.pow 2)).pow 16 using 1 <;> norm_num
  have hlim : Tendsto (fun z : ℝ ↦ (z⁻¹) ^ 2 / (2 + (z⁻¹) ^ 2) ^ 16) atTop (nhds 0) := by
    convert (hi.pow 2).div hd (by norm_num) using 1 <;> first | rfl | norm_num
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz
  exact (correctionWeight_inverse_chart z (by linarith)).symm

theorem correctionWeight_even (z : ℝ) : correctionWeight (-z) = correctionWeight z := by
  unfold correctionWeight
  have h30 : (-z) ^ 30 = z ^ 30 := by ring
  have h2 : (-z) ^ 2 = z ^ 2 := by ring
  rw [h30, h2]

def correctedProfile (p epsilon z : ℝ) : ℝ :=
  algebraicProfile p z * (1 + epsilon * correctionWeight z)

theorem correctedProfile_positive (p epsilon : ℝ) (hepsilon : -32768 < epsilon) (z : ℝ) :
    0 < correctedProfile p epsilon z := by
  apply mul_pos (algebraicProfile_positive p z)
  by_cases hsign : 0 ≤ epsilon
  · have := mul_nonneg hsign (correctionWeight_nonneg z)
    linarith
  · have hle := mul_le_mul_of_nonpos_left (correctionWeight_le z) (le_of_not_ge hsign)
    linarith

theorem correctedProfile_contDiff (p epsilon : ℝ) : ContDiff ℝ ∞ (correctedProfile p epsilon) :=
  (algebraicProfile_contDiff p).mul
    (contDiff_const.add (contDiff_const.mul correctionWeight_contDiff))

theorem correctedProfile_relative_tail (p epsilon : ℝ) :
    Tendsto (fun z ↦ correctedProfile p epsilon z / algebraicProfile p z) atTop (nhds 1) := by
  have heq : (fun z ↦ correctedProfile p epsilon z / algebraicProfile p z) =
      (fun z ↦ 1 + epsilon * correctionWeight z) := by
    funext z
    unfold correctedProfile
    field_simp [(algebraicProfile_positive p z).ne']
  rw [heq]
  convert tendsto_const_nhds.add (correctionWeight_tendsto_zero.const_mul epsilon) using 1 <;> simp

def correctionFactor (p epsilon z : ℝ) : ℝ :=
  epsilon * algebraicProfile p z / (1 + 2 * z ^ 2) ^ 16

theorem correctionFactor_contDiff (p epsilon : ℝ) : ContDiff ℝ ∞ (correctionFactor p epsilon) := by
  have hf := algebraicProfile_contDiff p
  unfold correctionFactor
  apply ContDiff.div (contDiff_const.mul hf) (by fun_prop)
  intro z
  positivity

theorem correctedProfile_eq (p epsilon : ℝ) :
    correctedProfile p epsilon = fun z ↦ algebraicProfile p z + z ^ 30 * correctionFactor p epsilon z := by
  funext z
  unfold correctedProfile correctionWeight correctionFactor
  ring

theorem iteratedDeriv_monomial_mul_zero_of_lt (n m : ℕ) (hn : n < m) (g : ℝ → ℝ)
    (hg : ContDiff ℝ ∞ g) : iteratedDeriv n (fun z ↦ z ^ m * g z) 0 = 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop)
    ((hg.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)]
  apply Finset.sum_eq_zero
  intro i hi
  have him : i ≠ m := (lt_of_le_of_lt (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) hn).ne
  rw [iteratedDeriv_fun_pow_zero, if_neg him]
  simp

theorem iteratedDeriv_monomial_mul_at_order (n : ℕ) (g : ℝ → ℝ) (hg : ContDiff ℝ ∞ g) :
    iteratedDeriv n (fun z ↦ z ^ n * g z) 0 = (n.factorial : ℝ) * g 0 := by
  rw [iteratedDeriv_fun_mul (by fun_prop)
    ((hg.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)]
  rw [Finset.sum_eq_single n]
  · simp [Nat.descFactorial_self]
  · intro i hi hin
    rw [iteratedDeriv_fun_pow_zero, if_neg hin]
    simp
  · simp

theorem correctedProfile_low_jets (p epsilon : ℝ) (n : ℕ) (hn : n < 30) :
    iteratedDeriv n (correctedProfile p epsilon) 0 = iteratedDeriv n (algebraicProfile p) 0 := by
  have hpow : ContDiff ℝ ∞ (fun z : ℝ ↦ z ^ 30) := by fun_prop
  have hterm : ContDiff ℝ ∞ (fun z : ℝ ↦ z ^ 30 * correctionFactor p epsilon z) :=
    hpow.mul (correctionFactor_contDiff p epsilon)
  rw [correctedProfile_eq]
  rw [iteratedDeriv_fun_add
    (((algebraicProfile_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    ((hterm.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)]
  rw [iteratedDeriv_monomial_mul_zero_of_lt n 30 hn _ (correctionFactor_contDiff p epsilon), add_zero]

theorem correctedProfile_thirtieth_jet (p epsilon : ℝ) :
    iteratedDeriv 30 (correctedProfile p epsilon) 0 = iteratedDeriv 30 (algebraicProfile p) 0 +
      (Nat.factorial 30 : ℝ) * epsilon := by
  have hpow : ContDiff ℝ ∞ (fun z : ℝ ↦ z ^ 30) := by fun_prop
  have hterm : ContDiff ℝ ∞ (fun z : ℝ ↦ z ^ 30 * correctionFactor p epsilon z) :=
    hpow.mul (correctionFactor_contDiff p epsilon)
  rw [correctedProfile_eq]
  rw [iteratedDeriv_fun_add
    (((algebraicProfile_contDiff p).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)
    ((hterm.of_le (WithTop.coe_le_coe.mpr le_top)).contDiffAt)]
  rw [iteratedDeriv_monomial_mul_at_order 30 _ (correctionFactor_contDiff p epsilon)]
  simp [correctionFactor]

theorem correctedProfile_axis_identity (alpha beta p epsilon : ℝ) (hepsilon : -32768 < epsilon) (z : ℝ) :
    (axialW alpha beta (correctedProfile p epsilon) z + beta * z) * deriv (correctedProfile p epsilon) z +
      (alpha + beta - deriv (axialW alpha beta (correctedProfile p epsilon)) z) *
        correctedProfile p epsilon z = 0 :=
  axialW_axis_identity alpha beta (correctedProfile p epsilon)
    ((correctedProfile_contDiff p epsilon).of_le (WithTop.coe_le_coe.mpr le_top))
    (correctedProfile_positive p epsilon hepsilon) z

/-- Exact rational correction returned by the complete radial-order-14 compatibility replay.
This literal's source attachment is computational; the bounds and resulting function laws below
are checked by the Lean kernel. -/
def resonanceRepairEpsilon : ℝ :=
  (-8851822921199785613621417443066016281182926116982311457301459062614200899082184589969057887127890434316223230613459928606880603954148898717772590150291106289149834700496174196627165384305943724327022743610371291630155196674390400336330191652461931 : ℝ) /
    (2838272940484286689524385409134752079054892203414085240934486274458469948803704562367704527585973618258549523989749589674272129378761138497724325712700187045655746357967459134217599592420687075949737742036030416606323585061489868662762373120000 : ℝ)

theorem resonanceRepairEpsilon_bounds : -32768 < resonanceRepairEpsilon ∧ resonanceRepairEpsilon < 0 := by
  norm_num [resonanceRepairEpsilon]

def resonanceRepairedAxis : ℝ → ℝ := correctedProfile (5 / 2) resonanceRepairEpsilon

theorem resonanceRepairedAxis_positive (z : ℝ) : 0 < resonanceRepairedAxis z :=
  correctedProfile_positive _ _ resonanceRepairEpsilon_bounds.1 z

theorem resonanceRepairedAxis_contDiff : ContDiff ℝ ∞ resonanceRepairedAxis :=
  correctedProfile_contDiff _ _

theorem resonanceRepairedAxis_low_jets (n : ℕ) (hn : n < 30) :
    iteratedDeriv n resonanceRepairedAxis 0 = iteratedDeriv n (algebraicProfile (5 / 2)) 0 :=
  correctedProfile_low_jets _ _ n hn

theorem resonanceRepairedAxis_thirtieth_jet :
    iteratedDeriv 30 resonanceRepairedAxis 0 = iteratedDeriv 30 (algebraicProfile (5 / 2)) 0 +
      (Nat.factorial 30 : ℝ) * resonanceRepairEpsilon :=
  correctedProfile_thirtieth_jet _ _

#print axioms correctionWeight_le
#print axioms correctionWeight_tendsto_zero
#print axioms correctedProfile_positive
#print axioms correctedProfile_relative_tail
#print axioms correctedProfile_low_jets
#print axioms correctedProfile_thirtieth_jet
#print axioms correctedProfile_axis_identity
#print axioms resonanceRepairEpsilon_bounds
#print axioms resonanceRepairedAxis_positive
#print axioms resonanceRepairedAxis_low_jets
#print axioms resonanceRepairedAxis_thirtieth_jet

end Soma.Holonics.Millennium.NavierStokesAxisJetPerturbation
