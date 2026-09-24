import Mathlib
import ElementaryHolonics.RH.FosterClassFlux
import ElementaryHolonics.RH.XiGrowth
import ElementaryHolonics.RH.HeatEquationEntire

/-!
# FT4 (i): `ξ` is a member of the Foster class, and the flow keeps the envelope

`ξ` is entire, symmetric, nonzero at `½`, and of growth `A exp(B ‖w‖^{3/2})` by `XiGrowth`; so it
is a member, and every FT0--FT3 theorem of the class applies to it. The flow `heatE t f` of a
function of growth `A exp(B ‖w‖^ρ)` has growth `A' exp(B 2^ρ ‖w‖^ρ)` with `A'` the sum of the
majorant of `HeatFlowEntire`. Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterClassHeat

open Complex
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiGrowth
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.FosterClassLandau

/-- **`ξ` is a member of the Foster class.** -/
instance instFosterClassRiemannXi : FosterClass riemannXi (Cθ * Real.exp 74 + 1) 10 (3 / 2) where
  diff := differentiable_riemannXi
  symm := riemannXi_one_sub
  centre := XiCentre.riemannXi_one_half_ne_zero
  A_pos := add_pos (mul_pos Cθ_pos (Real.exp_pos _)) one_pos
  B_nonneg := by norm_num
  σ_pos := by norm_num
  σ_lt_two := by norm_num
  growth := hasGrowth_riemannXi

/-- The sum of the majorant of the flow at time `t`. -/
def flowSum (B ρ t : ℝ) : ℝ :=
  ∑' k, majorant (4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ)) (2 / ρ - 1) k

/-- **The flow keeps the envelope**: `heatE t f` has growth `A · flowSum · exp(B 2^ρ ‖w‖^ρ)`. -/
theorem hasGrowth_heatE {f : ℂ → ℂ} {A B ρ : ℝ} (hf : Differentiable ℂ f) (hg : HasGrowth f A B ρ)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) (t : ℝ) :
    HasGrowth (heatE t f) (A * flowSum B ρ t) (B * 2 ^ ρ) ρ := by
  intro z
  have hδ : 0 < 2 / ρ - 1 := by
    rw [sub_pos, lt_div_iff₀ hρ0]
    linarith
  have hC : 0 ≤ 4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ) := by positivity
  have hsum := summable_majorant hC hδ
  have hterm : ∀ k, ‖heatTerm t f z k‖ ≤ (A * Real.exp (B * 2 ^ ρ * ‖z‖ ^ ρ)) *
      majorant (4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ)) (2 / ρ - 1) k :=
    fun k => norm_heatTerm_le_majorant hf hg hA hB hρ0 t (norm_nonneg z) le_rfl k
  have hsum' : Summable (fun k => ‖heatTerm t f z k‖) := summable_heatTerm hf hg hA hB hρ0 hρ2 t z
  calc ‖heatE t f z‖ = ‖∑' k, heatTerm t f z k‖ := rfl
    _ ≤ ∑' k, ‖heatTerm t f z k‖ := norm_tsum_le_tsum_norm hsum'
    _ ≤ ∑' k, (A * Real.exp (B * 2 ^ ρ * ‖z‖ ^ ρ)) *
          majorant (4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ)) (2 / ρ - 1) k :=
        Summable.tsum_le_tsum hterm hsum' (hsum.mul_left _)
    _ = A * flowSum B ρ t * Real.exp (B * 2 ^ ρ * ‖z‖ ^ ρ) := by
        rw [tsum_mul_left]
        unfold flowSum
        ring

theorem flowSum_nonneg {B ρ t : ℝ} (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) :
    0 ≤ flowSum B ρ t := by
  unfold flowSum
  apply tsum_nonneg
  intro k
  unfold majorant
  split_ifs
  · exact zero_le_one
  · positivity

theorem flowSum_pos {B ρ t : ℝ} (hB : 0 ≤ B) (hρ0 : 0 < ρ) (hρ2 : ρ < 2) :
    0 < flowSum B ρ t := by
  have hδ : 0 < 2 / ρ - 1 := by
    rw [sub_pos, lt_div_iff₀ hρ0]
    linarith
  have hC : 0 ≤ 4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ) := by positivity
  have hsum := summable_majorant hC hδ
  unfold flowSum
  have h0 : majorant (4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ)) (2 / ρ - 1) 0 = 1 := by
    unfold majorant
    simp
  have hnn : ∀ k, 0 ≤ majorant (4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ)) (2 / ρ - 1) k := by
    intro k
    unfold majorant
    split_ifs
    · exact zero_le_one
    · positivity
  calc (0 : ℝ) < 1 := one_pos
    _ = majorant (4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ)) (2 / ρ - 1) 0 := h0.symm
    _ ≤ ∑' k, majorant (4 * Real.exp 1 * |t| * Real.exp (B * 2 ^ ρ)) (2 / ρ - 1) k :=
        hsum.le_tsum 0 (fun k _ => hnn k)

/-- The growth envelope of the flow of `ξ`. -/
theorem hasGrowth_heatE_riemannXi (t : ℝ) :
    HasGrowth (heatE t riemannXi) ((Cθ * Real.exp 74 + 1) * flowSum 10 (3 / 2) t)
      (10 * 2 ^ (3 / 2 : ℝ)) (3 / 2) :=
  hasGrowth_heatE differentiable_riemannXi hasGrowth_riemannXi A_nonneg (by norm_num) (by norm_num)
    (by norm_num) t

end Soma.Holonics.RH.FosterClassHeat
