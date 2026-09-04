import Mathlib
import ElementaryHolonics.RH.FosterClassFlux
import ElementaryHolonics.RH.FosterClassHeat
import ElementaryHolonics.RH.HeatKernelPhi
import ElementaryHolonics.RH.PhaseFlowLedger
import ElementaryHolonics.RH.ZeroDynamicsEntire

/-!
# FT4 (i)--(ii): the flow of `ξ` is in the Foster class at every time, and the RT3 port is a theorem

`heatE t ξ` is entire (`HeatFlowEntire`), symmetric (`HeatEquationEntire`), of growth
`A_t exp(B ‖w‖^{3/2})` (`FosterClassHeat`), and nonzero at `½` at every time by the kernel
representation `heatE t ξ (½) = ∫ e^{−t u²} Φ(u) du > 0` (`HeatKernelPhi`). So it is a member of
the Foster class, and the comb flux of `FosterClassFlux` holds at every simple zero of every
`heatE t ξ`. With `ZeroDynamicsEntire.zero_curve_velocity_riemannXi`, the port
`PhaseFlowLedger.RodgersTaoZeroDynamics (fun t => heatE t ξ)` is discharged.

Every theorem is discharged with no `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.RH.FosterClassHeatFlow

open Complex
open Soma.Holonics.RH.RiemannXi
open Soma.Holonics.RH.XiGrowth
open Soma.Holonics.RH.EntireDerivativeGrowth
open Soma.Holonics.RH.HeatFlowEntire
open Soma.Holonics.RH.HeatEquationEntire
open Soma.Holonics.RH.ZeroDynamicsEntire
open Soma.Holonics.RH.PhaseFlowLedger
open Soma.Holonics.RH.FosterClassLandau
open Soma.Holonics.RH.FosterClassHeat
open Soma.Holonics.RH.HeatKernelPhi

/-- **`heatE t ξ` is a member of the Foster class at every time.** -/
instance instFosterClassHeatE (t : ℝ) :
    FosterClass (heatE t riemannXi) ((Cθ * Real.exp 74 + 1) * flowSum 10 (3 / 2) t)
      (10 * 2 ^ (3 / 2 : ℝ)) (3 / 2) where
  diff := differentiable_heatE_riemannXi t
  symm := heatE_riemannXi_one_sub t
  centre := heatE_riemannXi_half_ne_zero t
  A_pos := mul_pos (add_pos (mul_pos Cθ_pos (Real.exp_pos _)) one_pos)
    (flowSum_pos (by norm_num) (by norm_num) (by norm_num))
  B_nonneg := by positivity
  σ_pos := by norm_num
  σ_lt_two := by norm_num
  growth := hasGrowth_heatE_riemannXi t

/-- **The RT3 port is a theorem for the flow of `ξ`.** Along every `C¹` curve of zeros that is
simple at time `t`, the velocity is the principal-value comb flux about `½`. -/
theorem rodgersTaoZeroDynamics_heatE : RodgersTaoZeroDynamics (fun t => heatE t riemannXi) := by
  refine ⟨fun t z z' hz hz' hzero hs => ?_⟩
  have hv := zero_curve_velocity_riemannXi hz hz' hzero hs
  rw [hv]
  exact Soma.Holonics.RH.FosterClassFlux.flux (f := heatE t riemannXi) (hzero t) hs

end Soma.Holonics.RH.FosterClassHeatFlow
