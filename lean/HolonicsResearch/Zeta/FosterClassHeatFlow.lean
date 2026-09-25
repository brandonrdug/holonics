import Mathlib
import HolonicsResearch.Zeta.FosterClassFlux
import HolonicsResearch.Zeta.FosterClassHeat
import HolonicsResearch.Zeta.HeatKernelPhi
import HolonicsResearch.Zeta.PhaseFlowLedger
import HolonicsResearch.Zeta.ZeroDynamicsEntire

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

namespace Holonics.Zeta.FosterClassHeatFlow

open Complex
open Holonics.Zeta.RiemannXi
open Holonics.Zeta.XiGrowth
open Holonics.Zeta.EntireDerivativeGrowth
open Holonics.Zeta.HeatFlowEntire
open Holonics.Zeta.HeatEquationEntire
open Holonics.Zeta.ZeroDynamicsEntire
open Holonics.Zeta.PhaseFlowLedger
open Holonics.Zeta.FosterClassLandau
open Holonics.Zeta.FosterClassHeat
open Holonics.Zeta.HeatKernelPhi

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
  exact Holonics.Zeta.FosterClassFlux.flux (f := heatE t riemannXi) (hzero t) hs

end Holonics.Zeta.FosterClassHeatFlow
