import ElementaryHolonics.Millennium.NavierStokesDyadicFlowCommutator
import ElementaryHolonics.Millennium.NavierStokesTerminalDyadicShellPacking

/-!
# The localized dyadic vorticity-flux receiver

**[definition; formal-checked]** The parabolic clock attached to the dyadic frequency length
`2^j` is its square.  It is therefore exactly `4^j`; the spatial scale and its clock remain
separately typed until this theorem relates them.

**[proved-derived; formal-checked]** The existing finite multiplier-flow commutator is specialized
to the actual velocity and vorticity Fourier modes of an admitted solution.  The companion
stretching band applies the same direct dyadic multiplier after the addressed interaction
`(omega(p) dot nabla) u(k-p)`.  Since the named commutator is
`P_j (u dot nabla omega) - u dot nabla (P_j omega)`, its orientation in the localized vorticity
equation is negative.  The finite localized nonlinear right-hand side is therefore negative
commutator plus stretching, with every advecting and transported address retained.

**[proved-derived; formal-checked, conditional]** A summable family of individual-shell clock
budgets bounds the robust `ENNReal` terminal packing by Tonelli and therefore returns the existing
terminal shell-packing receipt.

**[open]** This file does not identify the finite flux with the complete nonlinear convolution,
does not prove a projected shell evolution or localized enstrophy balance, and does not prove the
scale-summable clock-budget inequality.  The missing analytic passage is precisely a cofinal
finite-aperture limit together with a scale-local dissipative/Carleson estimate which bounds each
actual signed-shell time integral by the corresponding budget.  The conditional receipt below
records that finish line without asserting it.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxReceiver

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTerminalDyadicShellPacking
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity

/-! ## The parabolic shell clock -/

/-- The discrete parabolic clock paired with one dyadic spatial-frequency length. -/
def dyadicParabolicShellClock (level : ℕ) : ℕ :=
  dyadicRadius level ^ 2

/-- Squaring the dyadic spatial length gives exactly one base-four clock step per scale. -/
theorem dyadicParabolicShellClock_eq_four_pow (level : ℕ) :
    dyadicParabolicShellClock level = 4 ^ level := by
  change (2 ^ level) ^ 2 = 4 ^ level
  calc
    (2 ^ level) ^ 2 = 2 ^ (level * 2) := (pow_mul 2 level 2).symm
    _ = 2 ^ (2 * level) := by rw [Nat.mul_comm]
    _ = (2 ^ 2) ^ level := pow_mul 2 2 level
    _ = 4 ^ level := by norm_num

theorem dyadicParabolicShellClock_pos (level : ℕ) :
    0 < dyadicParabolicShellClock level := by
  rw [dyadicParabolicShellClock_eq_four_pow]
  positivity

/-! ## Actual-solution finite transport and stretching faces -/

/-- The finite direct-band commutator `[P_j, u dot nabla] omega`, specialized to the actual
velocity and vorticity coefficients of one strict-interior solution slice. -/
def finiteOpenVorticityTransportCommutatorCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) : ComplexVector :=
  finiteDyadicFlowCommutatorCoefficient scale aperture
    (openPeriodicVelocityFourierMode solution t)
    (openPeriodicVorticityFourierMode solution t) k

/-- The finite projected stretching band `P_j ((omega dot nabla) u)`.  The multiplier is applied
after the addressed interaction, so this is distinct from the transport commutator. -/
def finiteOpenVorticityStretchingBandCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) : ComplexVector :=
  (dyadicHodgeBandWeight scale k : ℂ) •
    finiteAdvectiveCoefficient aperture
      (openPeriodicVorticityFourierMode solution t)
      (openPeriodicVelocityFourierMode solution t) k

/-- The complete finite nonlinear right-hand side in the transported projected-vorticity
equation: negative transported-shell commutator plus the projected stretching band.  This
orientation agrees with
`omega_t + u dot nabla omega = nu * Delta omega + (omega dot nabla) u`. -/
def finiteOpenVorticityFluxCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) : ComplexVector :=
  -finiteOpenVorticityTransportCommutatorCoefficient
      solution t scale aperture k +
    finiteOpenVorticityStretchingBandCoefficient
      solution t scale aperture k

/-- **Exact finite localized-flux law.** Every intermediate pin and multiplier difference remains
visible.  This theorem is algebraic and makes no cofinal-convergence assertion. -/
theorem finiteOpenVorticityFluxCoefficient_eq_neg_transport_add_stretching
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) :
    finiteOpenVorticityFluxCoefficient solution t scale aperture k =
      -(∑ p ∈ aperture,
        ((dyadicHodgeBandWeight scale k : ℂ) -
            (dyadicHodgeBandWeight scale (transportedFrequencyAt k p) : ℂ)) •
          complexAdvectiveInteraction p (transportedFrequencyAt k p)
            (openPeriodicVelocityFourierMode solution t p)
            (openPeriodicVorticityFourierMode solution t
              (transportedFrequencyAt k p))) +
      (dyadicHodgeBandWeight scale k : ℂ) •
        (∑ p ∈ aperture,
          complexAdvectiveInteraction p (transportedFrequencyAt k p)
            (openPeriodicVorticityFourierMode solution t p)
            (openPeriodicVelocityFourierMode solution t
              (transportedFrequencyAt k p))) := by
  unfold finiteOpenVorticityFluxCoefficient
    finiteOpenVorticityTransportCommutatorCoefficient
    finiteOpenVorticityStretchingBandCoefficient
  rw [finiteDyadicFlowCommutatorCoefficient_eq_sum_difference]
  rfl

/-- Phase-bearing finite synthesis of the localized nonlinear vorticity flux on a declared
output aperture. -/
def finiteOpenVorticityFluxBand
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (advectingAperture outputAperture : Finset SpatialFrequency) :
    C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis
    (finiteOpenVorticityFluxCoefficient solution t scale advectingAperture)
    outputAperture

/-! ## Conditional Dini/Carleson clock service -/

/-- A scale-addressed family of finite clock budgets for the actual signed-shell receiver.  The
second field is the exact unproved localized service inequality.  It is deliberately stated per
shell so a later flux/commutator theorem can supply it without first collapsing the scale
population. -/
structure OpenPeriodicDyadicCarlesonClockServiceReceipt
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure) where
  budget : ℕ → ℝ≥0∞
  budget_tsum_lt_top : (∑' level : ℕ, budget level) < ∞
  shell_lintegral_le_budget : ∀ level : ℕ,
    (∫⁻ t in Ioo (0 : ℝ) T,
      ENNReal.ofReal
        (openPeriodicVorticityDyadicShellSpatialSupRate solution level t) ∂volume) ≤
      budget level

/-- **Conditional terminal passage.** A scale-summable family of localized clock budgets pays the
robust terminal shell population.  Tonelli is used through the existing packing identity, so an
infinite shell population cannot be totalized to zero. -/
theorem terminalDyadicShellPackingReceipt_of_carlesonClockService
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (service : OpenPeriodicDyadicCarlesonClockServiceReceipt solution) :
    OpenPeriodicTerminalDyadicShellPackingReceipt solution := by
  constructor
  rw [openPeriodicVorticityTerminalDyadicShellPacking_eq_tsum_lintegral]
  exact lt_of_le_of_lt
    (ENNReal.tsum_le_tsum service.shell_lintegral_le_budget)
    service.budget_tsum_lt_top

section Audit

#print axioms dyadicParabolicShellClock_eq_four_pow
#print axioms finiteOpenVorticityFluxCoefficient_eq_neg_transport_add_stretching
#print axioms terminalDyadicShellPackingReceipt_of_carlesonClockService

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxReceiver
