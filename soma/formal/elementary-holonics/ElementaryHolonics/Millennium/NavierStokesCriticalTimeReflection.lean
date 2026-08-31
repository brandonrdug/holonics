import ElementaryHolonics.Millennium.NavierStokesCriticalMildReceiver

/-!
# Signed time reflection of the actual clocked vorticity source

**[proved-derived; formal-checked]**  The actual nonlinear source at an earlier time is split,
before any coefficient norm, into its signed difference from the target-time source and the
frozen target-time source.  The standing heat clock and curl receiver are linear, so the exact
clocked coefficient and the exact compact mild integrand preserve that split.

The source-difference population is retained as an extended Dini reconstruction fibre: elapsed
time is integrated against the norm of the literal native `H2` source difference divided by that
elapsed time.  The fibre may equal infinity.  No finiteness, Hölder rate, Dini rate, or terminal
uniformity is assumed or claimed here.

This is the cancellation-retaining decomposition required before an endpoint `r⁻¹` estimate can
be attempted.  It does not inhabit critical terminal control.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesCriticalTimeReflection

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalMildReceiver
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Linearity of the standing clock/curl passage -/

/-- The standing heat clock preserves subtraction of native weighted `H2` sources before the
curl receiver is taken. -/
theorem heatTransportedH2SourceCoefficient_sub
    (nu elapsed : ℝ) (left right : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) :
    heatTransportedH2SourceCoefficient nu elapsed (left - right) k =
      heatTransportedH2SourceCoefficient nu elapsed left k -
        heatTransportedH2SourceCoefficient nu elapsed right k := by
  ext component
  simp only [heatTransportedH2SourceCoefficient, Pi.sub_apply,
    weightedSobolevRawCoefficients_apply, lp.coeFn_sub]
  ring

/-- Curl is applied to the signed clocked difference, rather than to two absolute populations. -/
theorem heatTransportedH2SourceCurlCoefficient_sub
    (nu elapsed : ℝ) (left right : PeriodicVectorWeightedSobolev 2)
    (k : SpatialFrequency) :
    heatTransportedH2SourceCurlCoefficient nu elapsed (left - right) k =
      heatTransportedH2SourceCurlCoefficient nu elapsed left k -
        heatTransportedH2SourceCurlCoefficient nu elapsed right k := by
  simp only [heatTransportedH2SourceCurlCoefficient,
    heatTransportedH2SourceCoefficient_sub]
  exact map_sub (frequencyCurlMultiplierCLM k)
    (heatTransportedH2SourceCoefficient nu elapsed left k)
    (heatTransportedH2SourceCoefficient nu elapsed right k)

/-! ## The actual source increment and its Dini reconstruction fibre -/

/-- Literal native nonlinear-source difference between two actual strict-interior slices. -/
def openSharpNonlinearSourceIncrement
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (targetTime sourceTime : Ioo (0 : ℝ) T) :
    PeriodicVectorWeightedSobolev 2 :=
  sharpNonlinearSource (openVelocityWeightedH3State solution sourceTime) -
    sharpNonlinearSource (openVelocityWeightedH3State solution targetTime)

/-- The actual source difference at elapsed time `r`, totalized only to give the Dini fibre a
real-domain chart.  On `0 < r < horizon < targetTime` it is literally `N(target-r)-N(target)`. -/
def openSharpSourceElapsedIncrement
    {T nu target horizon : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (htarget : target ∈ Ioo (0 : ℝ) T) (hhorizon : horizon < target)
    (elapsed : ℝ) : PeriodicVectorWeightedSobolev 2 :=
  if helapsed : elapsed ∈ Ioo (0 : ℝ) horizon then
    openSharpNonlinearSourceIncrement solution ⟨target, htarget⟩
      ⟨target - elapsed,
        sub_pos.mpr (helapsed.2.trans hhorizon),
        (sub_lt_self target helapsed.1).trans htarget.2⟩
  else 0

/-- Extended Dini reconstruction fibre of the literal actual source increments.  It is retained
in `ℝ≥0∞`, so failure of endpoint integrability remains visible as the value `∞`. -/
def openSharpSourceDiniReconstructionFiber
    {T nu target horizon : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (htarget : target ∈ Ioo (0 : ℝ) T) (hhorizon : horizon < target) : ℝ≥0∞ :=
  ∫⁻ elapsed in Ioo (0 : ℝ) horizon,
    ENNReal.ofReal (‖openSharpSourceElapsedIncrement solution htarget hhorizon elapsed‖ /
      elapsed)

/-- Inside its addressed elapsed aperture, the totalized fibre recovers exactly the native
source difference which produced it. -/
theorem openSharpSourceElapsedIncrement_eq
    {T nu target horizon elapsed : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (htarget : target ∈ Ioo (0 : ℝ) T) (hhorizon : horizon < target)
    (helapsed : elapsed ∈ Ioo (0 : ℝ) horizon) :
    openSharpSourceElapsedIncrement solution htarget hhorizon elapsed =
      openSharpNonlinearSourceIncrement solution ⟨target, htarget⟩
        ⟨target - elapsed,
          sub_pos.mpr (helapsed.2.trans hhorizon),
          (sub_lt_self target helapsed.1).trans htarget.2⟩ := by
  simp [openSharpSourceElapsedIncrement, helapsed]

/-! ## Exact reflected/frozen decomposition -/

/-- The clocked actual nonlinear source is exactly its signed target-time increment plus the
frozen target-time face.  No norm or triangle inequality has occurred. -/
theorem heatTransportedOpenSharpSource_eq_increment_add_frozen
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (targetTime sourceTime : Ioo (0 : ℝ) T)
    (elapsed : ℝ) (k : SpatialFrequency) :
    heatTransportedH2SourceCurlCoefficient nu elapsed
        (sharpNonlinearSource (openVelocityWeightedH3State solution sourceTime)) k =
      heatTransportedH2SourceCurlCoefficient nu elapsed
          (openSharpNonlinearSourceIncrement solution targetTime sourceTime) k +
        heatTransportedH2SourceCurlCoefficient nu elapsed
          (sharpNonlinearSource (openVelocityWeightedH3State solution targetTime)) k := by
  rw [openSharpNonlinearSourceIncrement,
    heatTransportedH2SourceCurlCoefficient_sub]
  abel

/-- On the exact compact mild interval, the actual signed integrand is its reflected source
increment plus its frozen target-time face.  This is the source-time reflection before absolute
coefficient mass. -/
theorem compactStokesTransportedVorticityNonlinearMode_eq_reflected_add_frozen
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) {sourceTime : ℝ} (hsourceTime : sourceTime ∈ Icc s t) :
    compactStokesTransportedVorticityNonlinearMode
        solution hs hst ht k sourceTime =
      -heatTransportedH2SourceCurlCoefficient nu (t - sourceTime)
          (openSharpNonlinearSourceIncrement solution
            ⟨t, hs.trans_le hst, ht⟩
            ⟨sourceTime, hs.trans_le hsourceTime.1,
              hsourceTime.2.trans_lt ht⟩) k +
        -heatTransportedH2SourceCurlCoefficient nu (t - sourceTime)
          (sharpNonlinearSource
            (openVelocityWeightedH3State solution
              ⟨t, hs.trans_le hst, ht⟩)) k := by
  rw [compactStokesTransportedVorticityNonlinearMode_eq_sharpClockedCurl
    solution hs hst ht k hsourceTime]
  rw [heatTransportedOpenSharpSource_eq_increment_add_frozen
    solution ⟨t, hs.trans_le hst, ht⟩
      ⟨sourceTime, hs.trans_le hsourceTime.1, hsourceTime.2.trans_lt ht⟩
      (t - sourceTime) k]
  abel

/-! ## Audit -/

#print axioms heatTransportedH2SourceCoefficient_sub
#print axioms heatTransportedH2SourceCurlCoefficient_sub
#print axioms openSharpSourceElapsedIncrement_eq
#print axioms heatTransportedOpenSharpSource_eq_increment_add_frozen
#print axioms compactStokesTransportedVorticityNonlinearMode_eq_reflected_add_frozen

end Soma.Holonics.Millennium.NavierStokesCriticalTimeReflection
