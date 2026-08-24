import ElementaryHolonics.Millennium.NavierStokesCriticalContinuation
import ElementaryHolonics.Millennium.NavierStokesSmoothSliceWeightedH3
import ElementaryHolonics.Millennium.NavierStokesWeightedRestartAperture

/-!
# The coordinate receiver supplies one native restart cap

**[proved-derived]** The differentiated coordinate receiver and the complete Fourier restart
carrier are now connected without a postulated norm equivalence.  Parseval has already returned

`‖u(t)‖²_native ≤ 240 * coordinateLogH3Receiver(t)`.

Consequently one uniform bound on that coordinate receiver supplies one explicit native norm cap,
one radius, and one strictly positive viscous time aperture shared by every interior restart face.
This is the exact familywise passage required by `RestartSupplyFromUniformHighOrderBound`; the
remaining work is to turn the native fixed point into a smooth real periodic PDE patch.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesCoordinateWeightedRestartCap

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalContinuation
open Soma.Holonics.Millennium.NavierStokesCoordinateH3FrequencyComb
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-- A convenient name for the actual native weighted Fourier occurrence at one interior face. -/
def interiorSliceWeightedH3
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht : t ∈ Ioo 0 T) : PeriodicVectorWeightedSobolev 3 :=
  smoothSliceVectorWeightedH3 (fun x ↦ velocity x t)
    (openPeriodicSolutionOn_velocitySlice_contDiff solution ht)
    (solution.velocityPeriodic t ⟨ht.1.le, ht.2⟩)

/-- A receiver bound is converted to a deliberately polynomial native norm cap.  The additive
one avoids a square-root chart and remains uniform even at zero native norm. -/
def coordinateWeightedRestartCap (bound : ℝ) : ℝ :=
  1 + 240 * bound

/-- Every actual tail slice lies below the cap returned from the uniform coordinate receiver. -/
theorem norm_interiorSliceWeightedH3_le_cap
    {T a nu bound : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a)
    (uniform : UniformOpenHighOrderBound T a
      (coordinateLogH3Receiver velocity) bound)
    {t : ℝ} (ht : t ∈ Ico a T) :
    ‖interiorSliceWeightedH3 solution ⟨ha.trans_le ht.1, ht.2⟩‖ ≤
      coordinateWeightedRestartCap bound := by
  let state := interiorSliceWeightedH3 solution ⟨ha.trans_le ht.1, ht.2⟩
  have hsquare :=
    openPeriodicSolutionOn_norm_sq_smoothSliceVectorWeightedH3_le_logReceiver
      solution ⟨ha.trans_le ht.1, ht.2⟩
  change ‖state‖ ^ 2 ≤ 240 * coordinateLogH3Receiver velocity t at hsquare
  have hreceiver : 240 * coordinateLogH3Receiver velocity t ≤ 240 * bound :=
    mul_le_mul_of_nonneg_left (uniform t ht) (by norm_num)
  have hsquareBound : ‖state‖ ^ 2 ≤ 240 * bound := hsquare.trans hreceiver
  have hself : ‖state‖ ≤ 1 + ‖state‖ ^ 2 := by
    nlinarith [sq_nonneg (‖state‖ - 1)]
  unfold coordinateWeightedRestartCap
  exact hself.trans (by linarith)

/-- The family cap is nonnegative whenever the controlled tail is nonempty. -/
theorem coordinateWeightedRestartCap_nonneg
    {T a nu bound : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (ha : 0 < a) (haT : a < T)
    (uniform : UniformOpenHighOrderBound T a
      (coordinateLogH3Receiver velocity) bound) :
    0 ≤ coordinateWeightedRestartCap bound := by
  let state := interiorSliceWeightedH3 solution ⟨ha, haT⟩
  have hstate := norm_interiorSliceWeightedH3_le_cap solution ha uniform
    (t := a) ⟨le_rfl, haT⟩
  exact (norm_nonneg state).trans hstate

/-- The one common radius inherited from the coordinate receiver. -/
def coordinateWeightedRestartRadius (bound : ℝ) : ℝ :=
  weightedRestartRadiusFromCap (coordinateWeightedRestartCap bound)

/-- The one common local time inherited from viscosity and the coordinate receiver. -/
def coordinateWeightedRestartTime (nu bound : ℝ) : ℝ :=
  weightedRestartTimeFromCap nu (coordinateWeightedRestartCap bound)

/-- Positive viscosity and a genuine uniform tail bound return a strictly positive common local
time for all of its interior slices. -/
theorem coordinateWeightedRestartTime_pos
    {T a nu bound : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (haT : a < T)
    (uniform : UniformOpenHighOrderBound T a
      (coordinateLogH3Receiver velocity) bound) :
    0 < coordinateWeightedRestartTime nu bound := by
  exact weightedRestartTimeFromCap_pos hnu
    (coordinateWeightedRestartCap_nonneg solution ha haT uniform)

/-- Every tail slice is controlled by the same native cap used to select the common time, retaining
the addressed slice occurrence rather than replacing it by the scalar receiver. -/
theorem tailSlice_nativeCap_and_commonTime
    {T a nu bound : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (hnu : 0 < nu) (ha : 0 < a) (haT : a < T)
    (uniform : UniformOpenHighOrderBound T a
      (coordinateLogH3Receiver velocity) bound) :
    (∀ (t : ℝ) (ht : t ∈ Ico a T),
      ‖interiorSliceWeightedH3 solution ⟨ha.trans_le ht.1, ht.2⟩‖ ≤
        coordinateWeightedRestartCap bound) ∧
      0 < coordinateWeightedRestartTime nu bound := by
  constructor
  · intro t ht
    exact norm_interiorSliceWeightedH3_le_cap solution ha uniform ht
  · exact coordinateWeightedRestartTime_pos solution hnu ha haT uniform

section Audit

#print axioms norm_interiorSliceWeightedH3_le_cap
#print axioms coordinateWeightedRestartCap_nonneg
#print axioms coordinateWeightedRestartTime_pos
#print axioms tailSlice_nativeCap_and_commonTime

end Audit

end Soma.Holonics.Millennium.NavierStokesCoordinateWeightedRestartCap
