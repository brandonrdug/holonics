import ElementaryHolonics.Millennium.NavierStokesParabolicRebase
import ElementaryHolonics.Millennium.NavierStokesScaling

/-!
# Scaling audit for the critical mild terminal service

**[proved-derived; formal-checked]**  The sharp transported-source estimate has clock kernel
order `1 / 4`.  Integrating its target-time occurrence leaves a remaining-time moment of order
`3 / 4`.  This file records the exact parabolic weights of that returned moment.

In three spatial dimensions the quadratic `H3` terminal service has weight `3 / 2`, whereas the
time integral of the vorticity supremum has weight zero.  The unconditional kinetic-energy and
velocity-dissipation current has weight `-1`.  Thus the new heat estimate is a genuine sufficient
service route, but it is not itself a scale-critical closure of the energy current.

The final separator is only a receiver-scaling counterexample.  It does not assert blow-up or
produce a Navier--Stokes solution.  It rules out a scale-independent factorization of a positive
weight-`3 / 2` service face through one weight-`-1` energy/dissipation face.
-/

noncomputable section

namespace Soma.Holonics.Millennium.NavierStokesCriticalMildServiceScaling

open Soma.Holonics.Millennium.NavierStokesScaling

/-! ## Exact rational weight ledger -/

/-- The parabolic weight contributed by one time integration. -/
def timeIntegrationWeight : ℚ := -2

/-- The squared homogeneous Sobolev receiver carries twice the norm weight. -/
def squaredSobolevWeight (dimension order : ℚ) : ℚ :=
  2 * sobolevWeight dimension order

/-- Integrating an elapsed kernel of order `singularity` leaves a time moment of order
`1 - singularity`; the parabolic time chart gives that moment weight `-2(1-singularity)`. -/
def integratedElapsedMomentWeight (singularity : ℚ) : ℚ :=
  -2 * (1 - singularity)

/-- Weight of the terminal quadratic Sobolev service after source time and the integrated
elapsed-clock moment have both been retained. -/
def quadraticMildTerminalServiceWeight
    (dimension order singularity : ℚ) : ℚ :=
  squaredSobolevWeight dimension order + timeIntegrationWeight +
    integratedElapsedMomentWeight singularity

/-- Vorticity has one velocity-amplitude copy and one spatial derivative copy. -/
def vorticitySupremumWeight : ℚ := 2

/-- Weight of the scale-critical terminal vorticity integral. -/
def criticalVorticityTerminalWeight : ℚ :=
  vorticitySupremumWeight + timeIntegrationWeight

/-- Weight of the integrated squared `H1` velocity current returned by the energy law. -/
def integratedVelocityDissipationWeight (dimension : ℚ) : ℚ :=
  squaredSobolevWeight dimension 1 + timeIntegrationWeight

/-- The clock exponent, service weight, critical target, and energy current are exactly
`3/4`, `3/2`, `0`, and `-1` in dimension three. -/
theorem criticalMildTerminalService_weight_ledger :
    1 - (1 / 4 : ℚ) = 3 / 4 ∧
      quadraticMildTerminalServiceWeight 3 3 (1 / 4) = 3 / 2 ∧
      criticalVorticityTerminalWeight = 0 ∧
      integratedVelocityDissipationWeight 3 = -1 := by
  norm_num [quadraticMildTerminalServiceWeight, squaredSobolevWeight,
    integratedElapsedMomentWeight, timeIntegrationWeight,
    criticalVorticityTerminalWeight, vorticitySupremumWeight,
    integratedVelocityDissipationWeight, sobolevWeight]

/-- The quadratic `H3` clock service is strictly supercritical relative to the critical
vorticity terminal receiver. -/
theorem quadraticH3ClockService_not_critical :
    quadraticMildTerminalServiceWeight 3 3 (1 / 4) ≠
      criticalVorticityTerminalWeight := by
  norm_num [quadraticMildTerminalServiceWeight, squaredSobolevWeight,
    integratedElapsedMomentWeight, timeIntegrationWeight,
    criticalVorticityTerminalWeight, vorticitySupremumWeight, sobolevWeight]

/-- The quadratic `H3` clock service is also not carried by the unconditional integrated
velocity-dissipation weight. -/
theorem quadraticH3ClockService_not_energyDissipationWeight :
    quadraticMildTerminalServiceWeight 3 3 (1 / 4) ≠
      integratedVelocityDissipationWeight 3 := by
  norm_num [quadraticMildTerminalServiceWeight, squaredSobolevWeight,
    integratedElapsedMomentWeight, timeIntegrationWeight,
    integratedVelocityDissipationWeight, sobolevWeight]

/-! ## The exact Sobolev endpoint obstruction -/

/-- If the velocity is measured at homogeneous Sobolev order `s`, the divergence-form
nonlinearity loses one derivative and the vorticity curl loses another.  Three-dimensional
coefficient reconstruction costs a further `3/2` derivatives.  The heat clock therefore has
singularity `(7/2 - s)/2 = 7/4 - s/2`. -/
def heatCurlKernelSingularityFromSobolev (order : ℚ) : ℚ :=
  7 / 4 - order / 2

/-- After integrating the target-time occurrence, the corresponding remaining-time moment has
order `s/2 - 3/4`. -/
def integratedHeatCurlMomentFromSobolev (order : ℚ) : ℚ :=
  1 - heatCurlKernelSingularityFromSobolev order

theorem integratedHeatCurlMomentFromSobolev_eq (order : ℚ) :
    integratedHeatCurlMomentFromSobolev order = order / 2 - 3 / 4 := by
  simp [integratedHeatCurlMomentFromSobolev,
    heatCurlKernelSingularityFromSobolev]
  ring

/-- The terminal quadratic Sobolev service produced by this entire heat-clock family has exact
weight `s - 3/2` in dimension three. -/
theorem quadraticSobolevHeatCurlTerminalServiceWeight_eq (order : ℚ) :
    quadraticMildTerminalServiceWeight 3 order
        (heatCurlKernelSingularityFromSobolev order) =
      order - 3 / 2 := by
  simp [quadraticMildTerminalServiceWeight, squaredSobolevWeight,
    integratedElapsedMomentWeight, heatCurlKernelSingularityFromSobolev,
    timeIntegrationWeight, sobolevWeight]
  ring

/-- The heat clock is locally time-integrable exactly above the critical Sobolev order `3/2`. -/
theorem heatCurlKernelSingularity_lt_one_iff (order : ℚ) :
    heatCurlKernelSingularityFromSobolev order < 1 ↔ 3 / 2 < order := by
  simp [heatCurlKernelSingularityFromSobolev]
  constructor <;> intro h <;> linarith

/-- The quadratic terminal service is scale-critical exactly at Sobolev order `3/2`. -/
theorem quadraticSobolevHeatCurlTerminalServiceWeight_eq_zero_iff (order : ℚ) :
    quadraticMildTerminalServiceWeight 3 order
        (heatCurlKernelSingularityFromSobolev order) = 0 ↔
      order = 3 / 2 := by
  rw [quadraticSobolevHeatCurlTerminalServiceWeight_eq]
  constructor <;> intro h <;> linarith

/-- At the unique scale-critical Sobolev order the heat-clock kernel is exactly the nonintegrable
endpoint order one. -/
theorem criticalSobolevHeatCurlKernel_is_endpoint :
    heatCurlKernelSingularityFromSobolev (3 / 2) = 1 := by
  norm_num [heatCurlKernelSingularityFromSobolev]

/-- The unconditional velocity `H1` current reaches this direct heat family only with kernel
order `5/4`, already beyond the locally integrable endpoint. -/
theorem energyH1HeatCurlKernel_is_superendpoint :
    heatCurlKernelSingularityFromSobolev 1 = 5 / 4 := by
  norm_num [heatCurlKernelSingularityFromSobolev]

theorem energyH1HeatCurlKernel_not_locallyIntegrableOrder :
    ¬ heatCurlKernelSingularityFromSobolev 1 < 1 := by
  rw [energyH1HeatCurlKernel_is_superendpoint]
  norm_num

/-- No member of the direct absolute-coefficient Sobolev heat family is both scale-critical and
locally time-integrable.  A successful critical route must retain cancellation or replace the
endpoint by a genuinely finer Besov/Lorentz/Carleson receiver before taking absolute mass. -/
theorem no_critical_locallyIntegrable_directSobolevHeatService :
    ¬ ∃ order : ℚ,
      heatCurlKernelSingularityFromSobolev order < 1 ∧
      quadraticMildTerminalServiceWeight 3 order
          (heatCurlKernelSingularityFromSobolev order) = 0 := by
  rintro ⟨order, hkernel, hcritical⟩
  have hgt : 3 / 2 < order :=
    (heatCurlKernelSingularity_lt_one_iff order).mp hkernel
  have heq : order = 3 / 2 :=
    (quadraticSobolevHeatCurlTerminalServiceWeight_eq_zero_iff order).mp hcritical
  linarith

/-! ## Energy interpolation misses the Serrin line -/

/-- Reciprocal time exponent on the interpolation segment from `L∞_t L2_x` to
`L2_t L6_x`. -/
def energyInterpolationTimeReciprocal (mix : ℚ) : ℚ := mix / 2

/-- Reciprocal spatial exponent on the same energy interpolation segment. -/
def energyInterpolationSpaceReciprocal (mix : ℚ) : ℚ :=
  (1 - mix) / 2 + mix / 6

/-- The Serrin index written directly in reciprocal coordinates.  Critical velocity service has
index one. -/
def serrinReciprocalIndex (timeReciprocal spaceReciprocal : ℚ) : ℚ :=
  2 * timeReciprocal + 3 * spaceReciprocal

/-- Every interpolation of the unconditional energy endpoints remains on index `3/2`, not on
the critical Serrin index one.  In particular, the familiar `L4_t L3_x` interpolation point does
not supply a critical velocity service. -/
theorem energyInterpolation_serrinIndex (mix : ℚ) :
    serrinReciprocalIndex (energyInterpolationTimeReciprocal mix)
      (energyInterpolationSpaceReciprocal mix) = 3 / 2 := by
  simp [serrinReciprocalIndex, energyInterpolationTimeReciprocal,
    energyInterpolationSpaceReciprocal]
  ring

theorem energyInterpolation_ne_criticalSerrin (mix : ℚ) :
    serrinReciprocalIndex (energyInterpolationTimeReciprocal mix)
      (energyInterpolationSpaceReciprocal mix) ≠ 1 := by
  rw [energyInterpolation_serrinIndex]
  norm_num

/-- The midpoint of the energy interpolation segment is precisely the reciprocal-exponent chart
of `L4_t L3_x`, but its Serrin index is `3/2`. -/
theorem energyInterpolation_midpoint_is_L4L3_supercritical :
    energyInterpolationTimeReciprocal (1 / 2) = 1 / 4 ∧
      energyInterpolationSpaceReciprocal (1 / 2) = 1 / 3 ∧
      serrinReciprocalIndex
        (energyInterpolationTimeReciprocal (1 / 2))
        (energyInterpolationSpaceReciprocal (1 / 2)) = 3 / 2 := by
  norm_num [energyInterpolationTimeReciprocal,
    energyInterpolationSpaceReciprocal, serrinReciprocalIndex]

/-! ## Firing scale separator -/

/-- A positive terminal service face and a nonnegative energy/dissipation face at one reference
scale.  Under the square-root scale coordinate `r` (so the PDE scale is `r^2`), weights `3/2`
and `-1` become the integer powers `r^3` and `r^-2`. -/
structure TerminalServiceScalingProfile where
  service : ℝ
  energyDissipation : ℝ
  service_pos : 0 < service
  energyDissipation_nonneg : 0 ≤ energyDissipation

/-- Rebased positive-weight terminal service face. -/
def TerminalServiceScalingProfile.serviceFace
    (profile : TerminalServiceScalingProfile) (rootScale : ℝ) : ℝ :=
  rootScale ^ 3 * profile.service

/-- Rebased subcritical energy/dissipation face. -/
def TerminalServiceScalingProfile.energyDissipationFace
    (profile : TerminalServiceScalingProfile) (rootScale : ℝ) : ℝ :=
  (rootScale ^ 2)⁻¹ * profile.energyDissipation

/-- Every proposed scale-independent coefficient is separated by one positive rebase.  Therefore
the unconditional weight-`-1` current cannot, by scaling alone, dominate the positive-weight
terminal service required by the present quadratic `H3` heat route. -/
theorem TerminalServiceScalingProfile.exists_rootScale_separating_energyDissipation
    (profile : TerminalServiceScalingProfile) (coefficient : ℝ) :
    ∃ rootScale : ℝ, 0 < rootScale ∧
      coefficient * profile.energyDissipationFace rootScale <
        profile.serviceFace rootScale := by
  let cost : ℝ := |coefficient| * profile.energyDissipation
  let rootScale : ℝ := (cost + profile.service) / profile.service
  have hcost : 0 ≤ cost := by
    exact mul_nonneg (abs_nonneg coefficient) profile.energyDissipation_nonneg
  have hroot : 0 < rootScale := by
    dsimp [rootScale]
    exact div_pos (add_pos_of_nonneg_of_pos hcost profile.service_pos)
      profile.service_pos
  have hrootOne : 1 ≤ rootScale := by
    rw [le_div_iff₀ profile.service_pos]
    dsimp [cost]
    linarith
  have hinvSqLeOne : (rootScale ^ 2)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (sq_pos_of_pos hroot)]
    nlinarith
  have hcoefficient : coefficient ≤ |coefficient| := le_abs_self coefficient
  have hleft :
      coefficient * profile.energyDissipationFace rootScale ≤ cost := by
    unfold TerminalServiceScalingProfile.energyDissipationFace
    calc
      coefficient * ((rootScale ^ 2)⁻¹ * profile.energyDissipation) =
          (coefficient * profile.energyDissipation) * (rootScale ^ 2)⁻¹ := by ring
      _ ≤ (|coefficient| * profile.energyDissipation) * (rootScale ^ 2)⁻¹ := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoefficient profile.energyDissipation_nonneg)
          (inv_nonneg.mpr (sq_nonneg rootScale))
      _ ≤ |coefficient| * profile.energyDissipation := by
        exact mul_le_of_le_one_right hcost hinvSqLeOne
      _ = cost := rfl
  have hrootIdentity : rootScale * profile.service = cost + profile.service := by
    dsimp [rootScale]
    field_simp [profile.service_pos.ne']
  have hcostLtLinear : cost < rootScale * profile.service := by
    rw [hrootIdentity]
    exact lt_add_of_pos_right cost profile.service_pos
  have hlinearLeCubic :
      rootScale * profile.service ≤ rootScale ^ 3 * profile.service := by
    have hrootLeCube : rootScale ≤ rootScale ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hrootOne)
        (mul_nonneg hroot.le (add_nonneg hroot.le (by norm_num : (0 : ℝ) ≤ 1)))]
    exact mul_le_mul_of_nonneg_right hrootLeCube profile.service_pos.le
  exact ⟨rootScale, hroot,
    hleft.trans_lt (hcostLtLinear.trans_le hlinearLeCubic)⟩

section Audit

#print axioms criticalMildTerminalService_weight_ledger
#print axioms quadraticH3ClockService_not_critical
#print axioms quadraticH3ClockService_not_energyDissipationWeight
#print axioms integratedHeatCurlMomentFromSobolev_eq
#print axioms quadraticSobolevHeatCurlTerminalServiceWeight_eq
#print axioms heatCurlKernelSingularity_lt_one_iff
#print axioms quadraticSobolevHeatCurlTerminalServiceWeight_eq_zero_iff
#print axioms criticalSobolevHeatCurlKernel_is_endpoint
#print axioms energyH1HeatCurlKernel_is_superendpoint
#print axioms energyH1HeatCurlKernel_not_locallyIntegrableOrder
#print axioms no_critical_locallyIntegrable_directSobolevHeatService
#print axioms energyInterpolation_serrinIndex
#print axioms energyInterpolation_ne_criticalSerrin
#print axioms energyInterpolation_midpoint_is_L4L3_supercritical
#print axioms TerminalServiceScalingProfile.exists_rootScale_separating_energyDissipation

end Audit

end Soma.Holonics.Millennium.NavierStokesCriticalMildServiceScaling
