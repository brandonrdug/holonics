import ElementaryHolonics.Millennium.NavierStokesDissipationHodgeEnstrophy

/-!
# The fourth-power receiver retains an amplitude direction

**[counterexample]** The spatial fourth-power vorticity population exposed by the absorbed Hodge
passage cannot be absorbed uniformly through faces which grow only quadratically or cubically
along the same positive amplitude ray.  The statement is source-specific: its three coefficients
are the actual fourth-power mass, vorticity dissipation, and kinetic-energy/enstrophy base of one
admitted periodic solution slice.

This does not refute Navier--Stokes regularity.  It refutes only the proposed receiver
factorization which deletes the amplitude direction before the quartic population is returned.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace Soma.Holonics.Millennium.NavierStokesVorticityFourthPowerAmplitude

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDissipationHodgeInteraction
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity

local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Exact amplitude faces -/

/-- The actual scalar-amplitude action on a velocity world-sheet. -/
def amplitudeScaledVelocity (amplitude : ℝ) (velocity : VelocityField) : VelocityField :=
  fun x t ↦ amplitude • velocity x t

/-- Curl commutes exactly with the scalar-amplitude action, including at amplitude zero. -/
theorem vorticityField_amplitudeScaledVelocity
    (amplitude : ℝ) (velocity : VelocityField) (x : Space) (t : ℝ) :
    vorticityField (amplitudeScaledVelocity amplitude velocity) x t =
      amplitude • vorticityField velocity x t := by
  unfold vorticityField vorticityAt velocityJacobianAt amplitudeScaledVelocity
  change derivativeCurlLinearMap
      (fderiv ℝ (amplitude • fun y ↦ velocity y t) x) =
    amplitude • derivativeCurlLinearMap (fderiv ℝ (fun y ↦ velocity y t) x)
  rw [congrFun (fderiv_const_smul_of_field amplitude) x]
  exact map_smul derivativeCurlLinearMap amplitude _

/-- Periodic kinetic energy is an exact quadratic amplitude face. -/
theorem periodicKineticEnergy_amplitudeScaledVelocity
    (amplitude : ℝ) (velocity : VelocityField) (t : ℝ) :
    periodicKineticEnergy (amplitudeScaledVelocity amplitude velocity) t =
      amplitude ^ 2 * periodicKineticEnergy velocity t := by
  unfold periodicKineticEnergy kineticEnergyDensity amplitudeScaledVelocity
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [norm_smul, Real.norm_eq_abs]
  nlinarith [sq_abs amplitude]

/-- Periodic enstrophy is an exact quadratic amplitude face. -/
theorem periodicEnstrophy_amplitudeScaledVelocity
    (amplitude : ℝ) (velocity : VelocityField) (t : ℝ) :
    periodicEnstrophy (amplitudeScaledVelocity amplitude velocity) t =
      amplitude ^ 2 * periodicEnstrophy velocity t := by
  unfold periodicEnstrophy
  have hfield :
      vorticityField (amplitudeScaledVelocity amplitude velocity) =
        amplitudeScaledVelocity amplitude (vorticityField velocity) := by
    funext x s
    exact vorticityField_amplitudeScaledVelocity amplitude velocity x s
  rw [hfield, periodicKineticEnergy_amplitudeScaledVelocity]

/-- Every component gradient of vorticity carries the same scalar amplitude. -/
theorem gradient_vorticityField_amplitudeScaledVelocity
    (amplitude : ℝ) (velocity : VelocityField) (x : Space) (t : ℝ)
    (component : Fin 3) :
    gradient
        (fun y ↦ vorticityField (amplitudeScaledVelocity amplitude velocity) y t component) x =
      amplitude • gradient (fun y ↦ vorticityField velocity y t component) x := by
  have hfunction :
      (fun y ↦ vorticityField (amplitudeScaledVelocity amplitude velocity) y t component) =
        amplitude • (fun y ↦ vorticityField velocity y t component) := by
    funext y
    exact congrArg (fun v : Space ↦ v component)
      (vorticityField_amplitudeScaledVelocity amplitude velocity y t)
  unfold gradient
  rw [hfunction, congrFun (fderiv_const_smul_of_field amplitude) x]
  exact map_smul (InnerProductSpace.toDual ℝ Space).symm amplitude _

/-- Physical vorticity dissipation is an exact quadratic amplitude face. -/
theorem periodicVorticityDissipation_amplitudeScaledVelocity
    (amplitude : ℝ) (velocity : VelocityField) (t : ℝ) :
    periodicVorticityDissipation (amplitudeScaledVelocity amplitude velocity) t =
      amplitude ^ 2 * periodicVorticityDissipation velocity t := by
  unfold periodicVorticityDissipation
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro component _hcomponent
  rw [gradient_vorticityField_amplitudeScaledVelocity,
    norm_smul, Real.norm_eq_abs]
  nlinarith [sq_abs amplitude]

/-- Kinetic energy is nonnegative at the totalized unit-cube receiver without any equation of
motion. -/
theorem periodicKineticEnergy_nonneg_receiver
    (velocity : VelocityField) (t : ℝ) :
    0 ≤ periodicKineticEnergy velocity t := by
  unfold periodicKineticEnergy kineticEnergyDensity
  exact integral_nonneg fun _ ↦ mul_nonneg (by norm_num) (sq_nonneg _)

/-- On a nonnegative amplitude ray, the kinetic-energy/enstrophy base carries exact cubic
homogeneity. -/
theorem energyEnstrophyBase_amplitudeScaledVelocity
    (amplitude : ℝ) (hamplitude : 0 ≤ amplitude)
    (velocity : VelocityField) (t : ℝ) :
    Real.sqrt
          (2 * periodicKineticEnergy (amplitudeScaledVelocity amplitude velocity) t) *
        periodicEnstrophy (amplitudeScaledVelocity amplitude velocity) t =
      amplitude ^ 3 *
        (Real.sqrt (2 * periodicKineticEnergy velocity t) *
          periodicEnstrophy velocity t) := by
  rw [periodicKineticEnergy_amplitudeScaledVelocity,
    periodicEnstrophy_amplitudeScaledVelocity]
  have henergy : 0 ≤ 2 * periodicKineticEnergy velocity t :=
    mul_nonneg (by norm_num) (periodicKineticEnergy_nonneg_receiver velocity t)
  have hsqrt :
      Real.sqrt (2 * (amplitude ^ 2 * periodicKineticEnergy velocity t)) =
        amplitude * Real.sqrt (2 * periodicKineticEnergy velocity t) := by
    rw [show 2 * (amplitude ^ 2 * periodicKineticEnergy velocity t) =
        (amplitude * Real.sqrt (2 * periodicKineticEnergy velocity t)) ^ 2 by
      rw [mul_pow, Real.sq_sqrt henergy]
      ring]
    exact Real.sqrt_sq (mul_nonneg hamplitude (Real.sqrt_nonneg _))
  rw [hsqrt]
  ring

/-- The literal fourth-power population of an actual vorticity slice after scalar amplitude
transport. -/
def amplitudeScaledVorticityFourthPowerMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (amplitude : ℝ) : ℝ :=
  ∫ q : SpatialTorus, ‖amplitude • torusVorticityEvolution solution t q‖ ^ 4

/-- The actual torus fourth-power population is an exact quartic amplitude face. -/
theorem amplitudeScaledVorticityFourthPowerMass_eq
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (amplitude : ℝ) :
    amplitudeScaledVorticityFourthPowerMass solution t amplitude =
      amplitude ^ 4 * openPeriodicVorticityFourthPowerMass solution t := by
  unfold amplitudeScaledVorticityFourthPowerMass openPeriodicVorticityFourthPowerMass
  rw [← integral_const_mul]
  have hfunctions :
      (fun q : SpatialTorus ↦ ‖amplitude • torusVorticityEvolution solution t q‖ ^ 4) =
        fun q ↦ amplitude ^ 4 * ‖torusVorticityEvolution solution t q‖ ^ 4 := by
    funext q
    rw [norm_smul, Real.norm_eq_abs]
    rw [mul_pow]
    congr 1
    nlinarith [sq_abs amplitude]
  rw [hfunctions]

/-- The three source populations left at the current signed enstrophy receiver. -/
structure VorticityAmplitudeProfile where
  fourthPower : ℝ
  dissipation : ℝ
  energyEnstrophy : ℝ
  fourthPower_pos : 0 < fourthPower
  dissipation_nonneg : 0 ≤ dissipation
  energyEnstrophy_nonneg : 0 ≤ energyEnstrophy

/-- The exact quartic population on one positive amplitude ray. -/
def VorticityAmplitudeProfile.quarticFace
    (profile : VorticityAmplitudeProfile) (amplitude : ℝ) : ℝ :=
  amplitude ^ 4 * profile.fourthPower

/-- The exact quadratic dissipation population on the same amplitude ray. -/
def VorticityAmplitudeProfile.quadraticFace
    (profile : VorticityAmplitudeProfile) (amplitude : ℝ) : ℝ :=
  amplitude ^ 2 * profile.dissipation

/-- The kinetic-energy/enstrophy base grows cubically on a nonnegative amplitude ray. -/
def VorticityAmplitudeProfile.cubicFace
    (profile : VorticityAmplitudeProfile) (amplitude : ℝ) : ℝ :=
  amplitude ^ 3 * profile.energyEnstrophy

/-- Every proposed pair of fixed quadratic/cubic coefficients is separated by one exact positive
amplitude occurrence. -/
theorem VorticityAmplitudeProfile.exists_amplitude_separating_quartic
    (profile : VorticityAmplitudeProfile) (quadraticCoefficient cubicCoefficient : ℝ) :
    ∃ amplitude : ℝ, 0 < amplitude ∧
      quadraticCoefficient * profile.quadraticFace amplitude +
          cubicCoefficient * profile.cubicFace amplitude <
        profile.quarticFace amplitude := by
  let cost : ℝ :=
    |quadraticCoefficient| * profile.dissipation +
      |cubicCoefficient| * profile.energyEnstrophy
  let amplitude : ℝ := (cost + profile.fourthPower) / profile.fourthPower
  have hcost : 0 ≤ cost := by
    dsimp [cost]
    exact add_nonneg
      (mul_nonneg (abs_nonneg _) profile.dissipation_nonneg)
      (mul_nonneg (abs_nonneg _) profile.energyEnstrophy_nonneg)
  have hamp : 0 < amplitude := by
    dsimp [amplitude]
    exact div_pos (add_pos_of_nonneg_of_pos hcost profile.fourthPower_pos)
      profile.fourthPower_pos
  have hampOne : 1 ≤ amplitude := by
    rw [le_div_iff₀ profile.fourthPower_pos]
    dsimp [cost]
    linarith
  have hampTwoNonneg : 0 ≤ amplitude ^ 2 := sq_nonneg amplitude
  have hampThreeNonneg : 0 ≤ amplitude ^ 3 := by positivity
  have hampTwoLeThree : amplitude ^ 2 ≤ amplitude ^ 3 := by
    nlinarith [sq_nonneg amplitude, mul_nonneg (sq_nonneg amplitude) (sub_nonneg.mpr hampOne)]
  have hquadraticCoefficient :
      quadraticCoefficient * profile.dissipation ≤
        |quadraticCoefficient| * profile.dissipation :=
    mul_le_mul_of_nonneg_right (le_abs_self quadraticCoefficient)
      profile.dissipation_nonneg
  have hcubicCoefficient :
      cubicCoefficient * profile.energyEnstrophy ≤
        |cubicCoefficient| * profile.energyEnstrophy :=
    mul_le_mul_of_nonneg_right (le_abs_self cubicCoefficient)
      profile.energyEnstrophy_nonneg
  have hquadratic :
      quadraticCoefficient * profile.quadraticFace amplitude ≤
        (|quadraticCoefficient| * profile.dissipation) * amplitude ^ 3 := by
    unfold VorticityAmplitudeProfile.quadraticFace
    calc
      quadraticCoefficient * (amplitude ^ 2 * profile.dissipation) =
          (quadraticCoefficient * profile.dissipation) * amplitude ^ 2 := by ring
      _ ≤ (|quadraticCoefficient| * profile.dissipation) * amplitude ^ 2 :=
        mul_le_mul_of_nonneg_right hquadraticCoefficient hampTwoNonneg
      _ ≤ (|quadraticCoefficient| * profile.dissipation) * amplitude ^ 3 :=
        mul_le_mul_of_nonneg_left hampTwoLeThree
          (mul_nonneg (abs_nonneg _) profile.dissipation_nonneg)
  have hcubic :
      cubicCoefficient * profile.cubicFace amplitude ≤
        (|cubicCoefficient| * profile.energyEnstrophy) * amplitude ^ 3 := by
    unfold VorticityAmplitudeProfile.cubicFace
    calc
      cubicCoefficient * (amplitude ^ 3 * profile.energyEnstrophy) =
          (cubicCoefficient * profile.energyEnstrophy) * amplitude ^ 3 := by ring
      _ ≤ (|cubicCoefficient| * profile.energyEnstrophy) * amplitude ^ 3 :=
        mul_le_mul_of_nonneg_right hcubicCoefficient hampThreeNonneg
  have hcostBound :
      quadraticCoefficient * profile.quadraticFace amplitude +
          cubicCoefficient * profile.cubicFace amplitude ≤
        cost * amplitude ^ 3 := by
    calc
      _ ≤ (|quadraticCoefficient| * profile.dissipation) * amplitude ^ 3 +
          (|cubicCoefficient| * profile.energyEnstrophy) * amplitude ^ 3 :=
        add_le_add hquadratic hcubic
      _ = cost * amplitude ^ 3 := by
        dsimp [cost]
        ring
  have hamplitudeIdentity :
      amplitude * profile.fourthPower = cost + profile.fourthPower := by
    dsimp [amplitude]
    field_simp [profile.fourthPower_pos.ne']
  have hstrict : cost * amplitude ^ 3 <
      profile.quarticFace amplitude := by
    unfold VorticityAmplitudeProfile.quarticFace
    rw [show amplitude ^ 4 * profile.fourthPower =
        (amplitude * profile.fourthPower) * amplitude ^ 3 by ring]
    rw [hamplitudeIdentity]
    have hpositive : 0 < profile.fourthPower * amplitude ^ 3 :=
      mul_pos profile.fourthPower_pos (by positivity)
    nlinarith
  exact ⟨amplitude, hamp, hcostBound.trans_lt hstrict⟩

/-- There is no amplitude-independent factorization of the quartic face through only the
quadratic dissipation and cubic energy/enstrophy faces. -/
theorem VorticityAmplitudeProfile.no_uniform_quadratic_cubic_absorption
    (profile : VorticityAmplitudeProfile) :
    ¬ ∃ quadraticCoefficient cubicCoefficient : ℝ,
      ∀ amplitude : ℝ, 0 ≤ amplitude →
        profile.quarticFace amplitude ≤
          quadraticCoefficient * profile.quadraticFace amplitude +
            cubicCoefficient * profile.cubicFace amplitude := by
  rintro ⟨quadraticCoefficient, cubicCoefficient, hbound⟩
  obtain ⟨amplitude, hamp, hseparates⟩ :=
    profile.exists_amplitude_separating_quartic
      quadraticCoefficient cubicCoefficient
  exact (not_lt_of_ge (hbound amplitude hamp.le)) hseparates

/-! ## Attachment to the actual open periodic source -/

/-- A nonzero fourth-power slice supplies the exact three-face amplitude profile exposed by the
absorbed Hodge enstrophy theorem. -/
def openPeriodicVorticityAmplitudeProfile
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T)
    (hfourth : 0 < openPeriodicVorticityFourthPowerMass solution t) :
    VorticityAmplitudeProfile where
  fourthPower := openPeriodicVorticityFourthPowerMass solution t
  dissipation := periodicVorticityDissipation velocity t.1
  energyEnstrophy :=
    Real.sqrt (2 * periodicKineticEnergy velocity t.1) *
      periodicEnstrophy velocity t.1
  fourthPower_pos := hfourth
  dissipation_nonneg :=
    periodicVorticityDissipation_nonneg_of_openPeriodicSolution solution t
  energyEnstrophy_nonneg := by
    exact mul_nonneg (Real.sqrt_nonneg _) (periodicEnstrophy_nonneg_receiver _ _)

/-- **[counterexample; formal-checked]** On every admitted slice with nonzero fourth-power
vorticity, fixed coefficients cannot absorb every positive amplitude rebase of the exact quartic
remainder using only the quadratic dissipation and cubic kinetic-energy/enstrophy base. -/
theorem no_uniform_absorption_of_openPeriodicVorticityFourthPowerMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T)
    (hfourth : 0 < openPeriodicVorticityFourthPowerMass solution t) :
    ¬ ∃ quadraticCoefficient cubicCoefficient : ℝ,
      ∀ amplitude : ℝ, 0 ≤ amplitude →
        amplitude ^ 4 * openPeriodicVorticityFourthPowerMass solution t ≤
          quadraticCoefficient *
              (amplitude ^ 2 * periodicVorticityDissipation velocity t.1) +
            cubicCoefficient *
              (amplitude ^ 3 *
                (Real.sqrt (2 * periodicKineticEnergy velocity t.1) *
                  periodicEnstrophy velocity t.1)) := by
  simpa [openPeriodicVorticityAmplitudeProfile,
    VorticityAmplitudeProfile.quarticFace,
    VorticityAmplitudeProfile.quadraticFace,
    VorticityAmplitudeProfile.cubicFace] using
    (openPeriodicVorticityAmplitudeProfile solution t hfourth).no_uniform_quadratic_cubic_absorption

/-- **[counterexample; formal-checked]** The failed factorization is literal on the physical
receiver faces: the quartic vorticity population, vorticity dissipation, kinetic energy, and
enstrophy are all evaluated after applying the same scalar-amplitude transport to the velocity
world-sheet.  Thus replacing their exact homogeneities by receiver names does not close the
deleted amplitude direction. -/
theorem no_uniform_absorption_along_amplitudeScaledVelocity
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T)
    (hfourth : 0 < openPeriodicVorticityFourthPowerMass solution t) :
    ¬ ∃ quadraticCoefficient cubicCoefficient : ℝ,
      ∀ amplitude : ℝ, 0 ≤ amplitude →
        amplitudeScaledVorticityFourthPowerMass solution t amplitude ≤
          quadraticCoefficient *
              periodicVorticityDissipation
                (amplitudeScaledVelocity amplitude velocity) t.1 +
            cubicCoefficient *
              (Real.sqrt
                    (2 * periodicKineticEnergy
                      (amplitudeScaledVelocity amplitude velocity) t.1) *
                periodicEnstrophy
                  (amplitudeScaledVelocity amplitude velocity) t.1) := by
  rintro ⟨quadraticCoefficient, cubicCoefficient, hbound⟩
  apply no_uniform_absorption_of_openPeriodicVorticityFourthPowerMass solution t hfourth
  refine ⟨quadraticCoefficient, cubicCoefficient, ?_⟩
  intro amplitude hamplitude
  have hscaled := hbound amplitude hamplitude
  rw [amplitudeScaledVorticityFourthPowerMass_eq,
    periodicVorticityDissipation_amplitudeScaledVelocity,
    energyEnstrophyBase_amplitudeScaledVelocity amplitude hamplitude] at hscaled
  exact hscaled

section Audit

#print axioms vorticityField_amplitudeScaledVelocity
#print axioms periodicKineticEnergy_amplitudeScaledVelocity
#print axioms periodicEnstrophy_amplitudeScaledVelocity
#print axioms periodicVorticityDissipation_amplitudeScaledVelocity
#print axioms energyEnstrophyBase_amplitudeScaledVelocity
#print axioms amplitudeScaledVorticityFourthPowerMass_eq
#print axioms VorticityAmplitudeProfile.exists_amplitude_separating_quartic
#print axioms VorticityAmplitudeProfile.no_uniform_quadratic_cubic_absorption
#print axioms no_uniform_absorption_of_openPeriodicVorticityFourthPowerMass
#print axioms no_uniform_absorption_along_amplitudeScaledVelocity

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityFourthPowerAmplitude
