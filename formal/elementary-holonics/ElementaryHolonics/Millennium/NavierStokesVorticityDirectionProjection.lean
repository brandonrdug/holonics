import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionCancellation

/-!
# Canonical projection onto the vorticity-direction remainder

**[proved-derived]** The finite Hodge-strain carrier permits subtraction of any component aligned
with the receiving vorticity.  This owner removes that choice: bilinear projection through the
receiver determines one exact amplitude and an orthogonal returned difference.  For the actual
solution carrier the receiver is the complexification of a real vorticity vector, so every nonzero
receiver has a nonzero self-pairing and the decomposition is available without an isotropic-complex
exception.
-/

noncomputable section

open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation

/-- The scalar component of a source along a declared receiver.  Division is totalized; the
nonzero-self-pairing theorem below opens the chart exactly where reconstruction requires it. -/
def receiverAlignedAmplitude (receiver source : ComplexVector) : ℂ :=
  complexDot receiver source / complexDot receiver receiver

/-- The source difference remaining after the receiver-aligned component is removed. -/
def receiverDirectionRemainder (receiver source : ComplexVector) : ComplexVector :=
  source - receiverAlignedAmplitude receiver source • receiver

/-- Bilinear dot transport through an aligned subtraction. -/
theorem complexDot_sub_smul
    (receiver source : ComplexVector) (amplitude : ℂ) :
    complexDot receiver (source - amplitude • receiver) =
      complexDot receiver source - amplitude * complexDot receiver receiver := by
  simp [complexDot, dotProduct, Fin.sum_univ_succ]
  ring

/-- Every source is exactly the sum of its returned direction remainder and aligned component. -/
theorem receiverDirectionRemainder_add_aligned
    (receiver source : ComplexVector) :
    receiverDirectionRemainder receiver source +
        receiverAlignedAmplitude receiver source • receiver = source := by
  simp [receiverDirectionRemainder]

/-- The canonical remainder is bilinearly orthogonal to the receiver whenever the receiver chart
has nonzero self-pairing. -/
theorem complexDot_receiverDirectionRemainder_eq_zero
    {receiver source : ComplexVector} (hreceiver : complexDot receiver receiver ≠ 0) :
    complexDot receiver (receiverDirectionRemainder receiver source) = 0 := by
  rw [receiverDirectionRemainder, complexDot_sub_smul, receiverAlignedAmplitude,
    div_mul_cancel₀ _ hreceiver, sub_self]

/-- Orthogonality determines the aligned amplitude uniquely. -/
theorem receiverAlignedAmplitude_unique
    {receiver source : ComplexVector} (hreceiver : complexDot receiver receiver ≠ 0)
    {amplitude : ℂ}
    (horthogonal : complexDot receiver (source - amplitude • receiver) = 0) :
    amplitude = receiverAlignedAmplitude receiver source := by
  rw [complexDot_sub_smul] at horthogonal
  rw [receiverAlignedAmplitude, eq_div_iff hreceiver]
  exact (sub_eq_zero.mp horthogonal).symm

/-- The Hodge-strain occurrence factors through the canonical direction remainder. -/
theorem hodgeStrainModeReading_receiverDirectionRemainder
    (frequency : SpatialFrequency) (receiver source : ComplexVector) :
    hodgeStrainModeReading frequency receiver
        (receiverDirectionRemainder receiver source) =
      hodgeStrainModeReading frequency receiver source := by
  exact hodgeStrainModeReading_sub_aligned frequency receiver source
    (receiverAlignedAmplitude receiver source)

/-- Coordinatewise complexification of an actual real spatial vector. -/
def complexOfRealSpace (v : Space) : ComplexVector :=
  fun component ↦ (v component : ℂ)

/-- A nonzero real spatial vector has nonzero bilinear self-pairing after complexification. -/
theorem complexDot_complexOfRealSpace_self_ne_zero
    {v : Space} (hv : v ≠ 0) :
    complexDot (complexOfRealSpace v) (complexOfRealSpace v) ≠ 0 := by
  have hvfun : (fun component : Fin 3 ↦ v component) ≠ 0 := by
    intro h
    apply hv
    ext component
    exact congrFun h component
  obtain ⟨component, hcomponent⟩ := Function.ne_iff.mp hvfun
  have hsum : 0 < ∑ coordinate : Fin 3, (v coordinate : ℝ) ^ 2 := by
    refine Finset.sum_pos' (fun coordinate _ ↦ sq_nonneg (v coordinate : ℝ)) ?_
    exact ⟨component, Finset.mem_univ component, sq_pos_of_ne_zero hcomponent⟩
  have hcast : ((∑ coordinate : Fin 3, (v coordinate : ℝ) ^ 2 : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hsum.ne'
  simpa [complexDot, complexOfRealSpace, dotProduct, pow_two] using hcast

/-- The actual complex vorticity receiver is exactly the coordinatewise complexification of its
real source occurrence. -/
theorem openPeriodicComplexVorticityAt_eq_complexOfRealSpace
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) :
    openPeriodicComplexVorticityAt solution t q =
      complexOfRealSpace
        (vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q)) := by
  rfl

/-- At every point of nonzero actual vorticity, the canonical projection chart is open. -/
theorem openPeriodicComplexVorticityAt_self_ne_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus)
    (hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) ≠ 0) :
    complexDot (openPeriodicComplexVorticityAt solution t q)
      (openPeriodicComplexVorticityAt solution t q) ≠ 0 := by
  rw [openPeriodicComplexVorticityAt_eq_complexOfRealSpace]
  exact complexDot_complexOfRealSpace_self_ne_zero hvorticity

/-- Canonical direction remainder for one transported actual vorticity coefficient. -/
def openPeriodicProjectedDirectionRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (frequency : SpatialFrequency) : ComplexVector :=
  receiverDirectionRemainder (openPeriodicComplexVorticityAt solution t q)
    (openPeriodicTransportedVorticityMode solution t q frequency)

/-- The projected source plus its aligned face reconstructs the complete transported source. -/
theorem openPeriodicProjectedDirectionRemainder_add_aligned
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (frequency : SpatialFrequency) :
    openPeriodicProjectedDirectionRemainder solution t q frequency +
        receiverAlignedAmplitude (openPeriodicComplexVorticityAt solution t q)
            (openPeriodicTransportedVorticityMode solution t q frequency) •
          openPeriodicComplexVorticityAt solution t q =
      openPeriodicTransportedVorticityMode solution t q frequency := by
  exact receiverDirectionRemainder_add_aligned
    (openPeriodicComplexVorticityAt solution t q)
    (openPeriodicTransportedVorticityMode solution t q frequency)

/-- The actual projected direction remainder is orthogonal at every receiver occurrence.  At a
zero-vorticity point this is immediate; elsewhere the real carrier opens the projection chart. -/
theorem complexDot_openPeriodicProjectedDirectionRemainder_eq_zero
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (frequency : SpatialFrequency) :
    complexDot (openPeriodicComplexVorticityAt solution t q)
      (openPeriodicProjectedDirectionRemainder solution t q frequency) = 0 := by
  by_cases hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) = 0
  · have hreceiver : openPeriodicComplexVorticityAt solution t q = 0 := by
      rw [openPeriodicComplexVorticityAt_eq_complexOfRealSpace, hvorticity]
      rfl
    rw [hreceiver]
    simp [complexDot]
  · exact complexDot_receiverDirectionRemainder_eq_zero
      (openPeriodicComplexVorticityAt_self_ne_zero solution t q hvorticity)

/-- **[proved-derived; formal-checked]** The actual finite Hodge-strain reading factors through
the canonical projected direction remainder at every addressed source mode. -/
theorem openPeriodicFiniteHodgeStrainReading_eq_projectedDirectionRemainder
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Set.Ioo 0 T) (q : SpatialTorus) (modes : Finset SpatialFrequency) :
    finiteHodgeStrainReading modes (openPeriodicComplexVorticityAt solution t q)
        (openPeriodicProjectedDirectionRemainder solution t q) =
      openPeriodicFiniteHodgeStrainReading solution t q modes := by
  exact openPeriodicFiniteHodgeStrainReading_eq_directionRemainder
    solution t q modes
      (fun frequency ↦ receiverAlignedAmplitude
        (openPeriodicComplexVorticityAt solution t q)
        (openPeriodicTransportedVorticityMode solution t q frequency))

section Audit

#print axioms receiverDirectionRemainder_add_aligned
#print axioms complexDot_receiverDirectionRemainder_eq_zero
#print axioms receiverAlignedAmplitude_unique
#print axioms hodgeStrainModeReading_receiverDirectionRemainder
#print axioms complexDot_complexOfRealSpace_self_ne_zero
#print axioms openPeriodicComplexVorticityAt_self_ne_zero
#print axioms openPeriodicProjectedDirectionRemainder_add_aligned
#print axioms complexDot_openPeriodicProjectedDirectionRemainder_eq_zero
#print axioms openPeriodicFiniteHodgeStrainReading_eq_projectedDirectionRemainder

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
