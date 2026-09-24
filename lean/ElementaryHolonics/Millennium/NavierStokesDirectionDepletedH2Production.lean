import ElementaryHolonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
import ElementaryHolonics.Millennium.NavierStokesDirectionDepletionModulus

/-!
# Direction decomposition of the actual H2 nonlinear production

**[proved-derived; formal-checked]** The adaptive reciprocal heat clock exposes the complete
`H2` nonlinear vorticity source before any signed stretching receiver is taken.  This file splits
each actual source mode through the contemporaneous vorticity direction at an addressed spatial
receiver.  The aligned amplitude and the receiver-orthogonal phase fibre reconstruct the exact
sharp-source curl coefficient; the phase fibre is orthogonal and, away from zero vorticity, is
reconstructed losslessly by the double-cross seam.

The finite dyadic source mass is therefore bounded by the sum of its aligned population and its
orthogonal phase population.  The latter receives its own reciprocal-clock time current.  A
formal separator proves that the standing spatial direction-coherence hypothesis alone cannot
control this source-phase current: a perfectly coherent constant receiving direction can still
meet a nonzero orthogonal source coefficient.  A terminal estimate consequently needs a
constitutive law coupling the actual `H2` source to this phase-time current; no such law is assumed
or asserted here.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesDirectionDepletedH2Production

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearTriangleService
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeBandPositivity
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicSpectralClockService
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedPath
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesParabolicDirectionCurrent
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
open Soma.Holonics.Millennium.NavierStokesSmoothMildSourceChronology
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionBaseEnergy
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCancellation
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound

set_option maxHeartbeats 2400000

/-! ## The actual compact source occurrence and its polar receiver -/

/-- The contemporaneous actual vorticity direction used to read one compact nonlinear source
mode.  Compact clamping is part of the source chart and becomes the identity on the addressed
interval. -/
def compactH2ProductionDirectionReceiver
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (sourceTime : ℝ) : ComplexVector :=
  openPeriodicComplexVorticityAt solution
    (compactInteriorTime ha hab hbT sourceTime) q

/-- The scalar amplitude of one actual nonlinear vorticity-source mode along the receiving
vorticity direction. -/
def compactH2ProductionAlignedAmplitude
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ) : ℂ :=
  receiverAlignedAmplitude
    (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
    (compactVorticityNonlinearMode solution ha hab hbT frequency sourceTime)

/-- The complete aligned vector occurrence, retained separately from its scalar amplitude. -/
def compactH2ProductionAlignedMode
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ) : ComplexVector :=
  compactH2ProductionAlignedAmplitude solution ha hab hbT q frequency sourceTime •
    compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime

/-- The receiver-orthogonal phase/holonomy fibre of one actual nonlinear source mode. -/
def compactH2ProductionPhaseRemainderMode
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ) : ComplexVector :=
  receiverDirectionRemainder
    (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
    (compactVorticityNonlinearMode solution ha hab hbT frequency sourceTime)

/-- The aligned occurrence and phase fibre reconstruct the complete actual source mode. -/
theorem compactH2ProductionPhaseRemainder_add_aligned
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ) :
    compactH2ProductionPhaseRemainderMode
        solution ha hab hbT q frequency sourceTime +
      compactH2ProductionAlignedMode
        solution ha hab hbT q frequency sourceTime =
      compactVorticityNonlinearMode
        solution ha hab hbT frequency sourceTime := by
  exact receiverDirectionRemainder_add_aligned
    (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
    (compactVorticityNonlinearMode solution ha hab hbT frequency sourceTime)

/-- On the addressed source-time interval the polar reconstruction is literally the curl of the
native sharp `H2` source.  Thus the split is on the PDE coefficient feeding the `H3` heat edge,
not on a proxy population. -/
theorem compactH2ProductionPhaseRemainder_add_aligned_eq_sharpSourceCurl
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency)
    (hsourceTime : sourceTime ∈ Icc a b) :
    compactH2ProductionPhaseRemainderMode
        solution ha hab hbT q frequency sourceTime +
      compactH2ProductionAlignedMode
        solution ha hab hbT q frequency sourceTime =
      -heatTransportedH2SourceCurlCoefficient 1 0
        (sharpNonlinearSource
          (openVelocityWeightedH3State solution
            ⟨sourceTime, ha.trans_le hsourceTime.1,
              hsourceTime.2.trans_lt hbT⟩)) frequency := by
  rw [compactH2ProductionPhaseRemainder_add_aligned]
  exact compactVorticityNonlinearMode_eq_neg_unclockedSharpSourceCurl
    solution ha hab hbT frequency hsourceTime

/-- The phase fibre is bilinearly orthogonal to the contemporaneous actual vorticity receiver,
including the zero-vorticity chart. -/
theorem complexDot_compactH2ProductionPhaseRemainder_eq_zero
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ) :
    complexDot
        (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
        (compactH2ProductionPhaseRemainderMode
          solution ha hab hbT q frequency sourceTime) = 0 := by
  let t := compactInteriorTime ha hab hbT sourceTime
  by_cases hvorticity :
      vorticityAt (fun x ↦ velocity x t.1) (euclideanRepresentative q) = 0
  · have hreceiver :
        compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime = 0 := by
      unfold compactH2ProductionDirectionReceiver
      rw [openPeriodicComplexVorticityAt_eq_complexOfRealSpace, hvorticity]
      rfl
    rw [hreceiver]
    simp [complexDot]
  · exact complexDot_receiverDirectionRemainder_eq_zero
      (by
        simpa only [compactH2ProductionDirectionReceiver] using
          (openPeriodicComplexVorticityAt_self_ne_zero solution t q hvorticity))

/-- Away from zero vorticity, the oriented double-cross seam reconstructs the complete phase
fibre.  The inverse self-pairing is the exact local receiver aperture. -/
theorem compactH2ProductionPhaseRemainder_eq_doubleCross
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ)
    (hvorticity :
      vorticityAt
        (fun x ↦ velocity x (compactInteriorTime ha hab hbT sourceTime).1)
        (euclideanRepresentative q) ≠ 0) :
    compactH2ProductionPhaseRemainderMode
        solution ha hab hbT q frequency sourceTime =
      (complexDot
        (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
        (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime))⁻¹ •
        complexCross
          (receiverCrossDifference
            (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
            (compactVorticityNonlinearMode
              solution ha hab hbT frequency sourceTime))
          (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime) := by
  exact receiverDirectionRemainder_eq_inv_smul_crossDifference_cross
    (by
      simpa only [compactH2ProductionDirectionReceiver] using
        (openPeriodicComplexVorticityAt_self_ne_zero solution
          (compactInteriorTime ha hab hbT sourceTime) q hvorticity))

/-! ## Finite scale mass and the missing clocked phase current -/

/-- Absolute aligned population on the actual adjacent-shell source word. -/
def compactDyadicH2ProductionAlignedMassAt
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (scale : ℕ) (sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈ dyadicNonlinearSourceModes scale,
    |dyadicHodgeBandWeight scale frequency| *
      ‖compactH2ProductionAlignedMode
        solution ha hab hbT q frequency sourceTime‖

/-- Absolute population of the exact receiver-orthogonal reconstruction fibre. -/
def compactDyadicH2ProductionPhaseFibreMassAt
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (scale : ℕ) (sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈ dyadicNonlinearSourceModes scale,
    |dyadicHodgeBandWeight scale frequency| *
      ‖compactH2ProductionPhaseRemainderMode
        solution ha hab hbT q frequency sourceTime‖

/-- The oriented source seam before the double-cross reconstruction.  Unlike a scalar stretching
reading, this receiver preserves the complete orthogonal direction whenever the receiving
vorticity is nonzero. -/
def compactDyadicH2ProductionCrossSeamMassAt
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (scale : ℕ) (sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈ dyadicNonlinearSourceModes scale,
    |dyadicHodgeBandWeight scale frequency| *
      complexVectorL1
        (receiverCrossDifference
          (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
          (compactVorticityNonlinearMode
            solution ha hab hbT frequency sourceTime))

theorem compactDyadicH2ProductionAlignedMassAt_nonneg
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (scale : ℕ) (sourceTime : ℝ) :
    0 ≤ compactDyadicH2ProductionAlignedMassAt
      solution ha hab hbT q scale sourceTime := by
  exact Finset.sum_nonneg fun frequency _hfrequency ↦
    mul_nonneg (abs_nonneg _) (norm_nonneg _)

theorem compactDyadicH2ProductionPhaseFibreMassAt_nonneg
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (scale : ℕ) (sourceTime : ℝ) :
    0 ≤ compactDyadicH2ProductionPhaseFibreMassAt
      solution ha hab hbT q scale sourceTime := by
  exact Finset.sum_nonneg fun frequency _hfrequency ↦
    mul_nonneg (abs_nonneg _) (norm_nonneg _)

theorem compactDyadicH2ProductionCrossSeamMassAt_nonneg
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (scale : ℕ) (sourceTime : ℝ) :
    0 ≤ compactDyadicH2ProductionCrossSeamMassAt
      solution ha hab hbT q scale sourceTime := by
  exact Finset.sum_nonneg fun frequency _hfrequency ↦
    mul_nonneg (abs_nonneg _) (complexVectorL1_nonneg _)

/-- On a nonzero actual-vorticity chart, the cross seam pays the whole orthogonal source fibre
with the exact inverse receiver aperture.  The zero-vorticity chart is deliberately excluded:
there the cross seam vanishes while the source fibre can remain nonzero. -/
theorem compactDyadicH2ProductionPhaseFibreMassAt_le_crossSeam
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (scale : ℕ) (sourceTime : ℝ)
    (hvorticity :
      vorticityAt
        (fun x ↦ velocity x (compactInteriorTime ha hab hbT sourceTime).1)
        (euclideanRepresentative q) ≠ 0) :
    compactDyadicH2ProductionPhaseFibreMassAt
        solution ha hab hbT q scale sourceTime ≤
      (‖(complexDot
          (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
          (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime))⁻¹‖ *
        complexVectorL1
          (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)) *
        compactDyadicH2ProductionCrossSeamMassAt
          solution ha hab hbT q scale sourceTime := by
  let receiver :=
    compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime
  let source :=
    fun frequency ↦ compactVorticityNonlinearMode
      solution ha hab hbT frequency sourceTime
  let aperture := ‖(complexDot receiver receiver)⁻¹‖ * complexVectorL1 receiver
  have hreceiver : complexDot receiver receiver ≠ 0 := by
    dsimp only [receiver, compactH2ProductionDirectionReceiver]
    exact openPeriodicComplexVorticityAt_self_ne_zero solution
      (compactInteriorTime ha hab hbT sourceTime) q hvorticity
  unfold compactDyadicH2ProductionPhaseFibreMassAt
    compactDyadicH2ProductionCrossSeamMassAt
  change
    (∑ frequency ∈ dyadicNonlinearSourceModes scale,
      |dyadicHodgeBandWeight scale frequency| *
        ‖receiverDirectionRemainder receiver (source frequency)‖) ≤
      aperture *
        ∑ frequency ∈ dyadicNonlinearSourceModes scale,
          |dyadicHodgeBandWeight scale frequency| *
            complexVectorL1 (receiverCrossDifference receiver (source frequency))
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro frequency _hfrequency
  have hremainder :=
    complexVectorL1_receiverDirectionRemainder_le_crossDifference hreceiver
      (source := source frequency)
  calc
    |dyadicHodgeBandWeight scale frequency| *
        ‖receiverDirectionRemainder receiver (source frequency)‖ ≤
      |dyadicHodgeBandWeight scale frequency| *
        complexVectorL1 (receiverDirectionRemainder receiver (source frequency)) :=
      mul_le_mul_of_nonneg_left
        (norm_complexVector_le_complexVectorL1 _) (abs_nonneg _)
    _ ≤ |dyadicHodgeBandWeight scale frequency| *
        (‖(complexDot receiver receiver)⁻¹‖ *
          (complexVectorL1 (receiverCrossDifference receiver (source frequency)) *
            complexVectorL1 receiver)) :=
      mul_le_mul_of_nonneg_left hremainder (abs_nonneg _)
    _ = aperture *
        (|dyadicHodgeBandWeight scale frequency| *
          complexVectorL1 (receiverCrossDifference receiver (source frequency))) := by
      dsimp only [aperture]
      ring

/-- The actual absolute source population is paid exactly after retaining both polar faces.  This
is the strongest unconditional direction decomposition available from the standing owners. -/
theorem compactSmoothDyadicVorticityNonlinearSourceMassAt_le_aligned_add_phaseFibre
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (scale : ℕ) (sourceTime : ℝ) :
    compactSmoothDyadicVorticityNonlinearSourceMassAt
        solution ha hab hbT scale sourceTime ≤
      compactDyadicH2ProductionAlignedMassAt
          solution ha hab hbT q scale sourceTime +
        compactDyadicH2ProductionPhaseFibreMassAt
          solution ha hab hbT q scale sourceTime := by
  unfold compactSmoothDyadicVorticityNonlinearSourceMassAt
    compactDyadicH2ProductionAlignedMassAt
    compactDyadicH2ProductionPhaseFibreMassAt
    dyadicNonlinearSourceModes
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro frequency _hfrequency
  have hreconstruct := compactH2ProductionPhaseRemainder_add_aligned
    solution ha hab hbT q frequency sourceTime
  calc
    |dyadicHodgeBandWeight scale frequency| *
        ‖compactVorticityNonlinearMode
          solution ha hab hbT frequency sourceTime‖ =
      |dyadicHodgeBandWeight scale frequency| *
        ‖compactH2ProductionPhaseRemainderMode
            solution ha hab hbT q frequency sourceTime +
          compactH2ProductionAlignedMode
            solution ha hab hbT q frequency sourceTime‖ := by rw [hreconstruct]
    _ ≤ |dyadicHodgeBandWeight scale frequency| *
        (‖compactH2ProductionPhaseRemainderMode
            solution ha hab hbT q frequency sourceTime‖ +
          ‖compactH2ProductionAlignedMode
            solution ha hab hbT q frequency sourceTime‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (abs_nonneg _)
    _ = |dyadicHodgeBandWeight scale frequency| *
          ‖compactH2ProductionAlignedMode
            solution ha hab hbT q frequency sourceTime‖ +
        |dyadicHodgeBandWeight scale frequency| *
          ‖compactH2ProductionPhaseRemainderMode
            solution ha hab hbT q frequency sourceTime‖ := by ring

/-- The exact ENNReal reciprocal-clock current of the orthogonal source fibre.  It is total even
when the projection chart crosses zero vorticity, and is the missing time-sensitive receiver
which an endpoint direction-depletion theorem must control. -/
def compactDyadicH2ProductionPhaseClockCurrent
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (scale : ℕ) : ℝ≥0∞ :=
  ∫⁻ sourceTime in Icc a b,
    ENNReal.ofReal
      (dyadicParabolicClockBudget nu scale *
        compactDyadicH2ProductionPhaseFibreMassAt
          solution ha hab hbT q scale sourceTime)

/-- The oriented cross-seam time current.  On nonzero-vorticity charts it reconstructs the phase
current through the theorem above; a complete terminal law must additionally retain the fibre over
the zero-vorticity locus. -/
def compactDyadicH2ProductionCrossSeamClockCurrent
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (scale : ℕ) : ℝ≥0∞ :=
  ∫⁻ sourceTime in Icc a b,
    ENNReal.ofReal
      (dyadicParabolicClockBudget nu scale *
        compactDyadicH2ProductionCrossSeamMassAt
          solution ha hab hbT q scale sourceTime)

/-! ## Exact insufficiency of ordinary spatial direction coherence -/

/-- A constant real vorticity direction presenting the same unit receiver at every point. -/
def constantCoherentSeparatorField : Space → Space :=
  fun _ ↦ EuclideanSpace.basisFun (Fin 3) ℝ 0

theorem constantCoherentSeparatorField_hasLinearDirectionCoherence :
    HasLinearDirectionCoherence constantCoherentSeparatorField 0 := by
  intro x y
  have hzero : vectorOfCoordinates (![0, 0, 0] : Fin 3 → ℝ) = (0 : Space) := by
    ext component
    fin_cases component <;> simp [vectorOfCoordinates]
  simp [constantCoherentSeparatorField, normalizedDirectionSeam,
    normalizedDirection, cross, crossProduct, hzero]

theorem complexOfRealSpace_constantCoherentSeparatorField :
    complexOfRealSpace (constantCoherentSeparatorField 0) =
      orthogonalSeparatorReceiver := by
  ext component
  fin_cases component <;>
    simp [constantCoherentSeparatorField, complexOfRealSpace,
      orthogonalSeparatorReceiver, EuclideanSpace.basisFun_apply]

/-- **[counterexample; formal-checked]** No scalar multiple of the spatial direction-coherence
coefficient controls the orthogonal `H2` production coefficient.  The receiving field can have
perfect coherence (`K = 0`) while a nonzero source occurrence lies wholly in its phase fibre.
This names the missing constitutive input precisely: control of
`compactDyadicH2ProductionPhaseClockCurrent`, not another bound on the receiving direction alone. -/
theorem no_spatialDirectionCoherence_bound_for_H2ProductionPhaseFibre :
    ¬ ∃ constant : ℝ,
      ∀ (field : Space → Space) (K : ℝ) (source : ComplexVector),
        HasLinearDirectionCoherence field K →
          complexVectorL1
              (receiverDirectionRemainder
                (complexOfRealSpace (field 0)) source) ≤
            constant * K := by
  rintro ⟨constant, hbound⟩
  have hseparator := hbound constantCoherentSeparatorField 0
    orthogonalSeparatorOutput
    constantCoherentSeparatorField_hasLinearDirectionCoherence
  rw [complexOfRealSpace_constantCoherentSeparatorField,
    receiverDirectionRemainder_orthogonalSeparator,
    complexVectorL1_orthogonalSeparatorOutput] at hseparator
  norm_num at hseparator

section Audit

#print axioms compactH2ProductionPhaseRemainder_add_aligned
#print axioms compactH2ProductionPhaseRemainder_add_aligned_eq_sharpSourceCurl
#print axioms complexDot_compactH2ProductionPhaseRemainder_eq_zero
#print axioms compactH2ProductionPhaseRemainder_eq_doubleCross
#print axioms compactDyadicH2ProductionPhaseFibreMassAt_le_crossSeam
#print axioms compactSmoothDyadicVorticityNonlinearSourceMassAt_le_aligned_add_phaseFibre
#print axioms constantCoherentSeparatorField_hasLinearDirectionCoherence
#print axioms no_spatialDirectionCoherence_bound_for_H2ProductionPhaseFibre

end Audit

end Soma.Holonics.Millennium.NavierStokesDirectionDepletedH2Production
