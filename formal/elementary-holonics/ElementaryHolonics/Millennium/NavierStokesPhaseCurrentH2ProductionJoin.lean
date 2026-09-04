import ElementaryHolonics.Millennium.NavierStokesDirectionDepletedH2Production
import ElementaryHolonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation

/-!
# The source-phase time current and the missing H2 production chart

**[proved-derived; formal-checked]** The actual sharp-source curl has already been split at every
physical vorticity receiver into an aligned mode and its complete receiver-orthogonal phase fibre.
The signed `H2` production current, however, is a physical-space energy-test receiver: it pairs
first and second coordinate derivatives of the nonlinear source with the corresponding velocity
jets.  A vector source split cannot by itself return that scalar work.  The missing incidence is
the derivative-weighted test occurrence.

This file retains that occurrence explicitly.  A Hermitian real production reading is applied to
the actual source polar split, first at one Fourier mode and then through a signed time integral.
The resulting source-vorticity relative-phase current and aligned current reconstruct the complete
sharp-source-curl test current exactly, with the PDE sign and the zero-vorticity fibre preserved.
An exact separator then proves that the polar source faces without their test occurrence cannot
determine a production reading.  Consequently this construction does not identify the resulting
curl-test current with `coordinateH2NonlinearProductionCurrent`: the still-missing theorem is the
physical/Fourier derivative-and-Parseval chart carrying the order-one and order-two energy tests.
-/

noncomputable section

open MeasureTheory Real Set
open scoped BigOperators Interval

namespace Soma.Holonics.Millennium.NavierStokesPhaseCurrentH2ProductionJoin

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearSourceSquareOwner
open Soma.Holonics.Millennium.NavierStokesAdaptiveNonlinearTriangleService
open Soma.Holonics.Millennium.NavierStokesDirectionDepletedH2Production
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenCompactWeightedPath
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenH2EnergyH3Dissipation
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection

set_option maxHeartbeats 2400000

/-! ## The missing derivative-weighted test occurrence -/

/-- A real production receiver on a complex Fourier mode.  The test is the first argument so the
source remains complex-linear in the second argument, exactly as in the scalar torus Parseval
identity. -/
def sourceTestProductionReading (test source : ComplexVector) : ℝ :=
  (∑ component : Fin 3,
    (starRingEnd ℂ) (test component) * source component).re

/-- The production receiver is additive in the transported source occurrence. -/
theorem sourceTestProductionReading_add
    (test left right : ComplexVector) :
    sourceTestProductionReading test (left + right) =
      sourceTestProductionReading test left + sourceTestProductionReading test right := by
  simp [sourceTestProductionReading, mul_add, Finset.sum_add_distrib]

/-- The receiver returns zero on the zero source occurrence. -/
theorem sourceTestProductionReading_zero (test : ComplexVector) :
    sourceTestProductionReading test 0 = 0 := by
  simp [sourceTestProductionReading]

/-- The source-vorticity relative-phase part of one declared production test. -/
def sourceVorticityRelativePhaseReading
    (receiver source test : ComplexVector) : ℝ :=
  sourceTestProductionReading test (receiverDirectionRemainder receiver source)

/-- The receiver-aligned part of the same declared production test. -/
def sourceVorticityAlignedReading
    (receiver source test : ComplexVector) : ℝ :=
  sourceTestProductionReading test
    (receiverAlignedAmplitude receiver source • receiver)

/-- The test occurrence turns the polar vector reconstruction into an exact signed production
reconstruction.  No norm or absolute-value quotient has been taken. -/
theorem sourceVorticityRelativePhaseReading_add_aligned
    (receiver source test : ComplexVector) :
    sourceVorticityRelativePhaseReading receiver source test +
        sourceVorticityAlignedReading receiver source test =
      sourceTestProductionReading test source := by
  unfold sourceVorticityRelativePhaseReading sourceVorticityAlignedReading
  rw [← sourceTestProductionReading_add]
  exact congrArg (sourceTestProductionReading test)
    (receiverDirectionRemainder_add_aligned receiver source)

/-- At a zero receiver the aligned chart is zero and the complete source remains in the phase
fibre.  This is the zero-vorticity reconstruction fibre, not a removable singularity. -/
theorem sourceVorticityReadings_zero_receiver
    (source test : ComplexVector) :
    sourceVorticityRelativePhaseReading 0 source test =
        sourceTestProductionReading test source ∧
      sourceVorticityAlignedReading 0 source test = 0 := by
  constructor <;>
    simp [sourceVorticityRelativePhaseReading, sourceVorticityAlignedReading,
      receiverDirectionRemainder, receiverAlignedAmplitude, sourceTestProductionReading,
      complexDot]

/-- The two polar test faces pay the absolute complete test reading without changing its signed
reconstruction. -/
theorem abs_sourceTestProductionReading_le_polar
    (receiver source test : ComplexVector) :
    |sourceTestProductionReading test source| ≤
      |sourceVorticityRelativePhaseReading receiver source test| +
        |sourceVorticityAlignedReading receiver source test| := by
  rw [← sourceVorticityRelativePhaseReading_add_aligned receiver source test]
  exact abs_add_le _ _

/-! ## The actual sharp-source-curl production mode -/

/-- The complete signed test reading of the actual compact nonlinear vorticity mode. -/
def compactH2ProductionCompleteTestReading
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (sourceTime : ℝ) (test : ComplexVector) : ℝ :=
  sourceTestProductionReading test
    (compactVorticityNonlinearMode solution ha hab hbT frequency sourceTime)

/-- The signed relative-phase contribution to the same actual test occurrence. -/
def compactH2ProductionRelativePhaseTestReading
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ)
    (test : ComplexVector) : ℝ :=
  sourceTestProductionReading test
    (compactH2ProductionPhaseRemainderMode
      solution ha hab hbT q frequency sourceTime)

/-- The signed aligned contribution to the same actual test occurrence. -/
def compactH2ProductionAlignedTestReading
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ)
    (test : ComplexVector) : ℝ :=
  sourceTestProductionReading test
    (compactH2ProductionAlignedMode solution ha hab hbT q frequency sourceTime)

/-- The actual phase and aligned test readings reconstruct the complete nonlinear-vorticity mode
reading, including its sign. -/
theorem compactH2ProductionRelativePhaseTestReading_add_aligned
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ)
    (test : ComplexVector) :
    compactH2ProductionRelativePhaseTestReading
        solution ha hab hbT q frequency sourceTime test +
      compactH2ProductionAlignedTestReading
        solution ha hab hbT q frequency sourceTime test =
      compactH2ProductionCompleteTestReading
        solution ha hab hbT frequency sourceTime test := by
  unfold compactH2ProductionRelativePhaseTestReading
    compactH2ProductionAlignedTestReading compactH2ProductionCompleteTestReading
  rw [← sourceTestProductionReading_add]
  exact congrArg (sourceTestProductionReading test)
    (compactH2ProductionPhaseRemainder_add_aligned
      solution ha hab hbT q frequency sourceTime)

/-- On the addressed interval, the reconstructed reading is literally the test pairing against
the negative curl of `sharpNonlinearSource`; no source sign has been renamed. -/
theorem compactH2ProductionRelativePhaseTestReading_add_aligned_eq_sharpSourceCurl
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (test : ComplexVector)
    (hsourceTime : sourceTime ∈ Icc a b) :
    compactH2ProductionRelativePhaseTestReading
        solution ha hab hbT q frequency sourceTime test +
      compactH2ProductionAlignedTestReading
        solution ha hab hbT q frequency sourceTime test =
      sourceTestProductionReading test
        (-heatTransportedH2SourceCurlCoefficient 1 0
          (sharpNonlinearSource
            (openVelocityWeightedH3State solution
              ⟨sourceTime, ha.trans_le hsourceTime.1,
                hsourceTime.2.trans_lt hbT⟩)) frequency) := by
  unfold compactH2ProductionRelativePhaseTestReading
    compactH2ProductionAlignedTestReading
  rw [← sourceTestProductionReading_add]
  exact congrArg (sourceTestProductionReading test)
    (compactH2ProductionPhaseRemainder_add_aligned_eq_sharpSourceCurl
      solution ha hab hbT q frequency hsourceTime)

/-- At an actual zero-vorticity receiver the aligned test contribution vanishes and the complete
sharp-source-curl reading stays in the relative-phase fibre. -/
theorem compactH2ProductionReadings_at_zeroVorticity
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ)
    (test : ComplexVector)
    (hvorticity :
      vorticityAt
        (fun x ↦ velocity x (compactInteriorTime ha hab hbT sourceTime).1)
        (euclideanRepresentative q) = 0) :
    compactH2ProductionRelativePhaseTestReading
        solution ha hab hbT q frequency sourceTime test =
        compactH2ProductionCompleteTestReading
          solution ha hab hbT frequency sourceTime test ∧
      compactH2ProductionAlignedTestReading
        solution ha hab hbT q frequency sourceTime test = 0 := by
  have hreceiver :
      compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime = 0 := by
    unfold compactH2ProductionDirectionReceiver
    rw [openPeriodicComplexVorticityAt_eq_complexOfRealSpace, hvorticity]
    rfl
  constructor <;>
    simp [compactH2ProductionRelativePhaseTestReading,
      compactH2ProductionAlignedTestReading, compactH2ProductionCompleteTestReading,
      compactH2ProductionPhaseRemainderMode, compactH2ProductionAlignedMode,
      compactH2ProductionAlignedAmplitude, hreceiver, receiverDirectionRemainder,
      receiverAlignedAmplitude, sourceTestProductionReading, complexDot]

/-! ## The derivative-weighted finite Fourier receiver -/

/-- The explicit Fourier test naturally carried by the homogeneous order-one and order-two
velocity energy faces after curl transport: vorticity at order zero plus one Stokes derivative.
This definition does not assert the still-missing coordinate/Fourier integration-by-parts chart. -/
def compactH2CurlEnergyTestMode
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (sourceTime : ℝ) : ComplexVector :=
  ((1 + torusStokesEigenvalue frequency : ℝ) : ℂ) •
    openPeriodicVorticityFourierMode solution
      (compactInteriorTime ha hab hbT sourceTime) frequency

/-- One finite-aperture signed relative-phase current density under the explicit curl-energy test.
The physical receiver `q`, Fourier mode population, derivative weight and source time remain
separate addressed arguments. -/
def compactFiniteH2CurlRelativePhaseAt
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (modes : Finset SpatialFrequency) (sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈ modes,
    compactH2ProductionRelativePhaseTestReading
      solution ha hab hbT q frequency sourceTime
        (compactH2CurlEnergyTestMode
          solution ha hab hbT frequency sourceTime)

/-- The aligned companion density on the same finite Fourier aperture. -/
def compactFiniteH2CurlAlignedAt
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (modes : Finset SpatialFrequency) (sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈ modes,
    compactH2ProductionAlignedTestReading
      solution ha hab hbT q frequency sourceTime
        (compactH2CurlEnergyTestMode
          solution ha hab hbT frequency sourceTime)

/-- The complete finite-aperture negative-sharp-source-curl density under that test. -/
def compactFiniteH2CurlCompleteAt
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (modes : Finset SpatialFrequency) (sourceTime : ℝ) : ℝ :=
  ∑ frequency ∈ modes,
    compactH2ProductionCompleteTestReading
      solution ha hab hbT frequency sourceTime
        (compactH2CurlEnergyTestMode
          solution ha hab hbT frequency sourceTime)

/-- The finite Fourier population preserves the exact phase-plus-aligned reconstruction. -/
theorem compactFiniteH2CurlRelativePhaseAt_add_aligned
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (modes : Finset SpatialFrequency) (sourceTime : ℝ) :
    compactFiniteH2CurlRelativePhaseAt
        solution ha hab hbT q modes sourceTime +
      compactFiniteH2CurlAlignedAt
        solution ha hab hbT q modes sourceTime =
      compactFiniteH2CurlCompleteAt
        solution ha hab hbT modes sourceTime := by
  unfold compactFiniteH2CurlRelativePhaseAt compactFiniteH2CurlAlignedAt
    compactFiniteH2CurlCompleteAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  exact compactH2ProductionRelativePhaseTestReading_add_aligned
    solution ha hab hbT q frequency sourceTime
      (compactH2CurlEnergyTestMode solution ha hab hbT frequency sourceTime)

/-- Absolute payment at a finite Fourier aperture follows from the exact signed reconstruction. -/
theorem abs_compactFiniteH2CurlCompleteAt_le_polar
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (modes : Finset SpatialFrequency) (sourceTime : ℝ) :
    |compactFiniteH2CurlCompleteAt solution ha hab hbT modes sourceTime| ≤
      |compactFiniteH2CurlRelativePhaseAt
        solution ha hab hbT q modes sourceTime| +
      |compactFiniteH2CurlAlignedAt
        solution ha hab hbT q modes sourceTime| := by
  rw [← compactFiniteH2CurlRelativePhaseAt_add_aligned
    solution ha hab hbT q modes sourceTime]
  exact abs_add_le _ _

/-- On the actual source interval the complete finite density is exactly the negative curl of the
native `sharpNonlinearSource` paired against the derivative-weighted vorticity test. -/
theorem compactFiniteH2CurlCompleteAt_eq_sharpSourceCurl
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (modes : Finset SpatialFrequency) (hsourceTime : sourceTime ∈ Icc a b) :
    compactFiniteH2CurlCompleteAt solution ha hab hbT modes sourceTime =
      ∑ frequency ∈ modes,
        sourceTestProductionReading
          (compactH2CurlEnergyTestMode
            solution ha hab hbT frequency sourceTime)
          (-heatTransportedH2SourceCurlCoefficient 1 0
            (sharpNonlinearSource
              (openVelocityWeightedH3State solution
                ⟨sourceTime, ha.trans_le hsourceTime.1,
                  hsourceTime.2.trans_lt hbT⟩)) frequency) := by
  unfold compactFiniteH2CurlCompleteAt
  apply Finset.sum_congr rfl
  intro frequency _hfrequency
  unfold compactH2ProductionCompleteTestReading
  rw [compactVorticityNonlinearMode_eq_neg_unclockedSharpSourceCurl
    solution ha hab hbT frequency hsourceTime]

/-! ## Signed time transport -/

/-- The signed source-vorticity relative-phase time current for one Fourier path and one explicit
test path.  This is a real interval current, not the earlier absolute ENNReal phase mass. -/
def sourceVorticityRelativePhaseTimeCurrent
    (receiver source test : ℝ → ComplexVector) (a b : ℝ) : ℝ :=
  ∫ sourceTime in a..b,
    sourceVorticityRelativePhaseReading
      (receiver sourceTime) (source sourceTime) (test sourceTime)

/-- The aligned companion current on the same time orientation. -/
def sourceVorticityAlignedTimeCurrent
    (receiver source test : ℝ → ComplexVector) (a b : ℝ) : ℝ :=
  ∫ sourceTime in a..b,
    sourceVorticityAlignedReading
      (receiver sourceTime) (source sourceTime) (test sourceTime)

/-- The complete signed source-test time current. -/
def sourceTestProductionTimeCurrent
    (source test : ℝ → ComplexVector) (a b : ℝ) : ℝ :=
  ∫ sourceTime in a..b,
    sourceTestProductionReading (test sourceTime) (source sourceTime)

/-- Time integration preserves the exact polar production reconstruction. -/
theorem sourceVorticityRelativePhaseTimeCurrent_add_aligned
    (receiver source test : ℝ → ComplexVector) (a b : ℝ)
    (hphase : IntervalIntegrable
      (fun sourceTime ↦ sourceVorticityRelativePhaseReading
        (receiver sourceTime) (source sourceTime) (test sourceTime)) volume a b)
    (haligned : IntervalIntegrable
      (fun sourceTime ↦ sourceVorticityAlignedReading
        (receiver sourceTime) (source sourceTime) (test sourceTime)) volume a b) :
    sourceVorticityRelativePhaseTimeCurrent receiver source test a b +
        sourceVorticityAlignedTimeCurrent receiver source test a b =
      sourceTestProductionTimeCurrent source test a b := by
  unfold sourceVorticityRelativePhaseTimeCurrent sourceVorticityAlignedTimeCurrent
    sourceTestProductionTimeCurrent
  rw [← intervalIntegral.integral_add hphase haligned]
  apply intervalIntegral.integral_congr
  intro sourceTime _hsourceTime
  exact sourceVorticityRelativePhaseReading_add_aligned
    (receiver sourceTime) (source sourceTime) (test sourceTime)

/-- The actual signed finite-aperture source-vorticity relative-phase time current. -/
def compactFiniteH2CurlRelativePhaseTimeCurrent
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (modes : Finset SpatialFrequency) : ℝ :=
  ∫ sourceTime in a..b,
    compactFiniteH2CurlRelativePhaseAt
      solution ha hab hbT q modes sourceTime

/-- The actual aligned time current on the same aperture and orientation. -/
def compactFiniteH2CurlAlignedTimeCurrent
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (modes : Finset SpatialFrequency) : ℝ :=
  ∫ sourceTime in a..b,
    compactFiniteH2CurlAlignedAt solution ha hab hbT q modes sourceTime

/-- The complete actual negative-source-curl test current. -/
def compactFiniteH2CurlCompleteTimeCurrent
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (modes : Finset SpatialFrequency) : ℝ :=
  ∫ sourceTime in a..b,
    compactFiniteH2CurlCompleteAt solution ha hab hbT modes sourceTime

/-- The actual relative-phase and aligned time currents reconstruct the complete finite curl-test
current.  A bound on these two currents therefore pays this receiver exactly; identifying its
cofinal Parseval return with coordinate `P2` remains the separated missing chart below. -/
theorem compactFiniteH2CurlRelativePhaseTimeCurrent_add_aligned
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (modes : Finset SpatialFrequency)
    (hphase : IntervalIntegrable
      (compactFiniteH2CurlRelativePhaseAt
        solution ha hab hbT q modes) volume a b)
    (haligned : IntervalIntegrable
      (compactFiniteH2CurlAlignedAt
        solution ha hab hbT q modes) volume a b) :
    compactFiniteH2CurlRelativePhaseTimeCurrent
        solution ha hab hbT q modes +
      compactFiniteH2CurlAlignedTimeCurrent
        solution ha hab hbT q modes =
      compactFiniteH2CurlCompleteTimeCurrent
        solution ha hab hbT modes := by
  unfold compactFiniteH2CurlRelativePhaseTimeCurrent
    compactFiniteH2CurlAlignedTimeCurrent compactFiniteH2CurlCompleteTimeCurrent
  rw [← intervalIntegral.integral_add hphase haligned]
  apply intervalIntegral.integral_congr
  intro sourceTime _hsourceTime
  exact compactFiniteH2CurlRelativePhaseAt_add_aligned
    solution ha hab hbT q modes sourceTime

/-! ## Exact separator: the polar source faces do not contain their energy test -/

theorem sourceTestProductionReading_orthogonalSeparator_self :
    sourceTestProductionReading orthogonalSeparatorOutput orthogonalSeparatorOutput = 1 := by
  simp [sourceTestProductionReading, orthogonalSeparatorOutput]

theorem sourceTestProductionReading_orthogonalSeparator_zero_test :
    sourceTestProductionReading 0 orthogonalSeparatorOutput = 0 := by
  simp [sourceTestProductionReading]

/-- **[counterexample; formal-checked]** The same receiver, source, phase face and aligned face
return distinct production values under distinct derivative-weighted tests.  Therefore no function
of only the receiver and its two source faces can return every production pairing.  This is the
exact separator between the standing sharp-source-curl split and the coordinate `P2` receiver:
the missing datum is the order-one/order-two test chart (and its Parseval transport), not another
source decomposition. -/
theorem no_sourcePolarFaces_determine_all_productionTests :
    ¬ ∃ reading : ComplexVector → ComplexVector → ComplexVector → ℝ,
      ∀ (receiver source test : ComplexVector),
        reading receiver
            (receiverDirectionRemainder receiver source)
            (receiverAlignedAmplitude receiver source • receiver) =
          sourceTestProductionReading test source := by
  rintro ⟨reading, hreading⟩
  have hself := hreading orthogonalSeparatorReceiver orthogonalSeparatorOutput
    orthogonalSeparatorOutput
  have hzero := hreading orthogonalSeparatorReceiver orthogonalSeparatorOutput 0
  rw [sourceTestProductionReading_orthogonalSeparator_self] at hself
  rw [sourceTestProductionReading_orthogonalSeparator_zero_test] at hzero
  linarith

section Audit

#print axioms sourceVorticityRelativePhaseReading_add_aligned
#print axioms sourceVorticityReadings_zero_receiver
#print axioms compactH2ProductionRelativePhaseTestReading_add_aligned
#print axioms compactH2ProductionRelativePhaseTestReading_add_aligned_eq_sharpSourceCurl
#print axioms compactH2ProductionReadings_at_zeroVorticity
#print axioms compactFiniteH2CurlRelativePhaseAt_add_aligned
#print axioms abs_compactFiniteH2CurlCompleteAt_le_polar
#print axioms compactFiniteH2CurlCompleteAt_eq_sharpSourceCurl
#print axioms sourceVorticityRelativePhaseTimeCurrent_add_aligned
#print axioms compactFiniteH2CurlRelativePhaseTimeCurrent_add_aligned
#print axioms no_sourcePolarFaces_determine_all_productionTests

end Audit

end Soma.Holonics.Millennium.NavierStokesPhaseCurrentH2ProductionJoin
