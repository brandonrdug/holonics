import ElementaryHolonics.Millennium.NavierStokesDirectionDepletedH2Production
import ElementaryHolonics.Millennium.NavierStokesFiniteTimeVorticity

/-!
# The division-free vorticity cross-seam clock

**[proved-derived; formal-checked]**  The receiver-orthogonal source fibre used by the physical
`H2` production line has an exact clock law before the direction quotient is opened.  Crossing
the contemporaneous physical vorticity receiver with one nonlinear vorticity mode kills its
aligned face.  The exact Stokes mode equation then identifies the remaining numerator with the
sum of the vorticity-mode time jet and the viscous Stokes return:

`receiver cross phase = receiver cross modeTimeJet + nu * lambda * (receiver cross mode)`.

The law never divides by the receiver magnitude.  At a zero-vorticity receiver the cross seam
vanishes, but the complete phase fibre is retained separately and is exactly the complete source
mode.  Thus the zero fibre is not misidentified with a zero source.

The final theorem gives the same numerator law before Fourier diagonalization.  It is obtained
from the exact local curled-momentum balance and retains the vector Laplacian, curl forcing and
Eulerian vorticity time jet as distinct currents.  No norm estimate, direction-quotient
differentiation, terminal control or continuation claim is made.
-/

noncomputable section

open ContDiff Set
open scoped Laplacian

namespace Soma.Holonics.Millennium.NavierStokesVorticityCrossSeamClock

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDirectionDepletedH2Production
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesParabolicDirectionCurrent
open Soma.Holonics.Millennium.NavierStokesPeriodicEnergy
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCrossReconstruction
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionProjection

/-! ## Exact modewise clock -/

/-- The physical vorticity coefficient at one Fourier address and real clock occurrence. -/
def physicalVorticityMode
    (velocity : VelocityField) (frequency : SpatialFrequency) (sourceTime : ℝ) :
    ComplexVector :=
  frequencyCurlMultiplier frequency (velocityMode velocity frequency sourceTime)

/-- The exact Stokes time jet of one physical vorticity coefficient.  On an addressed compact
interior interval the compact source is the actual nonlinear source, so this is the derivative
returned by the open-solution mode equation. -/
def compactPhysicalVorticityModeTimeJet
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (sourceTime : ℝ) : ComplexVector :=
  (((-(nu * torusStokesEigenvalue frequency) : ℝ) : ℂ) •
      physicalVorticityMode velocity frequency sourceTime) +
    compactVorticityNonlinearMode solution ha hab hbT frequency sourceTime

/-- On the declared compact source interval, the displayed clock jet is literally the derivative
of the physical vorticity coefficient. -/
theorem openPeriodicSolutionOn_hasDerivAt_compactPhysicalVorticityMode
    {T nu a b sourceTime : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (hsourceTime : sourceTime ∈ Icc a b) :
    HasDerivAt
      (fun tau ↦ physicalVorticityMode velocity frequency tau)
      (compactPhysicalVorticityModeTimeJet
        solution ha hab hbT frequency sourceTime) sourceTime := by
  have hactual := openPeriodicSolutionOn_hasDerivAt_vorticityMode_stokes
    solution
    ⟨sourceTime, ha.trans_le hsourceTime.1, hsourceTime.2.trans_lt hbT⟩ frequency
  have hcompact := compactVorticityNonlinearMode_eq_actual
    solution ha hab hbT frequency hsourceTime
  rw [compactPhysicalVorticityModeTimeJet, hcompact]
  simpa only [physicalVorticityMode] using hactual

/-- The nonlinear source is exactly the mode clock jet plus the returned viscous Stokes
coefficient. -/
theorem compactVorticityNonlinearMode_eq_timeJet_add_stokes
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (frequency : SpatialFrequency) (sourceTime : ℝ) :
    compactVorticityNonlinearMode solution ha hab hbT frequency sourceTime =
      compactPhysicalVorticityModeTimeJet
          solution ha hab hbT frequency sourceTime +
        (((nu * torusStokesEigenvalue frequency : ℝ) : ℂ) •
          physicalVorticityMode velocity frequency sourceTime) := by
  ext component
  simp [compactPhysicalVorticityModeTimeJet]

/-- Crossing a fixed receiver distributes over an exact complex source sum. -/
theorem receiverCrossDifference_add
    (receiver left right : ComplexVector) :
    receiverCrossDifference receiver (left + right) =
      receiverCrossDifference receiver left +
        receiverCrossDifference receiver right := by
  exact (crossProduct receiver).map_add left right

/-- Crossing a fixed receiver transports a complex coefficient without changing its address. -/
theorem receiverCrossDifference_smul
    (receiver source : ComplexVector) (scale : ℂ) :
    receiverCrossDifference receiver (scale • source) =
      scale • receiverCrossDifference receiver source := by
  exact (crossProduct receiver).map_smul scale source

/-- **The exact division-free clock law for one physical `H2` source phase fibre.**  The left
side is the cross seam of the canonical receiver-orthogonal source occurrence.  The right side
is its physical vorticity-mode time jet plus the viscous Stokes return.  No nonzero-vorticity
hypothesis is used. -/
theorem compactH2ProductionPhaseCrossSeam_eq_timeJet_add_stokes
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ) :
    receiverCrossDifference
        (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
        (compactH2ProductionPhaseRemainderMode
          solution ha hab hbT q frequency sourceTime) =
      receiverCrossDifference
          (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
          (compactPhysicalVorticityModeTimeJet
            solution ha hab hbT frequency sourceTime) +
        (((nu * torusStokesEigenvalue frequency : ℝ) : ℂ) •
          receiverCrossDifference
            (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
            (physicalVorticityMode velocity frequency sourceTime)) := by
  rw [show receiverCrossDifference
      (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
      (compactH2ProductionPhaseRemainderMode
        solution ha hab hbT q frequency sourceTime) =
      receiverCrossDifference
        (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
        (compactVorticityNonlinearMode
          solution ha hab hbT frequency sourceTime) by
    exact receiverCrossDifference_directionRemainder _ _]
  rw [compactVorticityNonlinearMode_eq_timeJet_add_stokes,
    receiverCrossDifference_add, receiverCrossDifference_smul]

/-! ## The explicitly retained zero-receiver fibre -/

/-- At zero physical vorticity, the canonical phase fibre is the entire nonlinear source mode.
The cross seam is zero there, so this equality is the reconstruction fibre which a numerator-only
receiver must retain. -/
theorem compactH2ProductionPhaseRemainderMode_eq_source_of_zeroVorticity
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ)
    (hvorticity :
      vorticityAt
        (fun x ↦ velocity x (compactInteriorTime ha hab hbT sourceTime).1)
        (euclideanRepresentative q) = 0) :
    compactH2ProductionPhaseRemainderMode
        solution ha hab hbT q frequency sourceTime =
      compactVorticityNonlinearMode
        solution ha hab hbT frequency sourceTime := by
  have hreceiver :
      compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime = 0 := by
    unfold compactH2ProductionDirectionReceiver
    rw [openPeriodicComplexVorticityAt_eq_complexOfRealSpace, hvorticity]
    rfl
  simp [compactH2ProductionPhaseRemainderMode, receiverDirectionRemainder,
    receiverAlignedAmplitude, hreceiver, complexDot]

/-- The cross clock numerator vanishes at a zero receiver, while the theorem above retains the
complete source in the reconstruction fibre. -/
theorem compactH2ProductionPhaseCrossSeam_eq_zero_of_zeroVorticity
    {T nu a b : ℝ}
    {initial : InitialVelocity} {velocity : VelocityField} {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T)
    (q : SpatialTorus) (frequency : SpatialFrequency) (sourceTime : ℝ)
    (hvorticity :
      vorticityAt
        (fun x ↦ velocity x (compactInteriorTime ha hab hbT sourceTime).1)
        (euclideanRepresentative q) = 0) :
    receiverCrossDifference
        (compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime)
        (compactH2ProductionPhaseRemainderMode
          solution ha hab hbT q frequency sourceTime) = 0 := by
  have hreceiver :
      compactH2ProductionDirectionReceiver solution ha hab hbT q sourceTime = 0 := by
    unfold compactH2ProductionDirectionReceiver
    rw [openPeriodicComplexVorticityAt_eq_complexOfRealSpace, hvorticity]
    rfl
  rw [hreceiver]
  exact complexCross_zero_left _

/-! ## Pointwise physical cross-seam clock -/

/-- The exact pointwise curl of the advective velocity source.  This is transport minus
stretching before any Fourier or scalar receiver. -/
def pointwiseVorticityNonlinearCurlSource
    (velocity : VelocityField) (x : Space) (t : ℝ) : Space :=
  vorticityAt
    (fun y ↦ fderiv ℝ (fun z ↦ velocity z t) y (velocity y t)) x

/-- The pointwise receiver-orthogonal nonlinear curl fibre. -/
def pointwiseVorticitySourcePhaseFibre
    (velocity : VelocityField) (x : Space) (t : ℝ) : ComplexVector :=
  receiverDirectionRemainder
    (complexOfRealSpace (vorticityField velocity x t))
    (complexOfRealSpace (pointwiseVorticityNonlinearCurlSource velocity x t))

/-- The Eulerian clock current in the pointwise law is the literal time derivative of the
physical vorticity receiver on every interior slab event. -/
theorem smoothSolutionOn_hasDerivAt_pointwiseVorticityReceiver
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    HasDerivAt (fun tau ↦ vorticityField velocity x tau)
      (eulerianTimeJet (vorticityField velocity) x t) t := by
  have hjoint : DifferentiableAt ℝ
      (Function.uncurry (vorticityField velocity)) (x, t) :=
    ((smoothSolutionOn_vorticityField_contDiffOn_interior solution).contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds
        ⟨Set.mem_univ x, ht0, htT⟩)).differentiableAt (by simp)
  have htime := hjoint.hasFDerivAt.comp t
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) x t)
  simpa [eulerianTimeJet, Function.comp_def] using htime.hasDerivAt

/-- **The local physical numerator law.**  Curl momentum gives the source cross seam as the
viscous Laplacian seam plus the curl-forcing seam minus the Eulerian vorticity clock seam.  This
statement remains valid at zero vorticity and never differentiates a normalized direction. -/
theorem smoothSolutionOn_pointwiseVorticityPhaseCrossSeamClock
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial force velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    receiverCrossDifference
        (complexOfRealSpace (vorticityField velocity x t))
        (pointwiseVorticitySourcePhaseFibre velocity x t) =
      ((nu : ℂ) •
          receiverCrossDifference
            (complexOfRealSpace (vorticityField velocity x t))
            (complexOfRealSpace (Δ (fun y ↦ vorticityField velocity y t) x))) +
        receiverCrossDifference
          (complexOfRealSpace (vorticityField velocity x t))
          (complexOfRealSpace (vorticityField force x t)) -
        receiverCrossDifference
          (complexOfRealSpace (vorticityField velocity x t))
          (complexOfRealSpace
            (eulerianTimeJet (vorticityField velocity) x t)) := by
  rw [show receiverCrossDifference
      (complexOfRealSpace (vorticityField velocity x t))
      (pointwiseVorticitySourcePhaseFibre velocity x t) =
      receiverCrossDifference
        (complexOfRealSpace (vorticityField velocity x t))
        (complexOfRealSpace
          (pointwiseVorticityNonlinearCurlSource velocity x t)) by
    exact receiverCrossDifference_directionRemainder _ _]
  have hbalance := smoothSolutionOn_curledMomentum solution ht0 htT x
  have hsource :
      pointwiseVorticityNonlinearCurlSource velocity x t =
        nu • Δ (fun y ↦ vorticityField velocity y t) x +
          vorticityField force x t -
            eulerianTimeJet (vorticityField velocity) x t := by
    unfold pointwiseVorticityNonlinearCurlSource
    rw [← hbalance]
    abel
  rw [hsource]
  ext component
  fin_cases component <;>
    simp [receiverCrossDifference, complexCross, complexOfRealSpace, crossProduct] <;>
    ring

/-- On the unforced carrier used by the physical `H2` line, the local numerator is exactly
viscous diffusion minus the Eulerian vorticity clock. -/
theorem smoothSolutionOn_pointwiseVorticityPhaseCrossSeamClock_unforced
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution : SmoothSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    {t : ℝ} (ht0 : 0 < t) (htT : t < T) (x : Space) :
    receiverCrossDifference
        (complexOfRealSpace (vorticityField velocity x t))
        (pointwiseVorticitySourcePhaseFibre velocity x t) =
      ((nu : ℂ) •
          receiverCrossDifference
            (complexOfRealSpace (vorticityField velocity x t))
            (complexOfRealSpace (Δ (fun y ↦ vorticityField velocity y t) x))) -
        receiverCrossDifference
          (complexOfRealSpace (vorticityField velocity x t))
          (complexOfRealSpace
            (eulerianTimeJet (vorticityField velocity) x t)) := by
  have hforceZero : vorticityField (0 : VelocityField) x t = 0 := by
    change derivativeCurlLinearMap
      (fderiv ℝ (fun _ : Space ↦ (0 : Space)) x) = 0
    ext component
    fin_cases component <;>
      simp [derivativeCurlLinearMap_apply, curlFromJacobian,
        jacobianMatrix_apply]
  have hclock := smoothSolutionOn_pointwiseVorticityPhaseCrossSeamClock
    solution ht0 htT x
  rw [hforceZero] at hclock
  simpa [receiverCrossDifference, complexCross, complexOfRealSpace, crossProduct]
    using hclock

section Audit

#print axioms openPeriodicSolutionOn_hasDerivAt_compactPhysicalVorticityMode
#print axioms compactVorticityNonlinearMode_eq_timeJet_add_stokes
#print axioms compactH2ProductionPhaseCrossSeam_eq_timeJet_add_stokes
#print axioms compactH2ProductionPhaseRemainderMode_eq_source_of_zeroVorticity
#print axioms compactH2ProductionPhaseCrossSeam_eq_zero_of_zeroVorticity
#print axioms smoothSolutionOn_hasDerivAt_pointwiseVorticityReceiver
#print axioms smoothSolutionOn_pointwiseVorticityPhaseCrossSeamClock
#print axioms smoothSolutionOn_pointwiseVorticityPhaseCrossSeamClock_unforced

end Audit

end Soma.Holonics.Millennium.NavierStokesVorticityCrossSeamClock
