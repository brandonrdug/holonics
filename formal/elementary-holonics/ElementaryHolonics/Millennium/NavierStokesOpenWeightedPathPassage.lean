import ElementaryHolonics.Millennium.NavierStokesOpenMildFieldReconstruction
import ElementaryHolonics.Millennium.NavierStokesRestartSeam
import ElementaryHolonics.Millennium.NavierStokesWeightedClassicalRestartSupply

/-!
# An actual open solution enters the native weighted path circulation

**[proved-derived]** At every strict-interior face of an actual unforced periodic solution,
the complete weighted `H³` Fourier state itself selects a positive native clock.  The standing
invariant mild restart and all-order lift return a continuous native path.  Nonnegative-viscosity
overlap uniqueness then identifies the reconstructed restart field with the shifted actual
solution.  Exact recovery of every native coefficient upgrades that field equality to equality
of the native weighted states on each closed subaperture strictly inside the overlap.

Thus continuity and the mild fixed-point law are properties of the actual solution's coefficient
path, rather than of a separately postulated family.  The only aperture restriction is the
already-declared local clock and the remaining open lifespan.
-/

noncomputable section

open Function Set

namespace Soma.Holonics.Millennium.NavierStokesOpenWeightedPathPassage

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCoordinateNativeMildRestart
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenMildFieldReconstruction
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesRestartSeam
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedTower
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesUniformRestart
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartCarrier
open Soma.Holonics.Millennium.NavierStokesWeightedClassicalRestartSupply
open Soma.Holonics.Millennium.NavierStokesWeightedCommonApertureUniqueness
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteApertureHigherOrderPersistence
open Soma.Holonics.Millennium.NavierStokesWeightedFiniteOrderFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedFourierReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedLerayBilinear
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedRestartAperture
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothSliceReconstruction
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Native restart at one actual interior face -/

/-- The local clock selected by the complete native state of one actual interior slice. -/
def openSliceNativeClock
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T) : ℝ :=
  weightedRestartTimeFromCap nu ‖openVelocityWeightedH3State solution t₀‖

theorem openSliceNativeClock_pos
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T) :
    0 < openSliceNativeClock solution hnu t₀ := by
  exact weightedRestartTimeFromCap_pos hnu
    (norm_nonneg (openVelocityWeightedH3State solution t₀))

/-- The arbitrary actual interior slice returns its complete native mild/classical carrier. -/
noncomputable def openSliceWeightedClassicalCarrier
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T) :
    WeightedClassicalRestartCarrier nu
      ‖openVelocityWeightedH3State solution t₀‖ hnu
      (norm_nonneg (openVelocityWeightedH3State solution t₀))
      (openVelocityWeightedH3State solution t₀) := by
  let u : InitialVelocity := fun x ↦ velocity x t₀.1
  let hu := openPeriodicSolutionOn_velocitySlice_contDiff solution t₀.2
  let hperiodic : IsOnePeriodic u :=
    solution.velocityPeriodic t₀.1 ⟨t₀.2.1.le, t₀.2.2⟩
  let state : PeriodicVectorWeightedSobolev 3 :=
    openVelocityWeightedH3State solution t₀
  let initialTower : CompatibleNativeWeightedSobolevTower :=
    smoothSliceCompatibleNativeWeightedSobolevTower u hu hperiodic
  have hbase : initialTower.base = state := by
    rfl
  let native : NativeMildRestartAtCap nu ‖state‖ hnu (norm_nonneg state) state :=
    nativeMildRestartAtCap hnu (norm_nonneg state) state le_rfl
      (isWeightedFourierReal_smoothSliceVectorWeightedH3 u hu hperiodic)
      (openVelocityWeightedH3State_divergenceFree solution t₀)
  have hnativeFixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu)
        (weightedRestartTimeFromCap_pos hnu (norm_nonneg state)).le
        initialTower.base) native.path := by
    rw [hbase]
    simpa only [weightedMildRestartMap] using native.fixed
  let towerWitness := exists_coherentWeightedSmoothPathTower_of_nativeFixed
    hnu (weightedRestartTimeFromCap_pos hnu (norm_nonneg state)).le
    initialTower native.path hnativeFixed
  let tower := Classical.choose towerWitness
  exact weightedClassicalRestartCarrierOfNative
    hnu (norm_nonneg state) state native tower

/-- The carrier above is an official local restart of the very actual solution slice from which
it was constructed. -/
noncomputable def openSliceInteriorRestart
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T) :
    InteriorPeriodicRestart solution t₀.1
      (openSliceNativeClock solution hnu t₀) := by
  let state := openVelocityWeightedH3State solution t₀
  let carrier := openSliceWeightedClassicalCarrier solution hnu t₀
  have hlocal := carrier.toOpenPeriodicSolutionOn
    (jointSpacetimeSmoothnessUpgradeOfWeightedClassicalRestartCarrier carrier)
  refine
    { interior := ⟨t₀.2.1.le, t₀.2.2⟩
      radius_pos := openSliceNativeClock_pos solution hnu t₀
      restartVelocity := weightedClassicalRestartVelocity
        (openSliceNativeClock_pos solution hnu t₀).le carrier.path
      restartPressure := weightedClassicalRestartPressure
        (openSliceNativeClock_pos solution hnu t₀).le carrier.path
      restartSolution := ?_ }
  have hinitial : weightedClassicalRestartInitial state =
      velocityTrace velocity t₀.1 := by
    unfold state openVelocityWeightedH3State weightedClassicalRestartInitial velocityTrace
    exact reconstructedVelocity_smoothSliceVectorWeightedH3
      (fun x ↦ velocity x t₀.1)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution t₀.2)
      (solution.velocityPeriodic t₀.1 ⟨t₀.2.1.le, t₀.2.2⟩)
  have hforce : shiftVelocityField (0 : VelocityField) t₀.1 = 0 := by
    funext x tau
    rfl
  rw [hforce]
  rw [hinitial] at hlocal
  simpa only [openSliceNativeClock] using hlocal

/-! ## Exact state recovery from the reconstructed real field -/

/-- On the Fourier-real fibre, the complete reconstructed velocity is faithful to the native
weighted state.  Equality of physical fields therefore cannot silently collapse a coefficient
or its Sobolev weight. -/
theorem weightedH3State_eq_of_reconstructedVelocity_eq
    {left right : PeriodicVectorWeightedSobolev 3}
    (hleft : IsWeightedFourierReal 3 left)
    (hright : IsWeightedFourierReal 3 right)
    (hfield : reconstructedVelocity left = reconstructedVelocity right) :
    left = right := by
  funext component
  rw [← coefficientWeightedRealization_weightedSobolevCoefficients
      3 (left component),
    ← coefficientWeightedRealization_weightedSobolevCoefficients
      3 (right component)]
  congr 1
  apply Subtype.ext
  apply lp.ext
  funext k
  calc
    (weightedSobolevCoefficients 3 (left component)).1 k =
        vectorSpatialFourierCoeff (reconstructedVelocity left)
          (continuous_reconstructedVelocity left)
          (isOnePeriodic_reconstructedVelocity left) k component :=
      (vectorSpatialFourierCoeff_reconstructedVelocity_eq_unweighted
        hleft k component).symm
    _ = vectorSpatialFourierCoeff (reconstructedVelocity right)
          (continuous_reconstructedVelocity right)
          (isOnePeriodic_reconstructedVelocity right) k component := by
      rw [vectorSpatialFourierCoeff_apply, vectorSpatialFourierCoeff_apply]
      apply congrArg (fun field : C(SpatialTorus, ℂ) ↦
        torusSpatialFourierCoeff field k)
      apply ContinuousMap.ext
      intro q
      obtain ⟨x, rfl⟩ := euclideanToSpatialTorus_surjective q
      simp only [periodicTorusLift_projection]
      exact congrArg (fun value : Space ↦ (value component : ℂ))
        (congrFun hfield x)
    _ = (weightedSobolevCoefficients 3 (right component)).1 k :=
      vectorSpatialFourierCoeff_reconstructedVelocity_eq_unweighted
        hright k component

/-! ## The actual continuous native path on the uniqueness overlap -/

/-- The exact remaining lifespan/native-clock overlap at one actual interior face. -/
def openSliceNativeOverlap
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T) : ℝ :=
  restartCommonLifespan (openSliceInteriorRestart solution hnu t₀)

theorem openSliceNativeOverlap_pos
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T) :
    0 < openSliceNativeOverlap solution hnu t₀ :=
  InteriorPeriodicRestart.restartCommonLifespan_pos
    (openSliceInteriorRestart solution hnu t₀)

theorem openSliceNativeOverlap_le_clock
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T) :
    openSliceNativeOverlap solution hnu t₀ ≤
      openSliceNativeClock solution hnu t₀ := by
  unfold openSliceNativeOverlap restartCommonLifespan
  exact min_le_right _ _

/-- Restrict the native fixed path returned at an actual slice to any addressed closed aperture
strictly contained in the uniqueness overlap. -/
noncomputable def actualOpenWeightedH3Path
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    (S : ℝ) (hS : 0 ≤ S)
    (hSoverlap : S < openSliceNativeOverlap solution hnu t₀) :
    WeightedH3Path S :=
  weightedH3PathTimeRestrict
    ((le_of_lt hSoverlap).trans
      (openSliceNativeOverlap_le_clock solution hnu t₀))
    (openSliceWeightedClassicalCarrier solution hnu t₀).path

@[simp]
theorem actualOpenWeightedH3Path_apply
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    (S : ℝ) (hS : 0 ≤ S)
    (hSoverlap : S < openSliceNativeOverlap solution hnu t₀)
    (tau : Icc (0 : ℝ) S) :
    actualOpenWeightedH3Path solution hnu t₀ S hS hSoverlap tau =
      openVelocityWeightedH3State solution
        ⟨t₀.1 + tau.1, by
          constructor
          · linarith [t₀.2.1, tau.2.1]
          · have hoverlapRemaining :
                openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
              unfold openSliceNativeOverlap restartCommonLifespan
              exact min_le_left _ _
            linarith [tau.2.2, hSoverlap, hoverlapRemaining]
        ⟩ := by
  let carrier := openSliceWeightedClassicalCarrier solution hnu t₀
  let restart := openSliceInteriorRestart solution hnu t₀
  have hSclock : S ≤ openSliceNativeClock solution hnu t₀ :=
    (le_of_lt hSoverlap).trans
      (openSliceNativeOverlap_le_clock solution hnu t₀)
  let tauClock : Icc (0 : ℝ) (openSliceNativeClock solution hnu t₀) :=
    ⟨tau.1, tau.2.1, tau.2.2.trans hSclock⟩
  have htauOverlap : tau.1 ∈ openTimeSlab
      (openSliceNativeOverlap solution hnu t₀) :=
    ⟨tau.2.1, lt_of_le_of_lt tau.2.2 hSoverlap⟩
  have htauRemaining : tau.1 < T - t₀.1 := by
    have hoverlapRemaining :
        openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
      unfold openSliceNativeOverlap restartCommonLifespan
      exact min_le_left _ _
    exact lt_of_lt_of_le htauOverlap.2 hoverlapRemaining
  let shiftedTime : Ioo (0 : ℝ) T :=
    ⟨t₀.1 + tau.1,
      ⟨by linarith [t₀.2.1, tau.2.1], by linarith⟩⟩
  have hagree :=
    (InteriorPeriodicRestart.agreesWithShiftedBase restart hnu.le).velocity
  have hfield : reconstructedVelocity (carrier.path tauClock) =
      (fun x ↦ velocity x shiftedTime.1) := by
    funext x
    have hx := hagree x tau.1 htauOverlap
    have hx' : velocity x (t₀.1 + tau.1) =
        weightedClassicalRestartVelocity
          (openSliceNativeClock_pos solution hnu t₀).le carrier.path x tau.1 := by
      simpa only [restart, carrier, shiftVelocityField, openSliceInteriorRestart]
        using hx
    calc
      reconstructedVelocity (carrier.path tauClock) x =
          reconstructedVelocity
            (weightedPathExtension
              (openSliceNativeClock_pos solution hnu t₀).le
              carrier.path tau.1) x := by
        rw [weightedPathExtension_of_mem
          (openSliceNativeClock_pos solution hnu t₀).le carrier.path tauClock.2]
        congr 2
      _ = weightedClassicalRestartVelocity
            (openSliceNativeClock_pos solution hnu t₀).le
            carrier.path x tau.1 := rfl
      _ = velocity x shiftedTime.1 := hx'.symm
  have hcarrierReal : IsWeightedFourierReal 3 (carrier.path tauClock) :=
    carrier.fourierReal tauClock
  have hsliceReal : IsWeightedFourierReal 3
      (openVelocityWeightedH3State solution shiftedTime) :=
    isWeightedFourierReal_smoothSliceVectorWeightedH3
      (fun x ↦ velocity x shiftedTime.1)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution shiftedTime.2)
      (solution.velocityPeriodic shiftedTime.1
        ⟨shiftedTime.2.1.le, shiftedTime.2.2⟩)
  have hsliceReconstruct : reconstructedVelocity
      (openVelocityWeightedH3State solution shiftedTime) =
        (fun x ↦ velocity x shiftedTime.1) := by
    exact reconstructedVelocity_smoothSliceVectorWeightedH3
      (fun x ↦ velocity x shiftedTime.1)
      (openPeriodicSolutionOn_velocitySlice_contDiff solution shiftedTime.2)
      (solution.velocityPeriodic shiftedTime.1
        ⟨shiftedTime.2.1.le, shiftedTime.2.2⟩)
  change carrier.path tauClock =
    openVelocityWeightedH3State solution shiftedTime
  exact weightedH3State_eq_of_reconstructedVelocity_eq
    hcarrierReal hsliceReal (hfield.trans hsliceReconstruct.symm)

/-- The actual clock-shifted slice family, now presented on the addressed closed aperture. -/
def shiftedOpenVelocityWeightedH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    (S : ℝ) (hSoverlap : S < openSliceNativeOverlap solution hnu t₀) :
    Icc (0 : ℝ) S → PeriodicVectorWeightedSobolev 3 :=
  fun tau ↦ openVelocityWeightedH3State solution
    ⟨t₀.1 + tau.1, by
      constructor
      · linarith [t₀.2.1, tau.2.1]
      · have hoverlapRemaining :
            openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
          unfold openSliceNativeOverlap restartCommonLifespan
          exact min_le_left _ _
        linarith [tau.2.2, hSoverlap, hoverlapRemaining]
    ⟩

/-- The restricted native fixed path is literally the actual clock-shifted coefficient family. -/
theorem actualOpenWeightedH3Path_eq_shiftedState
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    (S : ℝ) (hS : 0 ≤ S)
    (hSoverlap : S < openSliceNativeOverlap solution hnu t₀) :
    (actualOpenWeightedH3Path solution hnu t₀ S hS hSoverlap :
        Icc (0 : ℝ) S → PeriodicVectorWeightedSobolev 3) =
      shiftedOpenVelocityWeightedH3State solution hnu t₀ S hSoverlap := by
  funext tau
  simpa only [shiftedOpenVelocityWeightedH3State] using
    actualOpenWeightedH3Path_apply solution hnu t₀ S hS hSoverlap tau

/-- Consequently the actual open-solution slice family is norm-continuous in the complete native
weighted `H³` carrier on every closed subaperture of the local overlap. -/
theorem continuous_shiftedOpenVelocityWeightedH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    (S : ℝ) (hS : 0 ≤ S)
    (hSoverlap : S < openSliceNativeOverlap solution hnu t₀) :
    Continuous (shiftedOpenVelocityWeightedH3State
      solution hnu t₀ S hSoverlap) := by
  rw [← actualOpenWeightedH3Path_eq_shiftedState
    solution hnu t₀ S hS hSoverlap]
  exact (actualOpenWeightedH3Path solution hnu t₀ S hS hSoverlap).continuous

/-- The exact sharp nonlinear source is continuous along the same actual native path. -/
theorem continuous_sharpNonlinearSource_shiftedOpenVelocityWeightedH3State
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    (S : ℝ) (hS : 0 ≤ S)
    (hSoverlap : S < openSliceNativeOverlap solution hnu t₀) :
    Continuous (fun tau ↦ sharpNonlinearSource
      (shiftedOpenVelocityWeightedH3State
        solution hnu t₀ S hSoverlap tau)) := by
  have hsource : Continuous
      (fun state : PeriodicVectorWeightedSobolev 3 ↦
        weightedLerayDivergenceConvolutionContinuous state state) :=
    weightedLerayDivergenceConvolutionContinuous.continuous.clm_apply continuous_id
  exact hsource.comp
    (continuous_shiftedOpenVelocityWeightedH3State
      solution hnu t₀ S hS hSoverlap)

/-- Reconstructing any face of the actual native path returns the original velocity slice
pointwise, with the local clock shift retained. -/
theorem reconstructedVelocity_actualOpenWeightedH3Path
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    (S : ℝ) (hS : 0 ≤ S)
    (hSoverlap : S < openSliceNativeOverlap solution hnu t₀)
    (tau : Icc (0 : ℝ) S) :
    reconstructedVelocity
        (actualOpenWeightedH3Path solution hnu t₀ S hS hSoverlap tau) =
      (fun x ↦ velocity x (t₀.1 + tau.1)) := by
  rw [actualOpenWeightedH3Path_apply]
  exact reconstructedVelocity_smoothSliceVectorWeightedH3
    (fun x ↦ velocity x (t₀.1 + tau.1))
    (openPeriodicSolutionOn_velocitySlice_contDiff solution (by
      constructor
      · linarith [t₀.2.1, tau.2.1]
      · have hoverlapRemaining :
            openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
          unfold openSliceNativeOverlap restartCommonLifespan
          exact min_le_left _ _
        linarith [tau.2.2, hSoverlap, hoverlapRemaining]))
    (solution.velocityPeriodic (t₀.1 + tau.1) (by
      constructor
      · linarith [t₀.2.1, tau.2.1]
      · have hoverlapRemaining :
            openSliceNativeOverlap solution hnu t₀ ≤ T - t₀.1 := by
          unfold openSliceNativeOverlap restartCommonLifespan
          exact min_le_left _ _
        linarith [tau.2.2, hSoverlap, hoverlapRemaining]))

/-- The actual shifted solution path obeys the complete native heat/Duhamel fixed-point law on
every addressed closed subaperture of the overlap. -/
theorem actualOpenWeightedH3Path_isFixedPt
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (t₀ : Ioo (0 : ℝ) T)
    (S : ℝ) (hS : 0 ≤ S)
    (hSoverlap : S < openSliceNativeOverlap solution hnu t₀) :
    IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hS
        (openVelocityWeightedH3State solution t₀))
      (actualOpenWeightedH3Path solution hnu t₀ S hS hSoverlap) := by
  let carrier := openSliceWeightedClassicalCarrier solution hnu t₀
  have hclock : 0 ≤ openSliceNativeClock solution hnu t₀ :=
    (openSliceNativeClock_pos solution hnu t₀).le
  have hSclock : S ≤ openSliceNativeClock solution hnu t₀ :=
    (le_of_lt hSoverlap).trans
      (openSliceNativeOverlap_le_clock solution hnu t₀)
  have hfixed : IsFixedPt
      (weightedMildMap (Real.toNNReal nu) (real_toNNReal_pos hnu) hclock
        (openVelocityWeightedH3State solution t₀)) carrier.path := by
    simpa only [carrier, openSliceNativeClock, weightedMildRestartMap] using
      carrier.fixed
  simpa only [actualOpenWeightedH3Path, carrier] using
    isFixedPt_weightedMildMap_timeRestrict
      (Real.toNNReal nu) (real_toNNReal_pos hnu) hS hclock hSclock
      (openVelocityWeightedH3State solution t₀) carrier.path hfixed

section Audit

#print axioms openSliceWeightedClassicalCarrier
#print axioms openSliceInteriorRestart
#print axioms weightedH3State_eq_of_reconstructedVelocity_eq
#print axioms actualOpenWeightedH3Path_apply
#print axioms continuous_shiftedOpenVelocityWeightedH3State
#print axioms continuous_sharpNonlinearSource_shiftedOpenVelocityWeightedH3State
#print axioms reconstructedVelocity_actualOpenWeightedH3Path
#print axioms actualOpenWeightedH3Path_isFixedPt

end Audit

end Soma.Holonics.Millennium.NavierStokesOpenWeightedPathPassage
