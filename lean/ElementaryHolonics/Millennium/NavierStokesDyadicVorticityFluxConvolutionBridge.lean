import ElementaryHolonics.Millennium.NavierStokesDyadicVorticityFluxReceiver
import ElementaryHolonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration

/-!
# Finite identification of localized vorticity flux with the actual nonlinear convolution

This file closes the first algebraic gap left by the dyadic vorticity-flux receiver.  The curl of
one ordered quadratic Fourier interaction is not, by itself, transport minus stretching.  The
identity becomes exact after the two decompositions `p + q = k` and `q + p = k` are retained
together.  Accordingly, the finite theorem below uses an aperture invariant under
`p ↦ k - p`; no infinite sum or convergence premise occurs.

For an admitted solution the resulting finite nonlinear source is exactly
`stretching - transport`.  The corrected localized flux `-[P_j,u·∇]ω + P_j(ω·∇u)` is then the
dyadic projection of that source plus the transported filtered-vorticity coefficient which is
moved to the left side of the localized vorticity equation.
-/

noncomputable section

open Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesDyadicFlowCommutator
open Soma.Holonics.Millennium.NavierStokesDyadicHodgeScaleChain
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxReceiver
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionCarrierIntegration
open Soma.Holonics.Millennium.NavierStokesOpenAdvectionConvolutionBridge
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesSmoothSliceWeightedH3
open Soma.Holonics.Millennium.NavierStokesTorusFourier

/-! ## The exchanged two-pin curl identity -/

/-- Exchanging the two input pins twice returns the original advecting address. -/
@[simp]
theorem transportedFrequencyAt_involutive (k p : SpatialFrequency) :
    transportedFrequencyAt k (transportedFrequencyAt k p) = p := by
  simp [transportedFrequencyAt]

/-- The exact defect before incompressibility is imposed.  It is the sum of the two longitudinal
mode defects, so retaining both exchanged decompositions is essential. -/
private theorem exchanged_vorticity_interaction_defect
    (p q : SpatialFrequency) (advecting transported : ComplexVector)
    :
    ((complexAdvectiveInteraction p q
          (frequencyCurlMultiplier p advecting) transported +
        complexAdvectiveInteraction q p
          (frequencyCurlMultiplier q transported) advecting) -
      (complexAdvectiveInteraction p q advecting
          (frequencyCurlMultiplier q transported) +
        complexAdvectiveInteraction q p transported
          (frequencyCurlMultiplier p advecting))) -
      (-frequencyCurlMultiplier (p + q)
        (complexAdvectiveInteraction p q advecting transported +
          complexAdvectiveInteraction q p transported advecting)) =
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 2) •
        ((complexDot (complexFrequencyVector p) advecting) •
            complexCross (complexFrequencyVector q) transported +
          (complexDot (complexFrequencyVector q) transported) •
            complexCross (complexFrequencyVector p) advecting) := by
  ext component
  fin_cases component <;>
    simp [frequencyCurlMultiplier, complexAdvectiveInteraction,
      complexCross, complexDot, complexFrequencyVector, crossProduct,
      dotProduct, Fin.sum_univ_succ, Pi.smul_apply, smul_eq_mul,
      Matrix.vecHead, Matrix.vecTail, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Fin.reduceFinMk] <;>
    ring

/-- The curl of the two exchanged velocity interactions is exactly stretching minus transport.
The two divergence equations are the only hypotheses. -/
theorem neg_frequencyCurlMultiplier_exchanged_interactions
    (p q : SpatialFrequency) (advecting transported : ComplexVector)
    (hadvecting :
      complexDot (complexFrequencyVector p) advecting = 0)
    (htransported :
      complexDot (complexFrequencyVector q) transported = 0) :
    -frequencyCurlMultiplier (p + q)
        (complexAdvectiveInteraction p q advecting transported +
          complexAdvectiveInteraction q p transported advecting) =
      (complexAdvectiveInteraction p q
          (frequencyCurlMultiplier p advecting) transported +
        complexAdvectiveInteraction q p
          (frequencyCurlMultiplier q transported) advecting) -
      (complexAdvectiveInteraction p q advecting
          (frequencyCurlMultiplier q transported) +
        complexAdvectiveInteraction q p transported
          (frequencyCurlMultiplier p advecting)) := by
  have hdefect := exchanged_vorticity_interaction_defect p q advecting transported
  have hzero :
      ((2 * (Real.pi : ℂ) * Complex.I) ^ 2) •
          ((complexDot (complexFrequencyVector p) advecting) •
              complexCross (complexFrequencyVector q) transported +
            (complexDot (complexFrequencyVector q) transported) •
              complexCross (complexFrequencyVector p) advecting) = 0 := by
    simp [hadvecting, htransported]
  rw [hzero] at hdefect
  exact (sub_eq_zero.mp hdefect).symm

/-! ## Pair-symmetric finite apertures -/

/-- A finite advecting aperture retains both decompositions of every addressed output mode. -/
def IsTransportPairedAperture
    (k : SpatialFrequency) (aperture : Finset SpatialFrequency) : Prop :=
  ∀ p, p ∈ aperture ↔ transportedFrequencyAt k p ∈ aperture

/-- The exchange `p ↦ k-p` as an involutive equivalence of the frequency lattice. -/
def transportedFrequencyEquiv (k : SpatialFrequency) :
    SpatialFrequency ≃ SpatialFrequency where
  toFun := transportedFrequencyAt k
  invFun := transportedFrequencyAt k
  left_inv := transportedFrequencyAt_involutive k
  right_inv := transportedFrequencyAt_involutive k

/-- Reindexing a pair-symmetric finite population by the exchanged pin changes no sum. -/
theorem sum_transportEquiv_eq
    {M : Type*} [AddCommMonoid M]
    (k : SpatialFrequency) (aperture : Finset SpatialFrequency)
    (hpaired : IsTransportPairedAperture k aperture)
    (f : SpatialFrequency → M) :
    (∑ p ∈ aperture, f (transportedFrequencyAt k p)) =
      ∑ p ∈ aperture, f p := by
  exact Finset.sum_equiv (transportedFrequencyEquiv k)
    (fun p ↦ hpaired p) (fun _p _hp ↦ rfl)

/-- Adjoin to an aperture the exchanged partner of every pin. -/
def pairedFrequencyAperture
    (k : SpatialFrequency) (aperture : Finset SpatialFrequency) :
    Finset SpatialFrequency :=
  aperture ∪ aperture.image (transportedFrequencyAt k)

/-- The paired completion is invariant under the exchange `p ↦ k-p`. -/
theorem pairedFrequencyAperture_isTransportPaired
    (k : SpatialFrequency) (aperture : Finset SpatialFrequency) :
    IsTransportPairedAperture k (pairedFrequencyAperture k aperture) := by
  intro p
  have hforward : ∀ r,
      r ∈ pairedFrequencyAperture k aperture →
        transportedFrequencyAt k r ∈ pairedFrequencyAperture k aperture := by
    intro r hr
    rw [pairedFrequencyAperture, Finset.mem_union] at hr ⊢
    rcases hr with hr | hr
    · exact Or.inr (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
    · rcases Finset.mem_image.mp hr with ⟨pin, hpin, hpinr⟩
      left
      have hrpin : transportedFrequencyAt k r = pin := by
        rw [← hpinr, transportedFrequencyAt_involutive]
      rwa [hrpin]
  constructor
  · exact hforward p
  · intro hp
    have := hforward (transportedFrequencyAt k p) hp
    simpa using this

/-- The pairing operation is cofinal on finite apertures: it retains every original pin. -/
theorem subset_pairedFrequencyAperture
    (k : SpatialFrequency) (aperture : Finset SpatialFrequency) :
    aperture ⊆ pairedFrequencyAperture k aperture := by
  intro p hp
  exact Finset.mem_union_left _ hp

/-- **Exact finite curl/convolution identity.** On a pair-symmetric aperture, negative curl of
the velocity advection population is exactly stretching minus vorticity transport. -/
theorem neg_frequencyCurlMultiplier_finiteAdvectiveCoefficient_eq
    (k : SpatialFrequency) (aperture : Finset SpatialFrequency)
    (hpaired : IsTransportPairedAperture k aperture)
    (velocityMode : SpatialFrequency → ComplexVector)
    (hdivergence : ∀ p,
      complexDot (complexFrequencyVector p) (velocityMode p) = 0) :
    -frequencyCurlMultiplier k
        (finiteAdvectiveCoefficient aperture velocityMode velocityMode k) =
      finiteAdvectiveCoefficient aperture
          (fun p ↦ frequencyCurlMultiplier p (velocityMode p)) velocityMode k -
        finiteAdvectiveCoefficient aperture velocityMode
          (fun p ↦ frequencyCurlMultiplier p (velocityMode p)) k := by
  let source : SpatialFrequency → ComplexVector := fun p ↦
    -frequencyCurlMultiplier k
      (complexAdvectiveInteraction p (transportedFrequencyAt k p)
        (velocityMode p) (velocityMode (transportedFrequencyAt k p)))
  let balance : SpatialFrequency → ComplexVector := fun p ↦
    complexAdvectiveInteraction p (transportedFrequencyAt k p)
        (frequencyCurlMultiplier p (velocityMode p))
        (velocityMode (transportedFrequencyAt k p)) -
      complexAdvectiveInteraction p (transportedFrequencyAt k p)
        (velocityMode p)
        (frequencyCurlMultiplier (transportedFrequencyAt k p)
          (velocityMode (transportedFrequencyAt k p)))
  have hpairPoint : ∀ p ∈ aperture,
      source p + source (transportedFrequencyAt k p) =
        balance p + balance (transportedFrequencyAt k p) := by
    intro p _hp
    have h := neg_frequencyCurlMultiplier_exchanged_interactions
      p (transportedFrequencyAt k p) (velocityMode p)
      (velocityMode (transportedFrequencyAt k p))
      (hdivergence p) (hdivergence (transportedFrequencyAt k p))
    rw [advecting_add_transportedFrequencyAt] at h
    calc
      source p + source (transportedFrequencyAt k p) =
          -frequencyCurlMultiplier k
            (complexAdvectiveInteraction p (transportedFrequencyAt k p)
                (velocityMode p) (velocityMode (transportedFrequencyAt k p)) +
              complexAdvectiveInteraction (transportedFrequencyAt k p) p
                (velocityMode (transportedFrequencyAt k p)) (velocityMode p)) := by
        simp [source, frequencyCurlMultiplier, complexCross, map_add, smul_add]
        abel
      _ =
          (complexAdvectiveInteraction p (transportedFrequencyAt k p)
              (frequencyCurlMultiplier p (velocityMode p))
              (velocityMode (transportedFrequencyAt k p)) +
            complexAdvectiveInteraction (transportedFrequencyAt k p) p
              (frequencyCurlMultiplier (transportedFrequencyAt k p)
                (velocityMode (transportedFrequencyAt k p))) (velocityMode p)) -
          (complexAdvectiveInteraction p (transportedFrequencyAt k p)
              (velocityMode p)
              (frequencyCurlMultiplier (transportedFrequencyAt k p)
                (velocityMode (transportedFrequencyAt k p))) +
            complexAdvectiveInteraction (transportedFrequencyAt k p) p
              (velocityMode (transportedFrequencyAt k p))
              (frequencyCurlMultiplier p (velocityMode p))) := h
      _ = balance p + balance (transportedFrequencyAt k p) := by
        simp only [balance, transportedFrequencyAt_involutive]
        abel
  have hpairSum :
      (∑ p ∈ aperture,
        (source p + source (transportedFrequencyAt k p))) =
      ∑ p ∈ aperture,
        (balance p + balance (transportedFrequencyAt k p)) := by
    exact Finset.sum_congr rfl hpairPoint
  have hsourceSwap := sum_transportEquiv_eq k aperture hpaired source
  have hbalanceSwap := sum_transportEquiv_eq k aperture hpaired balance
  have htwice :
      (2 : ℕ) • (∑ p ∈ aperture, source p) =
        (2 : ℕ) • (∑ p ∈ aperture, balance p) := by
    have hpairsNormalized :
        (∑ p ∈ aperture, source p) + (∑ p ∈ aperture, source p) =
          (∑ p ∈ aperture, balance p) + (∑ p ∈ aperture, balance p) := by
      simpa only [Finset.sum_add_distrib, hsourceSwap, hbalanceSwap] using hpairSum
    simpa only [two_nsmul] using hpairsNormalized
  have hsum :
      (∑ p ∈ aperture, source p) = ∑ p ∈ aperture, balance p :=
    nsmul_right_injective (by norm_num : (2 : ℕ) ≠ 0) htwice
  simpa [source, balance, finiteAdvectiveCoefficient,
    Finset.sum_sub_distrib, frequencyCurlMultiplier, complexCross,
    map_sum, Finset.smul_sum, Finset.sum_neg_distrib] using hsum

/-! ## Identification on an admitted open solution -/

/-- Every actual strict-interior velocity coefficient is longitudinally divergence-free. -/
theorem openPeriodicVelocityFourierMode_divergenceFree
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    complexDot (complexFrequencyVector k)
      (openPeriodicVelocityFourierMode solution t k) = 0 := by
  exact complexDot_vectorSpatialFourierCoeff_eq_zero_of_divergenceFree
    (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
    (fun x ↦ solution.incompressible x t.1 ⟨t.2.1.le, t.2.2⟩) k

/-- The complete `H³` carrier and the actual-solution Fourier owner have literally the same
mode population.  This makes the finite interaction below a genuine finite aperture of the
already-founded complete convolution rather than a parallel coefficient model. -/
theorem openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (component : Fin 3) (k : SpatialFrequency) :
    (openVelocityH3State solution t component).1 k =
      openPeriodicVelocityFourierMode solution t k component := by
  unfold openVelocityH3State smoothSliceH3State
  rw [smoothSliceSobolevCoefficients, smoothSliceFourierL2_apply]
  rfl

/-- The complete endpoint of the same actual coefficient population is the existing nonlinear
vorticity source.  No finite-aperture convergence assertion is needed or made here. -/
theorem vorticityNonlinearMode_eq_completeActualAdvectionConvolution
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    vorticityNonlinearMode solution t k =
      -frequencyCurlMultiplier k
        (vectorCoefficientAt
          (h3AdvectiveConvolution (openVelocityH3State solution t)
            (openVelocityH3State solution t)) k) :=
  vorticityNonlinearMode_eq_h3AdvectiveConvolution solution t k

/-- The actual nonlinear vorticity source truncated on one finite advecting aperture. -/
def finiteOpenVorticityNonlinearCoefficient
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) : ComplexVector :=
  -frequencyCurlMultiplier k
    (finiteAdvectiveCoefficient aperture
      (openPeriodicVelocityFourierMode solution t)
      (openPeriodicVelocityFourierMode solution t) k)

/-- On a pair-symmetric aperture the finite actual nonlinear source is literally stretching
minus vorticity transport. -/
theorem finiteOpenVorticityNonlinearCoefficient_eq_stretching_sub_transport
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) (hpaired : IsTransportPairedAperture k aperture) :
    finiteOpenVorticityNonlinearCoefficient solution t aperture k =
      finiteAdvectiveCoefficient aperture
          (openPeriodicVorticityFourierMode solution t)
          (openPeriodicVelocityFourierMode solution t) k -
        finiteAdvectiveCoefficient aperture
          (openPeriodicVelocityFourierMode solution t)
          (openPeriodicVorticityFourierMode solution t) k := by
  have hvorticity :
      (fun p ↦ frequencyCurlMultiplier p
        (openPeriodicVelocityFourierMode solution t p)) =
        openPeriodicVorticityFourierMode solution t := by
    funext p
    exact (openPeriodicSolutionOn_vorticityFourierMode_eq_frequencyCurlMultiplier
      solution t p).symm
  rw [finiteOpenVorticityNonlinearCoefficient, ← hvorticity]
  exact neg_frequencyCurlMultiplier_finiteAdvectiveCoefficient_eq
    k aperture hpaired (openPeriodicVelocityFourierMode solution t)
      (openPeriodicVelocityFourierMode_divergenceFree solution t)

/-- **Exact corrected localized-flux identity.** The finite receiver
`-[P_j,u·∇]ω + P_j(ω·∇u)` equals the projected finite nonlinear source plus the coefficient
`u·∇P_jω` moved to the left side of the localized vorticity equation. -/
theorem finiteOpenVorticityFluxCoefficient_eq_projectedSource_add_transport
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) (hpaired : IsTransportPairedAperture k aperture) :
    finiteOpenVorticityFluxCoefficient solution t scale aperture k =
      (dyadicHodgeBandWeight scale k : ℂ) •
          finiteOpenVorticityNonlinearCoefficient solution t aperture k +
        finiteAdvectiveCoefficient aperture
          (openPeriodicVelocityFourierMode solution t)
          (multiplierFilter (dyadicHodgeBandMultiplier scale)
            (openPeriodicVorticityFourierMode solution t)) k := by
  rw [finiteOpenVorticityFluxCoefficient,
    finiteOpenVorticityTransportCommutatorCoefficient,
    finiteOpenVorticityStretchingBandCoefficient,
    finiteDyadicFlowCommutatorCoefficient,
    finiteMultiplierFlowCommutatorCoefficient,
    finiteOpenVorticityNonlinearCoefficient_eq_stretching_sub_transport
      solution t aperture k hpaired]
  change
    -(dyadicHodgeBandMultiplier scale k •
          finiteAdvectiveCoefficient aperture
            (openPeriodicVelocityFourierMode solution t)
            (openPeriodicVorticityFourierMode solution t) k -
        finiteAdvectiveCoefficient aperture
          (openPeriodicVelocityFourierMode solution t)
          (multiplierFilter (dyadicHodgeBandMultiplier scale)
            (openPeriodicVorticityFourierMode solution t)) k) +
      dyadicHodgeBandMultiplier scale k •
        finiteAdvectiveCoefficient aperture
          (openPeriodicVorticityFourierMode solution t)
          (openPeriodicVelocityFourierMode solution t) k =
    dyadicHodgeBandMultiplier scale k •
        (finiteAdvectiveCoefficient aperture
            (openPeriodicVorticityFourierMode solution t)
            (openPeriodicVelocityFourierMode solution t) k -
          finiteAdvectiveCoefficient aperture
            (openPeriodicVelocityFourierMode solution t)
            (openPeriodicVorticityFourierMode solution t) k) +
      finiteAdvectiveCoefficient aperture
        (openPeriodicVelocityFourierMode solution t)
        (multiplierFilter (dyadicHodgeBandMultiplier scale)
          (openPeriodicVorticityFourierMode solution t)) k
  rw [smul_sub]
  abel

/-- The paired completion supplies the preceding exact identity for every original finite
aperture, while cofinally retaining all of its pins. -/
theorem finiteOpenVorticityFluxCoefficient_pairedCompletion
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (scale : ℕ) (aperture : Finset SpatialFrequency)
    (k : SpatialFrequency) :
    finiteOpenVorticityFluxCoefficient solution t scale
        (pairedFrequencyAperture k aperture) k =
      (dyadicHodgeBandWeight scale k : ℂ) •
          finiteOpenVorticityNonlinearCoefficient solution t
            (pairedFrequencyAperture k aperture) k +
        finiteAdvectiveCoefficient (pairedFrequencyAperture k aperture)
          (openPeriodicVelocityFourierMode solution t)
          (multiplierFilter (dyadicHodgeBandMultiplier scale)
            (openPeriodicVorticityFourierMode solution t)) k :=
  finiteOpenVorticityFluxCoefficient_eq_projectedSource_add_transport
    solution t scale (pairedFrequencyAperture k aperture) k
      (pairedFrequencyAperture_isTransportPaired k aperture)

section Audit

#print axioms neg_frequencyCurlMultiplier_finiteAdvectiveCoefficient_eq
#print axioms finiteOpenVorticityNonlinearCoefficient_eq_stretching_sub_transport
#print axioms finiteOpenVorticityFluxCoefficient_eq_projectedSource_add_transport
#print axioms finiteOpenVorticityFluxCoefficient_pairedCompletion
#print axioms openVelocityH3State_mode_eq_openPeriodicVelocityFourierMode
#print axioms vorticityNonlinearMode_eq_completeActualAdvectionConvolution

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicVorticityFluxConvolutionBridge
