import ElementaryHolonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
import ElementaryHolonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
import ElementaryHolonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/-!
# The critical vorticity receiver carried by the actual clocked mild passage

**[proved-derived]** This module joins the genuine open-solution vorticity coefficients, their
exact compact-interior mild identity, the native weighted `H3` realization of every actual source
slice, and the sharp one-derivative `H2` heat receiver.  The nonlinear history is kept first as a
complete six-occurrence curl population.  Every strictly positive elapsed face of that population
is then bounded by the locally integrable spectral-clock kernel times the square of the actual
weighted `H3` state.

The public objects retain the heat clock, the curl reconstruction incidence, and the actual source
state.  No circumference coordinate or closed-form clock realization occurs in a public theorem.
The result does not assert that the resulting quadratic `H3` history is uniformly or terminally
integrable.
-/

noncomputable section

open MeasureTheory Set
open scoped BigOperators ENNReal NNReal Interval

namespace Soma.Holonics.Millennium.NavierStokesCriticalMildReceiver

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesOpenFourierMildIdentity
open Soma.Holonics.Millennium.NavierStokesOpenFourierModeEvolution
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesOpenSharpNonlinearSourceIntegration
open Soma.Holonics.Millennium.NavierStokesSharpNonlinearSource
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesSharpHeatDerivative
open Soma.Holonics.Millennium.NavierStokesSharpVorticitySourceHeatBound
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert

/-! ## Receiver algebra -/

theorem complexVectorL1_add_le (a b : ComplexVector) :
    complexVectorL1 (a + b) ≤ complexVectorL1 a + complexVectorL1 b := by
  have h0 := norm_add_le (a 0) (b 0)
  have h1 := norm_add_le (a 1) (b 1)
  have h2 := norm_add_le (a 2) (b 2)
  unfold complexVectorL1
  change ‖a 0 + b 0‖ + ‖a 1 + b 1‖ + ‖a 2 + b 2‖ ≤ _
  linarith

@[simp]
theorem complexVectorL1_neg (a : ComplexVector) :
    complexVectorL1 (-a) = complexVectorL1 a := by
  simp [complexVectorL1]

theorem complexVectorL1_intervalIntegral_le
    {f : ℝ → ComplexVector} {s t : ℝ} (hst : s ≤ t)
    (hf : Continuous f) :
    complexVectorL1 (∫ τ in s..t, f τ) ≤
      ∫ τ in s..t, complexVectorL1 (f τ) := by
  have hcomponent (component : Fin 3) :
      ‖(∫ τ in s..t, f τ) component‖ ≤
        ∫ τ in s..t, ‖f τ component‖ := by
    let evaluation : ComplexVector →L[ℂ] ℂ :=
      ContinuousLinearMap.proj component
    change ‖evaluation (∫ τ in s..t, f τ)‖ ≤
      ∫ τ in s..t, ‖evaluation (f τ)‖
    rw [← evaluation.intervalIntegral_comp_comm (hf.intervalIntegrable s t)]
    exact intervalIntegral.norm_integral_le_of_norm_le hst
      (Filter.Eventually.of_forall fun _ _ ↦ le_rfl)
      ((evaluation.continuous.comp hf).norm.intervalIntegrable s t)
  have h0 := hcomponent 0
  have h1 := hcomponent 1
  have h2 := hcomponent 2
  unfold complexVectorL1
  let a : ℝ → ℝ := fun τ ↦ ‖f τ 0‖
  let b : ℝ → ℝ := fun τ ↦ ‖f τ 1‖
  let c : ℝ → ℝ := fun τ ↦ ‖f τ 2‖
  have ha : IntervalIntegrable a volume s t := by
    exact ((ContinuousLinearMap.proj (R := ℂ) 0).continuous.comp hf).norm.intervalIntegrable s t
  have hb : IntervalIntegrable b volume s t := by
    exact ((ContinuousLinearMap.proj (R := ℂ) 1).continuous.comp hf).norm.intervalIntegrable s t
  have hc : IntervalIntegrable c volume s t := by
    exact ((ContinuousLinearMap.proj (R := ℂ) 2).continuous.comp hf).norm.intervalIntegrable s t
  have hsplit : (∫ τ in s..t, a τ + b τ + c τ) =
      (∫ τ in s..t, a τ) + (∫ τ in s..t, b τ) +
        ∫ τ in s..t, c τ := by
    calc
      (∫ τ in s..t, a τ + b τ + c τ) =
          (∫ τ in s..t, a τ + b τ) + ∫ τ in s..t, c τ := by
        exact intervalIntegral.integral_add (ha.add hb) hc
      _ = _ := by rw [intervalIntegral.integral_add ha hb]
  change _ ≤ ∫ τ in s..t, a τ + b τ + c τ
  rw [hsplit]
  linarith

/-! ## Exact source-to-clock identification -/

/-- One heat-transported sharp source coefficient, retained as its six oriented curl
occurrences. -/
def openPeriodicSharpSourceClockedCurlOccurrenceMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : ℝ) (sourceTime : Ioo 0 T) : ℝ :=
  heatTransportedH2SourceCurlOccurrenceMass nu (t - sourceTime.1)
    (sharpNonlinearSource (openVelocityWeightedH3State solution sourceTime))

/-- On the addressed mild interval, the compact nonlinear mode is literally the negative curl
of the heat-clocked native sharp source coefficient. -/
theorem compactStokesTransportedVorticityNonlinearMode_eq_sharpClockedCurl
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) {τ : ℝ} (hτ : τ ∈ Icc s t) :
    compactStokesTransportedVorticityNonlinearMode
        solution hs hst ht k τ =
      -heatTransportedH2SourceCurlCoefficient nu (t - τ)
        (sharpNonlinearSource
          (openVelocityWeightedH3State solution
            ⟨τ, hs.trans_le hτ.1, hτ.2.trans_lt ht⟩)) k := by
  let τi : Ioo (0 : ℝ) T :=
    ⟨τ, hs.trans_le hτ.1, hτ.2.trans_lt ht⟩
  let source := sharpNonlinearSource (openVelocityWeightedH3State solution τi)
  let coefficient := unweightedSharpNonlinearSourceCoefficient
    (openVelocityWeightedH3State solution τi) k
  have hcoefficient :
      heatTransportedH2SourceCoefficient nu (t - τ) source k =
        heatStokesMultiplier nu (t - τ) k • coefficient := by
    ext component
    rfl
  rw [compactStokesTransportedVorticityNonlinearMode,
    compactVorticityNonlinearMode_eq_actual solution hs hst ht k hτ,
    vorticityNonlinearMode_eq_unweightedSharpNonlinearSourceCoefficient]
  change heatStokesMultiplier nu (t - τ) k •
      (-frequencyCurlMultiplierRealCLM k coefficient) =
    -frequencyCurlMultiplierRealCLM k
      (heatTransportedH2SourceCoefficient nu (t - τ) source k)
  rw [hcoefficient, map_smul]
  simp

/-- At positive elapsed time, the complete actual transported source population is bounded by
the retained six-occurrence reconstruction fibre. -/
theorem tsum_complexVectorL1_compactStokesTransportedVorticityNonlinearMode_le_occurrenceMass
    {T nu s t τ : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (hτ : τ ∈ Ico s t) :
    (∑' k : SpatialFrequency,
      complexVectorL1
        (compactStokesTransportedVorticityNonlinearMode
          solution hs hst ht k τ)) ≤
      openPeriodicSharpSourceClockedCurlOccurrenceMass solution t
        ⟨τ, hs.trans_le hτ.1, hτ.2.trans ht⟩ := by
  let τi : Ioo 0 T := ⟨τ, hs.trans_le hτ.1, hτ.2.trans ht⟩
  have helapsed : 0 < nu * (t - τ) := mul_pos hnu (sub_pos.mpr hτ.2)
  have hright := summable_heatTransportedH2SourceCurlEntryMass
    nu (t - τ) helapsed
      (sharpNonlinearSource (openVelocityWeightedH3State solution τi))
  have hleft : Summable fun k : SpatialFrequency ↦
      complexVectorL1
        (compactStokesTransportedVorticityNonlinearMode
          solution hs hst ht k τ) := by
    refine Summable.of_nonneg_of_le (fun k ↦ complexVectorL1_nonneg _) ?_ hright
    intro k
    rw [compactStokesTransportedVorticityNonlinearMode_eq_sharpClockedCurl
      solution hs hst ht k ⟨hτ.1, hτ.2.le⟩,
      complexVectorL1_neg,
      heatTransportedH2SourceCurlCoefficient_eq_complexCurl]
    exact complexVectorL1_complexCurlFromJacobian_le _
  apply Summable.tsum_le_tsum
  · intro k
    rw [compactStokesTransportedVorticityNonlinearMode_eq_sharpClockedCurl
      solution hs hst ht k ⟨hτ.1, hτ.2.le⟩,
      complexVectorL1_neg]
    rw [heatTransportedH2SourceCurlCoefficient_eq_complexCurl]
    exact complexVectorL1_complexCurlFromJacobian_le _
  · exact hleft
  · exact hright

/-! ## The complete positive-elapsed nonlinear service law -/

/-- Named locally integrable clock scale emitted by one recovered spatial derivative. -/
def clockedFirstDerivativeH2ServiceKernel (nu elapsed : ℝ) : ℝ :=
  (2 * (nu * elapsed)) ^ (-1 / 4 : ℝ)

/-- The named positive-elapsed clock kernel is locally integrable for every positive viscosity. -/
theorem integrableOn_clockedFirstDerivativeH2ServiceKernel
    (nu horizon : ℝ) (hnu : 0 < nu) (hhorizon : 0 < horizon) :
    IntegrableOn (clockedFirstDerivativeH2ServiceKernel nu) (Ioo 0 horizon) := by
  have hbase : IntegrableOn (fun dt : ℝ ↦ dt ^ (-1 / 4 : ℝ)) (Ioo 0 horizon) :=
    (intervalIntegral.integrableOn_Ioo_rpow_iff hhorizon).2 (by norm_num)
  let scale : ℝ := (2 * nu) ^ (-1 / 4 : ℝ)
  have hscaled := hbase.const_mul scale
  refine IntegrableOn.congr_fun hscaled ?_ measurableSet_Ioo
  intro dt hdt
  unfold clockedFirstDerivativeH2ServiceKernel
  dsimp [scale]
  rw [show 2 * (nu * dt) = (2 * nu) * dt by ring,
    Real.mul_rpow (by positivity) hdt.1.le]

/-- Every positive-elapsed actual source face is quadratically controlled by the actual native
weighted `H3` slice which caused it. -/
theorem openPeriodicSharpSourceClockedCurlOccurrenceMass_le
    {T nu t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (sourceTime : Ioo 0 T)
    (hnuElapsed : 0 < nu * (t - sourceTime.1))
    (hlocal : 2 * (nu * (t - sourceTime.1)) ≤ 1) :
    openPeriodicSharpSourceClockedCurlOccurrenceMass solution t sourceTime ≤
      6 * sharpHeatFirstDerivativeH2Constant *
        clockedFirstDerivativeH2ServiceKernel nu (t - sourceTime.1) *
          ((23328 * periodicH3EmbeddingConstant) *
            ‖openVelocityWeightedH3State solution sourceTime‖ ^ 2) := by
  have hbound := heatTransportedH2SourceCurlOccurrenceMass_le
    nu (t - sourceTime.1) hnuElapsed hlocal
      (sharpNonlinearSource (openVelocityWeightedH3State solution sourceTime))
  have hsource := norm_sharpNonlinearSource_le
    (openVelocityWeightedH3State solution sourceTime)
  have hfactor : 0 ≤ 6 * (sharpHeatFirstDerivativeH2Constant *
      (2 * (nu * (t - sourceTime.1))) ^ (-1 / 4 : ℝ)) := by
    have hconstant : 0 ≤ sharpHeatFirstDerivativeH2Constant := by
      unfold sharpHeatFirstDerivativeH2Constant sharpHeatSecondDerivativeH3Constant
      positivity
    exact mul_nonneg (by norm_num)
      (mul_nonneg hconstant (Real.rpow_nonneg (by positivity) _))
  unfold openPeriodicSharpSourceClockedCurlOccurrenceMass
    clockedFirstDerivativeH2ServiceKernel
  exact hbound.trans (by
    have := mul_le_mul_of_nonneg_left hsource hfactor
    simpa only [mul_assoc] using this)

/-! ## Exact finite-aperture mild receiver -/

/-- The clocked initial vorticity population retained by a finite receiver aperture. -/
def finiteClockedInitialVorticityCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (s : Ioo 0 T) (t : ℝ) (modes : Finset SpatialFrequency) : ℝ :=
  ∑ k ∈ modes,
    complexVectorL1
      (heatStokesMultiplier nu (t - s.1) k •
        openPeriodicVorticityFourierMode solution s k)

/-- The actual vorticity coefficient mass seen through one finite addressed aperture. -/
def finiteOpenPeriodicVorticityCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) : ℝ :=
  ∑ k ∈ modes, complexVectorL1 (openPeriodicVorticityFourierMode solution t k)

/-- The complete compact-interior nonlinear history seen by one finite aperture. -/
def finiteClockedVorticitySourceHistoryMass
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (modes : Finset SpatialFrequency) (τ : ℝ) : ℝ :=
  ∑ k ∈ modes,
    complexVectorL1
      (compactStokesTransportedVorticityNonlinearMode
        solution hs hst ht k τ)

theorem continuous_finiteClockedVorticitySourceHistoryMass
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (modes : Finset SpatialFrequency) :
    Continuous
      (finiteClockedVorticitySourceHistoryMass solution hs hst ht modes) := by
  unfold finiteClockedVorticitySourceHistoryMass complexVectorL1
  apply continuous_finsetSum modes
  intro k _hk
  have hmode := continuous_compactStokesTransportedVorticityNonlinearMode
    solution hs hst ht k
  exact (((Continuous.norm
      ((ContinuousLinearMap.proj (R := ℂ) 0).continuous.comp hmode)).add
    (Continuous.norm
      ((ContinuousLinearMap.proj (R := ℂ) 1).continuous.comp hmode))).add
      (Continuous.norm
        ((ContinuousLinearMap.proj (R := ℂ) 2).continuous.comp hmode)))

/-- The exact mild identity gives one coefficientwise `L1` service inequality while retaining
the full clocked source history of that coefficient. -/
theorem complexVectorL1_openPeriodicVorticityFourierMode_le_clockedMildHistory
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (k : SpatialFrequency) :
    complexVectorL1
        (openPeriodicVorticityFourierMode solution
          ⟨t, hs.trans_le hst, ht⟩ k) ≤
      complexVectorL1
          (heatStokesMultiplier nu (t - s) k •
            openPeriodicVorticityFourierMode solution
              ⟨s, hs, hst.trans_lt ht⟩ k) +
        ∫ τ in s..t,
          complexVectorL1
            (compactStokesTransportedVorticityNonlinearMode
              solution hs hst ht k τ) := by
  rw [← frequencyCurlMultiplier_velocityMode_eq_openPeriodicVorticityFourierMode
    solution ⟨t, hs.trans_le hst, ht⟩ k]
  rw [openPeriodicSolutionOn_vorticityMode_mild_identity solution hs hst ht k]
  apply (complexVectorL1_add_le _ _).trans
  rw [frequencyCurlMultiplier_velocityMode_eq_openPeriodicVorticityFourierMode
    solution ⟨s, hs, hst.trans_lt ht⟩ k]
  apply add_le_add le_rfl
  exact complexVectorL1_intervalIntegral_le hst
    (continuous_compactStokesTransportedVorticityNonlinearMode
      solution hs hst ht k)

/-- **Exact finite-aperture clocked mild receiver.**  Every finite family of actual final-time
vorticity coefficients is paid by its exact clocked initial population and the complete compact
nonlinear history through that same aperture.  No source-time coefficient or reconstruction fibre
is discarded. -/
theorem finiteOpenPeriodicVorticityCoefficientMass_le_clockedMildHistory
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (modes : Finset SpatialFrequency) :
    finiteOpenPeriodicVorticityCoefficientMass solution
        ⟨t, hs.trans_le hst, ht⟩ modes ≤
      finiteClockedInitialVorticityCoefficientMass solution
          ⟨s, hs, hst.trans_lt ht⟩ t modes +
        ∫ τ in s..t,
          finiteClockedVorticitySourceHistoryMass
            solution hs hst ht modes τ := by
  unfold finiteOpenPeriodicVorticityCoefficientMass
    finiteClockedInitialVorticityCoefficientMass
  have hsum := Finset.sum_le_sum (s := modes)
    (fun k _hk ↦
      complexVectorL1_openPeriodicVorticityFourierMode_le_clockedMildHistory
        solution hs hst ht k)
  calc
    (∑ k ∈ modes,
        complexVectorL1
          (openPeriodicVorticityFourierMode solution ⟨t, hs.trans_le hst, ht⟩ k)) ≤
        ∑ k ∈ modes,
          (complexVectorL1
              (heatStokesMultiplier nu (t - s) k •
                openPeriodicVorticityFourierMode solution
                  ⟨s, hs, hst.trans_lt ht⟩ k) +
            ∫ τ in s..t,
              complexVectorL1
                (compactStokesTransportedVorticityNonlinearMode
                  solution hs hst ht k τ)) := hsum
    _ = (∑ k ∈ modes,
          complexVectorL1
            (heatStokesMultiplier nu (t - s) k •
              openPeriodicVorticityFourierMode solution
                ⟨s, hs, hst.trans_lt ht⟩ k)) +
        ∑ k ∈ modes, ∫ τ in s..t,
          complexVectorL1
            (compactStokesTransportedVorticityNonlinearMode
              solution hs hst ht k τ) := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      unfold finiteClockedVorticitySourceHistoryMass
      have hint : ∀ k ∈ modes, IntervalIntegrable
          (fun τ ↦ complexVectorL1
            (compactStokesTransportedVorticityNonlinearMode
              solution hs hst ht k τ)) volume s t := by
        intro k _hk
        unfold complexVectorL1
        have hmode := continuous_compactStokesTransportedVorticityNonlinearMode
          solution hs hst ht k
        exact (((Continuous.norm
            ((ContinuousLinearMap.proj (R := ℂ) 0).continuous.comp hmode)).add
          (Continuous.norm
            ((ContinuousLinearMap.proj (R := ℂ) 1).continuous.comp hmode))).add
          (Continuous.norm
            ((ContinuousLinearMap.proj (R := ℂ) 2).continuous.comp hmode))).intervalIntegrable s t
      rw [← intervalIntegral.integral_finsetSum hint]

/-- On every strict source-time face, the finite nonlinear history factors through the same
complete six-occurrence sharp-source population, independently of the aperture. -/
theorem finiteClockedVorticitySourceHistoryMass_le_occurrenceMass
    {T nu s t τ : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (modes : Finset SpatialFrequency) (hτ : τ ∈ Ico s t) :
    finiteClockedVorticitySourceHistoryMass solution hs hst ht modes τ ≤
      openPeriodicSharpSourceClockedCurlOccurrenceMass solution t
        ⟨τ, hs.trans_le hτ.1, hτ.2.trans ht⟩ := by
  unfold finiteClockedVorticitySourceHistoryMass
  have hsum :=
    tsum_complexVectorL1_compactStokesTransportedVorticityNonlinearMode_le_occurrenceMass
      solution hnu hs hst ht hτ
  let τi : Ioo 0 T := ⟨τ, hs.trans_le hτ.1, hτ.2.trans ht⟩
  have helapsed : 0 < nu * (t - τ) := mul_pos hnu (sub_pos.mpr hτ.2)
  have hright := summable_heatTransportedH2SourceCurlEntryMass
    nu (t - τ) helapsed
      (sharpNonlinearSource (openVelocityWeightedH3State solution τi))
  have hsourceSummable : Summable fun k : SpatialFrequency ↦
      complexVectorL1
        (compactStokesTransportedVorticityNonlinearMode
          solution hs hst ht k τ) := by
    refine Summable.of_nonneg_of_le (fun k ↦ complexVectorL1_nonneg _) ?_ hright
    intro k
    rw [compactStokesTransportedVorticityNonlinearMode_eq_sharpClockedCurl
      solution hs hst ht k ⟨hτ.1, hτ.2.le⟩,
      complexVectorL1_neg,
      heatTransportedH2SourceCurlCoefficient_eq_complexCurl]
    exact complexVectorL1_complexCurlFromJacobian_le _
  exact (hsourceSummable.sum_le_tsum modes
    (fun _ _ ↦ complexVectorL1_nonneg _)).trans hsum

/-- The exact finite-aperture history is therefore controlled, at every strict source-time face,
by the locally integrable clock kernel and the square of the actual weighted `H3` slice. -/
theorem finiteClockedVorticitySourceHistoryMass_le_actualH3ClockService
    {T nu s t τ : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (hlocal : 2 * (nu * (t - s)) ≤ 1)
    (modes : Finset SpatialFrequency) (hτ : τ ∈ Ico s t) :
    finiteClockedVorticitySourceHistoryMass solution hs hst ht modes τ ≤
      6 * sharpHeatFirstDerivativeH2Constant *
        clockedFirstDerivativeH2ServiceKernel nu (t - τ) *
          ((23328 * periodicH3EmbeddingConstant) *
            ‖openVelocityWeightedH3State solution
              ⟨τ, hs.trans_le hτ.1, hτ.2.trans ht⟩‖ ^ 2) := by
  have hnuElapsed : 0 < nu * (t - τ) :=
    mul_pos hnu (sub_pos.mpr hτ.2)
  have hlocalτ : 2 * (nu * (t - τ)) ≤ 1 := by
    have hstep : 2 * (nu * (t - τ)) ≤ 2 * (nu * (t - s)) := by
      calc
        2 * (nu * (t - τ)) = (2 * nu) * (t - τ) := by ring
        _ ≤ (2 * nu) * (t - s) :=
          mul_le_mul_of_nonneg_left (sub_le_sub_left hτ.1 t)
            (mul_nonneg (by norm_num) hnu.le)
        _ = 2 * (nu * (t - s)) := by ring
    exact hstep.trans hlocal
  exact (finiteClockedVorticitySourceHistoryMass_le_occurrenceMass
    solution hnu hs hst ht modes hτ).trans
      (openPeriodicSharpSourceClockedCurlOccurrenceMass_le
        solution ⟨τ, hs.trans_le hτ.1, hτ.2.trans ht⟩ hnuElapsed hlocalτ)

/-! ## Complete coefficient population and its exact extended history -/

theorem complexVectorL1_real_smul (r : ℝ) (v : ComplexVector) :
    complexVectorL1 (r • v) = |r| * complexVectorL1 v := by
  unfold complexVectorL1
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
  ring

/-- Complete clocked initial population.  Unlike an unlabelled numerical bound, this receiver
retains the actual heat-clock action at every lattice address. -/
def fullClockedInitialVorticityCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (s : Ioo 0 T) (t : ℝ) : ℝ :=
  ∑' k : SpatialFrequency,
    complexVectorL1
      (heatStokesMultiplier nu (t - s.1) k •
        openPeriodicVorticityFourierMode solution s k)

theorem summable_fullClockedInitialVorticityCoefficientMass
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (s : Ioo 0 T) {t : ℝ} (hst : s.1 ≤ t) :
    Summable fun k : SpatialFrequency ↦
      complexVectorL1
        (heatStokesMultiplier nu (t - s.1) k •
          openPeriodicVorticityFourierMode solution s k) := by
  have hsource :=
    summable_complexVectorL1_openPeriodicVorticityFourierMode solution s
  refine Summable.of_nonneg_of_le (fun k ↦ complexVectorL1_nonneg _) ?_ hsource
  intro k
  have hclockNonneg : 0 ≤ heatStokesMultiplier nu (t - s.1) k := by
    unfold heatStokesMultiplier
    positivity
  have hclockLe : heatStokesMultiplier nu (t - s.1) k ≤ 1 := by
    unfold heatStokesMultiplier
    rw [Real.exp_le_one_iff]
    exact neg_nonpos.mpr (mul_nonneg
      (mul_nonneg hnu (sub_nonneg.mpr hst)) (torusStokesEigenvalue_nonneg k))
  rw [complexVectorL1_real_smul, abs_of_nonneg hclockNonneg]
  exact mul_le_of_le_one_left (complexVectorL1_nonneg _) hclockLe

/-- The complete reconstruction fibre of the extended nonnegative time-history receiver.  It is
the supremum of the literal interval integrals returned by all finite lattice apertures; thus no
enumeration or convergence claim is hidden in its definition.  Finiteness is deliberately not
built in. -/
def completeClockedVorticitySourceHistoryIntegral
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T) : ℝ≥0∞ :=
  ⨆ modes : Finset SpatialFrequency,
    ENNReal.ofReal
      (∫ τ in s..t,
        finiteClockedVorticitySourceHistoryMass
          solution hs hst ht modes τ)

theorem finiteClockedVorticitySourceHistoryIntegral_le_complete
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (modes : Finset SpatialFrequency) :
    ENNReal.ofReal
        (∫ τ in s..t,
          finiteClockedVorticitySourceHistoryMass
            solution hs hst ht modes τ) ≤
      completeClockedVorticitySourceHistoryIntegral solution hs hst ht := by
  exact le_iSup (fun aperture : Finset SpatialFrequency ↦
    ENNReal.ofReal
      (∫ τ in s..t,
        finiteClockedVorticitySourceHistoryMass
          solution hs hst ht aperture τ)) modes

/-- **Complete exact clocked mild receiver.**  The full actual final-time vorticity coefficient
mass crosses the compact mild identity without a cutoff.  Its entire source-history reconstruction
fibre is retained as the supremum of the literal finite-aperture time integrals.  This unconditional
theorem does not assert that the extended history is below `∞`; that is precisely the terminal
service obligation, so this result supplies no terminal control claim. -/
theorem ofReal_openPeriodicFullVorticityCoefficientMass_le_completeClockedMildHistory
    {T nu s t : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 ≤ nu) (hs : 0 < s) (hst : s ≤ t) (ht : t < T) :
    ENNReal.ofReal
        (openPeriodicFullVorticityCoefficientMass solution
          ⟨t, hs.trans_le hst, ht⟩) ≤
      ENNReal.ofReal
          (fullClockedInitialVorticityCoefficientMass solution
            ⟨s, hs, hst.trans_lt ht⟩ t) +
        completeClockedVorticitySourceHistoryIntegral solution hs hst ht := by
  let finalTime : Ioo 0 T := ⟨t, hs.trans_le hst, ht⟩
  let sourceTime : Ioo 0 T := ⟨s, hs, hst.trans_lt ht⟩
  let finalTerm : SpatialFrequency → ℝ := fun k ↦
    complexVectorL1 (openPeriodicVorticityFourierMode solution finalTime k)
  let initialTerm : SpatialFrequency → ℝ := fun k ↦
    complexVectorL1
      (heatStokesMultiplier nu (t - s) k •
        openPeriodicVorticityFourierMode solution sourceTime k)
  have hfinalSummable : Summable finalTerm := by
    exact summable_complexVectorL1_openPeriodicVorticityFourierMode solution finalTime
  have hinitialSummable : Summable initialTerm := by
    exact summable_fullClockedInitialVorticityCoefficientMass
      solution hnu sourceTime hst
  have hfinite (modes : Finset SpatialFrequency) :
      ∑ k ∈ modes, ENNReal.ofReal (finalTerm k) ≤
        ENNReal.ofReal
            (fullClockedInitialVorticityCoefficientMass solution sourceTime t) +
          completeClockedVorticitySourceHistoryIntegral solution hs hst ht := by
    have hmild :=
      finiteOpenPeriodicVorticityCoefficientMass_le_clockedMildHistory
        solution hs hst ht modes
    have hhistoryNonneg : 0 ≤
        ∫ τ in s..t,
          finiteClockedVorticitySourceHistoryMass
            solution hs hst ht modes τ := by
      apply intervalIntegral.integral_nonneg hst
      intro τ _hτ
      unfold finiteClockedVorticitySourceHistoryMass
      exact Finset.sum_nonneg fun _ _ ↦ complexVectorL1_nonneg _
    have hinitialFiniteNonneg : 0 ≤ ∑ k ∈ modes, initialTerm k :=
      Finset.sum_nonneg fun _ _ ↦ complexVectorL1_nonneg _
    have hfinalFiniteNonneg : 0 ≤ ∑ k ∈ modes, finalTerm k :=
      Finset.sum_nonneg fun _ _ ↦ complexVectorL1_nonneg _
    change (∑ k ∈ modes, finalTerm k) ≤
      (∑ k ∈ modes, initialTerm k) +
        ∫ τ in s..t,
          finiteClockedVorticitySourceHistoryMass
            solution hs hst ht modes τ at hmild
    have hmildENN := ENNReal.ofReal_le_ofReal hmild
    rw [ENNReal.ofReal_add hinitialFiniteNonneg hhistoryNonneg] at hmildENN
    have hinitialFinite :
        ENNReal.ofReal (∑ k ∈ modes, initialTerm k) ≤
          ENNReal.ofReal
            (fullClockedInitialVorticityCoefficientMass solution sourceTime t) := by
      apply ENNReal.ofReal_le_ofReal
      exact hinitialSummable.sum_le_tsum modes
        (fun _ _ ↦ complexVectorL1_nonneg _)
    have hhistory :=
      finiteClockedVorticitySourceHistoryIntegral_le_complete
        solution hs hst ht modes
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun k _hk ↦ complexVectorL1_nonneg _)]
    exact hmildENN.trans (add_le_add hinitialFinite hhistory)
  change ENNReal.ofReal (∑' k, finalTerm k) ≤ _
  rw [ENNReal.ofReal_tsum_of_nonneg
    (fun k ↦ complexVectorL1_nonneg _) hfinalSummable]
  exact (Summable.tsum_le_of_sum_le
    ENNReal.summable hfinite)

section Audit

#print axioms compactStokesTransportedVorticityNonlinearMode_eq_sharpClockedCurl
#print axioms openPeriodicSharpSourceClockedCurlOccurrenceMass_le
#print axioms integrableOn_clockedFirstDerivativeH2ServiceKernel
#print axioms finiteOpenPeriodicVorticityCoefficientMass_le_clockedMildHistory
#print axioms finiteClockedVorticitySourceHistoryMass_le_occurrenceMass
#print axioms finiteClockedVorticitySourceHistoryMass_le_actualH3ClockService
#print axioms ofReal_openPeriodicFullVorticityCoefficientMass_le_completeClockedMildHistory

end Audit

end Soma.Holonics.Millennium.NavierStokesCriticalMildReceiver
