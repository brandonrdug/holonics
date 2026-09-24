import ElementaryHolonics.Millennium.NavierStokesCriticalVorticityRate
import ElementaryHolonics.Millennium.NavierStokesTorusFourier
import Mathlib.Data.Pi.Interval

/-!
# Genuine finite sharp dyadic aperture projectors on the periodic three-torus

**[proved-derived]** The logarithmic continuation line needs actual Fourier populations rather
than three arbitrary real-valued placeholders called `low`, `middle`, and `high`.  This module
constructs the first such populations directly on the integer character lattice of `(R / Z)^3`.

The construction is deliberately aperture-aware.  A frequency cube and each dyadic shell are
finite.  Low, middle, and high populations reconstruct the projector through a declared outer
dyadic aperture; no theorem silently identifies that finite return with the complete infinite
Fourier series.  Haar orthogonality proves that finite synthesis is an exact coefficient
projector.  Specialization to an admitted Navier--Stokes slice then gives genuine vorticity and
Jacobian band fields, not conclusion-shaped scalar functions.

**[open]** The coefficientwise critical-vorticity bound proved below is exact, but summing it costs
the number of modes.  These projectors use sharp cube indicators, whose kernel norms can retain
aperture dependence.  The BKM continuation squeeze therefore needs a replacement by smooth
annular multipliers together with a scale-uniform periodic Calderon--Zygmund/Littlewood--Paley
kernel theorem; it is not a missing theorem about the present sharp cutoffs alone.
-/

noncomputable section

open ContDiff MeasureTheory Set
open scoped BigOperators ComplexConjugate

namespace Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesCriticalVorticityRate
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicEnstrophy
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesTorusVorticity
open Soma.Holonics.Millennium.NavierStokesVorticity

/- Keep the same probability Haar chart used by `NavierStokesTorusFourier`. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-! ## Finite frequency cubes and dyadic populations -/

/-- The genuine finite integer-frequency cube with coordinate radius `radius`. -/
def frequencyCube (radius : ℕ) : Finset SpatialFrequency :=
  Finset.Icc
    (fun _ : Fin 3 ↦ -(radius : ℤ))
    (fun _ : Fin 3 ↦ (radius : ℤ))

/-- Membership in a frequency cube is exactly the three coordinate inequalities. -/
theorem mem_frequencyCube_iff (radius : ℕ) (k : SpatialFrequency) :
    k ∈ frequencyCube radius ↔
      ∀ coordinate : Fin 3,
        -(radius : ℤ) ≤ k coordinate ∧ k coordinate ≤ (radius : ℤ) := by
  rw [frequencyCube, Finset.mem_Icc]
  constructor
  · intro hk coordinate
    exact ⟨hk.1 coordinate, hk.2 coordinate⟩
  · intro hk
    exact ⟨fun coordinate ↦ (hk coordinate).1, fun coordinate ↦ (hk coordinate).2⟩

/-- The cube really contains `(2 radius + 1)^3` integer modes. -/
theorem card_frequencyCube (radius : ℕ) :
    (frequencyCube radius).card = (2 * radius + 1) ^ 3 := by
  simp [frequencyCube, Pi.card_Icc]
  omega

/-- Enlarging the coordinate radius preserves every addressed frequency. -/
theorem frequencyCube_mono {inner outer : ℕ} (h : inner ≤ outer) :
    frequencyCube inner ⊆ frequencyCube outer := by
  intro k hk
  rw [mem_frequencyCube_iff] at hk ⊢
  have hcast : (inner : ℤ) ≤ (outer : ℤ) := by exact_mod_cast h
  intro coordinate
  exact ⟨(neg_le_neg hcast).trans (hk coordinate).1,
    (hk coordinate).2.trans hcast⟩

/-- Radius of the `level`-th dyadic cube. -/
def dyadicRadius (level : ℕ) : ℕ := 2 ^ level

/-- The finite shell between two consecutive dyadic cubes. -/
def dyadicFrequencyShell (level : ℕ) : Finset SpatialFrequency :=
  frequencyCube (dyadicRadius (level + 1)) \ frequencyCube (dyadicRadius level)

/-- Shell membership retains both its outer support and its missing inner face. -/
theorem mem_dyadicFrequencyShell_iff (level : ℕ) (k : SpatialFrequency) :
    k ∈ dyadicFrequencyShell level ↔
      k ∈ frequencyCube (dyadicRadius (level + 1)) ∧
        k ∉ frequencyCube (dyadicRadius level) := by
  simp [dyadicFrequencyShell]

/-- The unit low-frequency population. -/
def lowFrequencyModes : Finset SpatialFrequency := frequencyCube 1

/-- All finite middle modes between the unit cube and the selected dyadic depth. -/
def middleFrequencyModes (depth : ℕ) : Finset SpatialFrequency :=
  frequencyCube (dyadicRadius depth) \ lowFrequencyModes

/-- The finite high population between the selected depth and an explicitly larger aperture. -/
def highFrequencyApertureModes (depth highShells : ℕ) : Finset SpatialFrequency :=
  frequencyCube (dyadicRadius (depth + highShells)) \
    frequencyCube (dyadicRadius depth)

theorem lowFrequencyModes_subset_middleCube (depth : ℕ) :
    lowFrequencyModes ⊆ frequencyCube (dyadicRadius depth) := by
  apply frequencyCube_mono
  exact Nat.one_le_pow depth 2 (by norm_num)

theorem middleCube_subset_outerCube (depth highShells : ℕ) :
    frequencyCube (dyadicRadius depth) ⊆
      frequencyCube (dyadicRadius (depth + highShells)) := by
  apply frequencyCube_mono
  exact Nat.pow_le_pow_right (by norm_num) (Nat.le_add_right depth highShells)

/-- Low, middle, and high finite populations exactly partition the declared outer aperture. -/
theorem low_union_middle_union_high_eq_outerCube (depth highShells : ℕ) :
    (lowFrequencyModes ∪ middleFrequencyModes depth) ∪
        highFrequencyApertureModes depth highShells =
      frequencyCube (dyadicRadius (depth + highShells)) := by
  rw [show lowFrequencyModes ∪ middleFrequencyModes depth =
      frequencyCube (dyadicRadius depth) by
    exact Finset.union_sdiff_of_subset (lowFrequencyModes_subset_middleCube depth)]
  exact Finset.union_sdiff_of_subset (middleCube_subset_outerCube depth highShells)

/-! ## Exact finite Fourier synthesis -/

/-- Synthesis of a finite coefficient population on the genuine torus. -/
def finiteFourierSynthesis
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coeff : SpatialFrequency → E) (modes : Finset SpatialFrequency) :
    C(SpatialTorus, E) where
  toFun q := ∑ k ∈ modes, UnitAddTorus.mFourier k q • coeff k
  continuous_toFun := by fun_prop

/-- Probability-Haar orthogonality of two genuine torus characters. -/
theorem integral_mFourier_neg_mul_mFourier (n m : SpatialFrequency) :
    (∫ q : SpatialTorus,
      UnitAddTorus.mFourier (-n) q * UnitAddTorus.mFourier m q) =
        if n = m then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (UnitAddTorus.orthonormal_mFourier (d := Fin 3))) n m
  rw [ContinuousMap.inner_toLp (volume : Measure SpatialTorus)
    (UnitAddTorus.mFourier n) (UnitAddTorus.mFourier m)] at h
  simpa only [UnitAddTorus.mFourier_neg, mul_comm] using h

/-- **Exact projector receipt.**  A synthesized finite population has precisely its admitted
coefficient at every supported mode and zero at every unsupported mode. -/
theorem mFourierCoeff_finiteFourierSynthesis
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (coeff : SpatialFrequency → E) (modes : Finset SpatialFrequency)
    (n : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (fun q : SpatialTorus ↦ finiteFourierSynthesis coeff modes q) n =
      if n ∈ modes then coeff n else 0 := by
  classical
  rw [UnitAddTorus.mFourierCoeff]
  change (∫ q : SpatialTorus,
      UnitAddTorus.mFourier (-n) q •
        (∑ k ∈ modes, UnitAddTorus.mFourier k q • coeff k)) = _
  simp_rw [Finset.smul_sum, smul_smul]
  have hint : ∀ k ∈ modes, Integrable (fun q : SpatialTorus ↦
      (UnitAddTorus.mFourier (-n) q * UnitAddTorus.mFourier k q) • coeff k) := by
    intro k _hk
    exact continuousMap_integrable_on_compact
      { toFun := fun q : SpatialTorus ↦
          (UnitAddTorus.mFourier (-n) q * UnitAddTorus.mFourier k q) • coeff k
        continuous_toFun := by fun_prop }
  rw [integral_finset_sum modes hint]
  simp_rw [integral_smul_const, integral_mFourier_neg_mul_mFourier]
  simp

/-- Pointwise triangle bound for a genuine finite Fourier population. -/
theorem norm_finiteFourierSynthesis_le_sum_norm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coeff : SpatialFrequency → E) (modes : Finset SpatialFrequency)
    (q : SpatialTorus) :
    ‖finiteFourierSynthesis coeff modes q‖ ≤ ∑ k ∈ modes, ‖coeff k‖ := by
  unfold finiteFourierSynthesis
  calc
    ‖∑ k ∈ modes, UnitAddTorus.mFourier k q • coeff k‖ ≤
        ∑ k ∈ modes, ‖UnitAddTorus.mFourier k q • coeff k‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ modes, ‖coeff k‖ := by
      apply Finset.sum_congr rfl
      intro k _hk
      rw [norm_smul]
      simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
        fourier_apply, Circle.norm_coe, Finset.prod_const_one]
      simp only [one_mul]

/-- Synthesis respects an exact nested-population split. -/
theorem finiteFourierSynthesis_eq_add_sdiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coeff : SpatialFrequency → E) {inner outer : Finset SpatialFrequency}
    (h : inner ⊆ outer) :
    finiteFourierSynthesis coeff outer =
      finiteFourierSynthesis coeff inner +
        finiteFourierSynthesis coeff (outer \ inner) := by
  ext q
  unfold finiteFourierSynthesis
  have hsum := Finset.sum_sdiff
    (f := fun k ↦ UnitAddTorus.mFourier k q • coeff k) h
  simpa [add_comm] using hsum.symm

/-- The finite outer projector is exactly the sum of its constructed low, middle, and high
projectors. -/
theorem finiteFourierSynthesis_outerCube_eq_threeBands
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (coeff : SpatialFrequency → E) (depth highShells : ℕ) :
    finiteFourierSynthesis coeff
        (frequencyCube (dyadicRadius (depth + highShells))) =
      finiteFourierSynthesis coeff lowFrequencyModes +
        finiteFourierSynthesis coeff (middleFrequencyModes depth) +
          finiteFourierSynthesis coeff
            (highFrequencyApertureModes depth highShells) := by
  rw [finiteFourierSynthesis_eq_add_sdiff coeff
    (middleCube_subset_outerCube depth highShells)]
  rw [finiteFourierSynthesis_eq_add_sdiff coeff
    (lowFrequencyModes_subset_middleCube depth)]
  rfl

/-! ## Actual vorticity populations of an admitted solution slice -/

/-- Coordinatewise complexification of the actual descended vorticity slice. -/
def complexTorusVorticitySlice
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) : C(SpatialTorus, ComplexVector) where
  toFun q := complexifySpace (torusVorticityEvolution solution t q)
  continuous_toFun := continuous_complexifySpace.comp
    (torusVorticityEvolution solution t).continuous

/-- The Fourier coefficient used by the active solution owner is definitionally the coefficient
of the descended complex vorticity slice. -/
theorem openPeriodicVorticityFourierMode_eq_mFourierCoeff
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    openPeriodicVorticityFourierMode solution t k =
      UnitAddTorus.mFourierCoeff (complexTorusVorticitySlice solution t) k := rfl

/-- Complexifying a real Euclidean vector into the coordinatewise complex chart cannot increase
its norm. -/
theorem norm_complexifySpace_le (v : Space) :
    ‖complexifySpace v‖ ≤ ‖v‖ := by
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg v)]
  intro coordinate
  simp only [complexifySpace, Complex.norm_real]
  exact PiLp.norm_apply_le v coordinate

/-- Every actual vorticity coefficient is bounded by the genuine spatial critical receiver.
This uses probability Haar measure and does not replace the field by a cube surrogate. -/
theorem norm_openPeriodicVorticityFourierMode_le_criticalVorticityRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    ‖openPeriodicVorticityFourierMode solution t k‖ ≤
      criticalVorticityRate solution t.1 := by
  rw [criticalVorticityRate_eq solution t.2]
  rw [openPeriodicVorticityFourierMode_eq_mFourierCoeff]
  rw [UnitAddTorus.mFourierCoeff]
  have hpoint : ∀ q : SpatialTorus,
      ‖UnitAddTorus.mFourier (-k) q • complexTorusVorticitySlice solution t q‖ ≤
        ‖torusVorticityEvolution solution t‖ := by
    intro q
    rw [norm_smul]
    have hchar : ‖UnitAddTorus.mFourier (-k) q‖ = 1 := by
      simp only [UnitAddTorus.mFourier, ContinuousMap.coe_mk, norm_prod,
        fourier_apply, Circle.norm_coe, Finset.prod_const_one]
    rw [hchar, one_mul]
    exact (norm_complexifySpace_le (torusVorticityEvolution solution t q)).trans
      ((torusVorticityEvolution solution t).norm_coe_le_norm q)
  have h := MeasureTheory.norm_integral_le_of_norm_le_const
    (μ := (volume : Measure SpatialTorus))
    (Filter.Eventually.of_forall hpoint)
  simpa using h

/-- Actual vorticity field synthesized from a declared finite frequency population. -/
def openPeriodicVorticityBandProjector
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) :
    C(SpatialTorus, ComplexVector) :=
  finiteFourierSynthesis (openPeriodicVorticityFourierMode solution t) modes

/-- Exact coefficient support of an actual vorticity band. -/
theorem mFourierCoeff_openPeriodicVorticityBandProjector
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (k : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (openPeriodicVorticityBandProjector solution t modes) k =
      if k ∈ modes then openPeriodicVorticityFourierMode solution t k else 0 := by
  exact mFourierCoeff_finiteFourierSynthesis _ _ _

/-- A finite actual vorticity band is bounded by its exact coefficient population. -/
theorem norm_openPeriodicVorticityBandProjector_le_sum_norm
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus) :
    ‖openPeriodicVorticityBandProjector solution t modes q‖ ≤
      ∑ k ∈ modes, ‖openPeriodicVorticityFourierMode solution t k‖ :=
  norm_finiteFourierSynthesis_le_sum_norm _ _ _

/-- Concrete finite-band estimate from the critical receiver.  The explicit cardinality factor
records the loss of this sharp aperture; obtaining a scale-uniform middle-shell estimate requires
a different smooth multiplier owner and its kernel-cancellation theorem. -/
theorem norm_openPeriodicVorticityBandProjector_le_card_mul_criticalVorticityRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus) :
    ‖openPeriodicVorticityBandProjector solution t modes q‖ ≤
      modes.card * criticalVorticityRate solution t.1 := by
  calc
    ‖openPeriodicVorticityBandProjector solution t modes q‖ ≤
        ∑ k ∈ modes, ‖openPeriodicVorticityFourierMode solution t k‖ :=
      norm_openPeriodicVorticityBandProjector_le_sum_norm solution t modes q
    _ ≤ modes.card * criticalVorticityRate solution t.1 := by
      simpa [nsmul_eq_mul] using Finset.sum_le_card_nsmul modes
        (fun k ↦ ‖openPeriodicVorticityFourierMode solution t k‖)
        (criticalVorticityRate solution t.1)
        (fun k _hk ↦
          norm_openPeriodicVorticityFourierMode_le_criticalVorticityRate
            solution t k)

/-- The cube-apertured form exposes its exact `(2 radius + 1)^3` mode cost. -/
theorem norm_openPeriodicVorticityCubeProjector_le_modeCount_mul_criticalVorticityRate
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (radius : ℕ) (q : SpatialTorus) :
    ‖openPeriodicVorticityBandProjector solution t (frequencyCube radius) q‖ ≤
      ((2 * radius + 1) ^ 3 : ℕ) * criticalVorticityRate solution t.1 := by
  simpa [card_frequencyCube] using
    norm_openPeriodicVorticityBandProjector_le_card_mul_criticalVorticityRate
      solution t (frequencyCube radius) q

/-- The actual finite outer vorticity aperture decomposes into the three constructed bands. -/
theorem openPeriodicVorticityOuterCube_eq_threeBands
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth highShells : ℕ) :
    openPeriodicVorticityBandProjector solution t
        (frequencyCube (dyadicRadius (depth + highShells))) =
      openPeriodicVorticityBandProjector solution t lowFrequencyModes +
        openPeriodicVorticityBandProjector solution t (middleFrequencyModes depth) +
          openPeriodicVorticityBandProjector solution t
            (highFrequencyApertureModes depth highShells) :=
  finiteFourierSynthesis_outerCube_eq_threeBands _ depth highShells

/-! ## Actual Jacobian populations of an admitted solution slice -/

/-- Normed coefficient chart for the nine Jacobian entries.  `Matrix` intentionally carries no
canonical norm in mathlib, so the analytic receiver exposes the same entries in their curried
finite-product chart. -/
abbrev ComplexJacobianArray := Fin 3 → Fin 3 → ℂ

/-- The genuine-torus Fourier coefficient of the actual Jacobian on one admitted solution
slice. -/
def openPeriodicJacobianFourierMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) : ComplexJacobianArray :=
  fun component coordinate ↦
    actualJacobianFourierMode (fun x ↦ velocity x t.1)
      (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2)
      (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩) k component coordinate

/-- Every actual solution-slice Jacobian coefficient is the established derivative multiplier of
the actual velocity coefficient. -/
theorem openPeriodicJacobianFourierMode_eq_fourierJacobianMode
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (k : SpatialFrequency) :
    openPeriodicJacobianFourierMode solution t k =
      fourierJacobianMode k (openPeriodicVelocityFourierMode solution t k) := by
  funext component coordinate
  exact actualJacobianFourierMode_eq_multiplier
    (fun x ↦ velocity x t.1)
    (openPeriodicSolutionOn_velocitySlice_contDiff_one solution t.2)
    (solution.velocityPeriodic t.1 ⟨t.2.1.le, t.2.2⟩)
    k component coordinate

/-- Actual Jacobian field synthesized from a declared finite mode population. -/
def openPeriodicJacobianBandProjector
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) :
    C(SpatialTorus, ComplexJacobianArray) :=
  finiteFourierSynthesis (openPeriodicJacobianFourierMode solution t) modes

/-- Exact coefficient support of an actual Jacobian band. -/
theorem mFourierCoeff_openPeriodicJacobianBandProjector
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (k : SpatialFrequency) :
    UnitAddTorus.mFourierCoeff
        (openPeriodicJacobianBandProjector solution t modes) k =
      if k ∈ modes then openPeriodicJacobianFourierMode solution t k else 0 := by
  exact mFourierCoeff_finiteFourierSynthesis _ _ _

/-- Exact finite-band Jacobian estimate before any unproved Calderon--Zygmund cancellation is
invoked. -/
theorem norm_openPeriodicJacobianBandProjector_le_sum_norm
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (modes : Finset SpatialFrequency) (q : SpatialTorus) :
    ‖openPeriodicJacobianBandProjector solution t modes q‖ ≤
      ∑ k ∈ modes, ‖openPeriodicJacobianFourierMode solution t k‖ :=
  norm_finiteFourierSynthesis_le_sum_norm _ _ _

/-- The actual finite outer Jacobian aperture decomposes into the three constructed bands. -/
theorem openPeriodicJacobianOuterCube_eq_threeBands
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) (depth highShells : ℕ) :
    openPeriodicJacobianBandProjector solution t
        (frequencyCube (dyadicRadius (depth + highShells))) =
      openPeriodicJacobianBandProjector solution t lowFrequencyModes +
        openPeriodicJacobianBandProjector solution t (middleFrequencyModes depth) +
          openPeriodicJacobianBandProjector solution t
            (highFrequencyApertureModes depth highShells) :=
  finiteFourierSynthesis_outerCube_eq_threeBands _ depth highShells

section Audit

#print axioms card_frequencyCube
#print axioms integral_mFourier_neg_mul_mFourier
#print axioms mFourierCoeff_finiteFourierSynthesis
#print axioms finiteFourierSynthesis_outerCube_eq_threeBands
#print axioms norm_openPeriodicVorticityFourierMode_le_criticalVorticityRate
#print axioms mFourierCoeff_openPeriodicVorticityBandProjector
#print axioms norm_openPeriodicVorticityCubeProjector_le_modeCount_mul_criticalVorticityRate
#print axioms openPeriodicJacobianFourierMode_eq_fourierJacobianMode
#print axioms mFourierCoeff_openPeriodicJacobianBandProjector
#print axioms openPeriodicJacobianOuterCube_eq_threeBands

end Audit

end Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
