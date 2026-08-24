import Mathlib.Algebra.Order.Chebyshev
import ElementaryHolonics.Millennium.NavierStokesCoordinateH3Estimate

/-!
# Periodic cube interpolation for the middle H³ commutator faces

The three middle order-three Leibniz faces contain two second spatial derivatives and one
third spatial derivative.  This owner proves the periodic interpolation step which was left
open by `NavierStokesCoordinateH3Estimate`.

The source identity is one-dimensional but is enacted on an addressed coordinate circle of the
three-torus.  If `g = ∂ᵢ f` and `h = ∂ᵢ g`, periodic integration by parts gives

`(∫ g⁴) = -3 ∫ f g² h`.

The elementary square inequality then returns `∫ g⁴ ≤ 9 M² ∫ h²` whenever
`|f| ≤ M` on the cube.  No compact-support replacement, Fourier cutoff, or interpolation
hypothesis is introduced.
-/

noncomputable section

open ContDiff InnerProductSpace MeasureTheory Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesPeriodicCubeInterpolation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesFiniteTime
open Soma.Holonics.Millennium.NavierStokesFiniteTimeVorticity
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPeriodicFlux
open Soma.Holonics.Millennium.NavierStokesH3Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH1Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH2Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Production
open Soma.Holonics.Millennium.NavierStokesCoordinateH3Estimate

/-! ## An addressed scalar flux -/

/-- A scalar current carried through one addressed coordinate face. -/
def coordinateScalarFlux (direction : Fin 3) (f : Space → ℝ) : InitialVelocity :=
  fun x ↦ f x • spatialBasisVector direction

theorem coordinateScalarFlux_contDiff
    (direction : Fin 3) {f : Space → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (coordinateScalarFlux direction f) := by
  exact hf.smul contDiff_const

theorem coordinateScalarFlux_isOnePeriodic
    (direction : Fin 3) {f : Space → ℝ} (hf : IsOnePeriodic f) :
    IsOnePeriodic (coordinateScalarFlux direction f) := by
  intro x coordinate
  simp only [coordinateScalarFlux]
  rw [hf x coordinate]

/-- The divergence of a scalar current through coordinate `i` is its derivative in coordinate
`i`.  The proof retains the actual Euclidean divergence owner. -/
theorem divergence_coordinateScalarFlux
    (direction : Fin 3) {f : Space → ℝ} (hf : ContDiff ℝ 1 f) (x : Space) :
    divergence (coordinateScalarFlux direction f) x =
      fderiv ℝ f x (spatialBasisVector direction) := by
  rw [← sum_coordinate_fderiv_eq_divergence]
  have hdiff : DifferentiableAt ℝ f x := hf.differentiable (by norm_num) x
  have hfluxDerivative :
      fderiv ℝ (coordinateScalarFlux direction f) x =
        (fderiv ℝ f x).smulRight (spatialBasisVector direction) := by
    simpa [coordinateScalarFlux] using
      fderiv_smul_const hdiff (spatialBasisVector direction)
  rw [hfluxDerivative]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  simp [spatialBasisVector]

/-! ## The exact periodic quartic identity -/

/-- Periodic integration by parts for an addressed first and second derivative. -/
theorem integral_fourth_power_eq_neg_three_mul
    (direction : Fin 3) (f g h : Space → ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 0 h)
    (hfPeriodic : IsOnePeriodic f) (hgPeriodic : IsOnePeriodic g)
    (hfg : ∀ x, fderiv ℝ f x (spatialBasisVector direction) = g x)
    (hgh : ∀ x, fderiv ℝ g x (spatialBasisVector direction) = h x) :
    ∫ x in unitCube, g x ^ 4 =
      -3 * ∫ x in unitCube, f x * g x ^ 2 * h x := by
  let density : Space → ℝ := fun x ↦ f x * g x ^ 3
  have hdensity : ContDiff ℝ 1 density := hf.mul (hg.pow 3)
  have hdensityPeriodic : IsOnePeriodic density := by
    intro x coordinate
    simp only [density]
    rw [hfPeriodic x coordinate, hgPeriodic x coordinate]
  have hflux :
      ∫ x in unitCube, divergence (coordinateScalarFlux direction density) x = 0 :=
    integral_divergence_unitCube_eq_zero_of_onePeriodic
      (coordinateScalarFlux direction density)
      (coordinateScalarFlux_isOnePeriodic direction hdensityPeriodic)
      (coordinateScalarFlux_contDiff direction hdensity)
  have hdensityDerivative : ∀ x,
      fderiv ℝ density x (spatialBasisVector direction) =
        g x ^ 4 + 3 * (f x * g x ^ 2 * h x) := by
    intro x
    have hfdiff : DifferentiableAt ℝ f x := hf.differentiable (by norm_num) x
    have hgdiff : DifferentiableAt ℝ g x := hg.differentiable (by norm_num) x
    have hgpowdiff : DifferentiableAt ℝ (fun y ↦ g y ^ 3) x := hgdiff.pow 3
    have hmul := fderiv_fun_mul hfdiff hgpowdiff
    have hgpow := fderiv_pow 3 hgdiff
    have hmulApply := congrArg
      (fun L : Space →L[ℝ] ℝ ↦ L (spatialBasisVector direction)) hmul
    have hgpowApply := congrArg
      (fun L : Space →L[ℝ] ℝ ↦ L (spatialBasisVector direction)) hgpow
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] at hmulApply hgpowApply
    rw [hfg x] at hmulApply
    rw [hgh x] at hgpowApply
    dsimp [density] at hmulApply ⊢
    rw [hmulApply, hgpowApply]
    ring
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hzero :
      ∫ x in unitCube, (g x ^ 4 + 3 * (f x * g x ^ 2 * h x)) = 0 := by
    rw [← hflux]
    apply setIntegral_congr_fun hcubeCompact.measurableSet
    intro x _hx
    rw [divergence_coordinateScalarFlux direction hdensity x,
      hdensityDerivative x]
  have hg4 : IntegrableOn (fun x ↦ g x ^ 4) unitCube :=
    ((hg.continuous.pow 4).continuousOn.integrableOn_compact hcubeCompact)
  have hfg2h : IntegrableOn (fun x ↦ f x * g x ^ 2 * h x) unitCube :=
    (((hf.continuous.mul (hg.continuous.pow 2)).mul hh.continuous).continuousOn
      ).integrableOn_compact hcubeCompact
  rw [integral_add hg4 (hfg2h.const_mul 3), integral_const_mul] at hzero
  linarith

/-! ## The periodic `L⁴` interpolation return -/

/-- The scalar periodic cube inequality at the exact derivative scale needed by the middle
commutator population. -/
theorem integral_fourth_power_le_nine_mul
    (direction : Fin 3) (f g h : Space → ℝ) (M : ℝ)
    (hf : ContDiff ℝ 1 f) (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 0 h)
    (hfPeriodic : IsOnePeriodic f) (hgPeriodic : IsOnePeriodic g)
    (hfg : ∀ x, fderiv ℝ f x (spatialBasisVector direction) = g x)
    (hgh : ∀ x, fderiv ℝ g x (spatialBasisVector direction) = h x)
    (hM : ∀ x ∈ unitCube, |f x| ≤ M) :
    ∫ x in unitCube, g x ^ 4 ≤
      9 * M ^ 2 * ∫ x in unitCube, h x ^ 2 := by
  have hid := integral_fourth_power_eq_neg_three_mul direction f g h
    hf hg hh hfPeriodic hgPeriodic hfg hgh
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hg4 : IntegrableOn (fun x ↦ g x ^ 4) unitCube :=
    ((hg.continuous.pow 4).continuousOn.integrableOn_compact hcubeCompact)
  have hh2 : IntegrableOn (fun x ↦ h x ^ 2) unitCube :=
    ((hh.continuous.pow 2).continuousOn.integrableOn_compact hcubeCompact)
  have hfg2h : IntegrableOn (fun x ↦ f x * g x ^ 2 * h x) unitCube :=
    (((hf.continuous.mul (hg.continuous.pow 2)).mul hh.continuous).continuousOn
      ).integrableOn_compact hcubeCompact
  have hpoint : ∀ x ∈ unitCube,
      -(3 * (f x * g x ^ 2 * h x)) ≤
        (1 / 2 : ℝ) * g x ^ 4 + (9 / 2 : ℝ) * M ^ 2 * h x ^ 2 := by
    intro x hx
    have habs : |f x| ≤ M := hM x hx
    calc
      -(3 * (f x * g x ^ 2 * h x)) ≤
          |3 * (f x * g x ^ 2 * h x)| := neg_le_abs _
      _ = 3 * |f x| * g x ^ 2 * |h x| := by
        rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3),
          abs_sq]
        ring
      _ ≤ 3 * M * g x ^ 2 * |h x| := by
        gcongr
      _ ≤ (1 / 2 : ℝ) * g x ^ 4 + (9 / 2 : ℝ) * M ^ 2 * h x ^ 2 := by
        have hsquare' : 0 ≤ (g x ^ 2 - 3 * M * |h x|) ^ 2 := sq_nonneg _
        have habssq : |h x| ^ 2 = h x ^ 2 := sq_abs (h x)
        nlinarith [hsquare', habssq]
  have hintegral :
      ∫ x in unitCube, -(3 * (f x * g x ^ 2 * h x)) ≤
        ∫ x in unitCube,
          ((1 / 2 : ℝ) * g x ^ 4 + (9 / 2 : ℝ) * M ^ 2 * h x ^ 2) := by
    apply setIntegral_mono_on
    · exact (hfg2h.const_mul 3).neg
    · exact (hg4.const_mul (1 / 2)).add (hh2.const_mul ((9 / 2) * M ^ 2))
    · exact hcubeCompact.measurableSet
    · exact hpoint
  rw [integral_neg, integral_const_mul, integral_add (hg4.const_mul (1 / 2))
      (hh2.const_mul ((9 / 2) * M ^ 2)), integral_const_mul, integral_const_mul] at hintegral
  have hidAssoc :
      -(3 * ∫ x in unitCube, f x * g x ^ 2 * h x) =
        ∫ x in unitCube, g x ^ 4 := by
    calc
      -(3 * ∫ x in unitCube, f x * g x ^ 2 * h x) =
          -3 * ∫ x in unitCube, f x * g x ^ 2 * h x := by ring
      _ = ∫ x in unitCube, g x ^ 4 := hid.symm
  rw [hidAssoc] at hintegral
  have hleft : 0 ≤ ∫ x in unitCube, g x ^ 4 := by
    exact integral_nonneg_of_ae (Filter.Eventually.of_forall (fun x ↦ by positivity))
  nlinarith

/-! ## The actual spatial jets -/

/-- Projecting a differentiable Euclidean field to one component commutes with its Fréchet
derivative. -/
theorem fderiv_component_apply
    (w : InitialVelocity) (hw : ContDiff ℝ 1 w) (x direction : Space)
    (component : Fin 3) :
    fderiv ℝ (fun y ↦ w y component) x direction =
      (fderiv ℝ w x direction) component := by
  have hproject := (EuclideanSpace.proj component).hasFDerivAt.comp x
    (hw.differentiable (by norm_num) x).hasFDerivAt
  have hprojectApply := congrArg
    (fun L : Space →L[ℝ] ℝ ↦ L direction) hproject.fderiv
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply] using hprojectApply

/-- A component of every ordered second spatial jet satisfies the exact periodic `L⁴`
interpolation inequality.  The repeated third word `(i,i,j)` is one member of the existing
twenty-seven-word dissipation population. -/
theorem integral_secondSpatialCoordinateJet_component_fourth_le
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (i j component : Fin 3) :
    ∫ x in unitCube, (secondSpatialCoordinateJet u i j x component) ^ 4 ≤
      9 * cubeGradientSup u ^ 2 *
        ∫ x in unitCube, (thirdSpatialCoordinateJet u i i j x component) ^ 2 := by
  let first : InitialVelocity := spatialDirectionalJet u j
  let second : InitialVelocity := secondSpatialCoordinateJet u i j
  let third : InitialVelocity := thirdSpatialCoordinateJet u i i j
  let f : Space → ℝ := fun x ↦ first x component
  let g : Space → ℝ := fun x ↦ second x component
  let h : Space → ℝ := fun x ↦ third x component
  have hfirstSmooth : ContDiff ℝ ∞ first :=
    spatialDirectionalJet_contDiff u hu j
  have hsecondSmooth : ContDiff ℝ ∞ second :=
    secondSpatialCoordinateJet_contDiff u hu i j
  have hthirdSmooth : ContDiff ℝ ∞ third :=
    thirdSpatialCoordinateJet_contDiff u hu i i j
  have hf : ContDiff ℝ 1 f := by
    exact (EuclideanSpace.proj component).contDiff.comp
      (hfirstSmooth.of_le (WithTop.coe_le_coe.mpr le_top))
  have hg : ContDiff ℝ 1 g := by
    exact (EuclideanSpace.proj component).contDiff.comp
      (hsecondSmooth.of_le (WithTop.coe_le_coe.mpr le_top))
  have hh : ContDiff ℝ 0 h := by
    exact (EuclideanSpace.proj component).contDiff.comp
      (hthirdSmooth.of_le (WithTop.coe_le_coe.mpr le_top))
  have hfirstPeriodic : IsOnePeriodic first :=
    spatialDirectionalJet_isOnePeriodic u hperiodic j
  have hsecondPeriodic : IsOnePeriodic second :=
    secondSpatialCoordinateJet_isOnePeriodic u hperiodic i j
  have hfPeriodic : IsOnePeriodic f := by
    intro x coordinate
    exact congrArg (fun z : Space ↦ z component) (hfirstPeriodic x coordinate)
  have hgPeriodic : IsOnePeriodic g := by
    intro x coordinate
    exact congrArg (fun z : Space ↦ z component) (hsecondPeriodic x coordinate)
  have hfg : ∀ x, fderiv ℝ f x (spatialBasisVector i) = g x := by
    intro x
    rw [fderiv_component_apply first
      (hfirstSmooth.of_le (WithTop.coe_le_coe.mpr le_top))]
    rfl
  have hgh : ∀ x, fderiv ℝ g x (spatialBasisVector i) = h x := by
    intro x
    rw [fderiv_component_apply second
      (hsecondSmooth.of_le (WithTop.coe_le_coe.mpr le_top))]
    rfl
  have hM : ∀ x ∈ unitCube, |f x| ≤ cubeGradientSup u := by
    intro x hx
    exact abs_spatialDirectionalJet_component_le_cubeGradientSup
      u hu x hx j component
  simpa [f, g, h, first, second, third] using
    integral_fourth_power_le_nine_mul i f g h (cubeGradientSup u)
      hf hg hh hfPeriodic hgPeriodic hfg hgh hM

/-- In three Euclidean components, the fourth power of the vector norm is bounded by three
times the sum of the component fourth powers. -/
theorem norm_fourth_le_three_mul_sum_component_fourth (v : Space) :
    ‖v‖ ^ 4 ≤ 3 * ∑ component : Fin 3, (v component) ^ 4 := by
  have hsum := sq_sum_le_card_mul_sum_sq
    (s := Finset.univ) (f := fun component : Fin 3 ↦ ‖v component‖ ^ 2)
  calc
    ‖v‖ ^ 4 = (‖v‖ ^ 2) ^ 2 := by ring
    _ = (∑ component : Fin 3, ‖v component‖ ^ 2) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
    _ ≤ (Finset.univ.card : ℝ) *
        ∑ component : Fin 3, (‖v component‖ ^ 2) ^ 2 := by
      exact_mod_cast hsum
    _ = 3 * ∑ component : Fin 3, (v component) ^ 4 := by
      norm_num [Real.norm_eq_abs, sq_abs]
      apply Finset.sum_congr rfl
      intro component _hcomponent
      ring

/-- The vector-valued second jet inherits a complete periodic `L⁴` bound.  Its return is
written as the finite component population of one repeated third word, so no Hilbert--Schmidt
identity is hidden in the statement. -/
theorem integral_norm_secondSpatialCoordinateJet_fourth_le
    (u : InitialVelocity) (hu : ContDiff ℝ ∞ u) (hperiodic : IsOnePeriodic u)
    (i j : Fin 3) :
    ∫ x in unitCube, ‖secondSpatialCoordinateJet u i j x‖ ^ 4 ≤
      27 * cubeGradientSup u ^ 2 *
        ∑ component : Fin 3,
          ∫ x in unitCube,
            (thirdSpatialCoordinateJet u i i j x component) ^ 2 := by
  let second : InitialVelocity := secondSpatialCoordinateJet u i j
  let third : InitialVelocity := thirdSpatialCoordinateJet u i i j
  have hsecondSmooth : ContDiff ℝ ∞ second :=
    secondSpatialCoordinateJet_contDiff u hu i j
  have hthirdSmooth : ContDiff ℝ ∞ third :=
    thirdSpatialCoordinateJet_contDiff u hu i i j
  have hcubeCompact : IsCompact unitCube := by
    unfold unitCube
    exact (EuclideanSpace.equiv (Fin 3) ℝ).toHomeomorph.isCompact_preimage.mpr
      isCompact_Icc
  have hleftIntegrable : IntegrableOn (fun x ↦ ‖second x‖ ^ 4) unitCube :=
    ((hsecondSmooth.continuous.norm.pow 4).continuousOn).integrableOn_compact hcubeCompact
  have hcomponentFourthIntegrable : ∀ component : Fin 3,
      IntegrableOn (fun x ↦ (second x component) ^ 4) unitCube := by
    intro component
    exact ((((EuclideanSpace.proj component).continuous.comp
      hsecondSmooth.continuous).pow 4).continuousOn).integrableOn_compact hcubeCompact
  have hrightIntegrable : IntegrableOn
      (fun x ↦ 3 * ∑ component : Fin 3, (second x component) ^ 4) unitCube := by
    exact (Integrable.const_mul
      (integrable_finset_sum Finset.univ
        (fun component _hcomponent ↦ hcomponentFourthIntegrable component)) 3)
  have hpoint : ∀ x ∈ unitCube,
      ‖second x‖ ^ 4 ≤ 3 * ∑ component : Fin 3, (second x component) ^ 4 := by
    intro x _hx
    exact norm_fourth_le_three_mul_sum_component_fourth (second x)
  calc
    ∫ x in unitCube, ‖secondSpatialCoordinateJet u i j x‖ ^ 4 =
        ∫ x in unitCube, ‖second x‖ ^ 4 := by rfl
    _ ≤ ∫ x in unitCube,
        3 * ∑ component : Fin 3, (second x component) ^ 4 :=
      setIntegral_mono_on hleftIntegrable hrightIntegrable
        hcubeCompact.measurableSet hpoint
    _ = 3 * ∑ component : Fin 3,
        ∫ x in unitCube, (second x component) ^ 4 := by
      rw [integral_const_mul,
        integral_finset_sum Finset.univ
          (fun component _hcomponent ↦ hcomponentFourthIntegrable component)]
    _ ≤ 3 * ∑ component : Fin 3,
        (9 * cubeGradientSup u ^ 2 *
          ∫ x in unitCube, (third x component) ^ 2) := by
      gcongr with component
      simpa [second, third] using
        integral_secondSpatialCoordinateJet_component_fourth_le
          u hu hperiodic i j component
    _ = 27 * cubeGradientSup u ^ 2 *
        ∑ component : Fin 3,
          ∫ x in unitCube,
            (thirdSpatialCoordinateJet u i i j x component) ^ 2 := by
      dsimp [third]
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro component _hcomponent
      ring

/-! ## Kernel audit -/

#print axioms divergence_coordinateScalarFlux
#print axioms integral_fourth_power_eq_neg_three_mul
#print axioms integral_fourth_power_le_nine_mul
#print axioms integral_secondSpatialCoordinateJet_component_fourth_le
#print axioms integral_norm_secondSpatialCoordinateJet_fourth_le

end Soma.Holonics.Millennium.NavierStokesPeriodicCubeInterpolation
