import ElementaryHolonics.Millennium.NavierStokesInfiniteFourierHeatRestart
import ElementaryHolonics.Millennium.NavierStokesFourierTriads

/-!
# The infinite Fourier nonlinearity before the mild fixed point

The existing infinite owner supplies the genuine `ℓ²(ℤ³)` Fourier carrier, the weighted
`H³` subtype, and the exact diagonal heat semigroup.  This successor constructs two pieces that a
nonlinear mild passage must actually use:

* translation on the complete Fourier `ℓ²` population and the discrete Young passage
  `ℓ¹ * ℓ² → ℓ²`, including its exact coefficient law and norm-one constant;
* the genuine derivative multiplier on an `H³` coefficient population, returned in `ℓ²`.

These results remove finite cutoffs from the coefficient-level convolution aperture.  They do not
assert that every `H³` population has yet been transported into the required weighted `ℓ¹`
envelopes.  The remaining analytic edge for the standard `H³` mild contraction is the weighted
three-dimensional discrete Sobolev--Young estimate

`H³(ℤ³) × H³(ℤ³) → H²(ℤ³)`

for the differentiated convolution, together with the modewise bounded Leray projection on that
carrier.  No local-existence, fixed-point, Duhamel, or continuation conclusion is assumed.
-/

noncomputable section

open scoped BigOperators ENNReal NNReal

namespace Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity

open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesFourierTriads
open Soma.Holonics.Millennium.NavierStokesFiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeat
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatH3
open Soma.Holonics.Millennium.NavierStokesInfiniteFourierHeatRestart

/-! ## Exact translation on the complete Fourier Hilbert carrier -/

/-- [definition] The addressed translation `k ↦ k - p` of the integer frequency lattice. -/
def frequencyTranslation (p : SpatialFrequency) : SpatialFrequency ≃ SpatialFrequency :=
  Equiv.addRight (-p)

@[simp]
theorem frequencyTranslation_apply (p k : SpatialFrequency) :
    frequencyTranslation p k = k - p := by
  simp [frequencyTranslation, sub_eq_add_neg]

/-- [definition] Translation of every coefficient of a genuine Fourier `ℓ²` population. -/
def translatePeriodicFourierL2
    (p : SpatialFrequency) (coeff : PeriodicFourierL2) : PeriodicFourierL2 :=
  ⟨fun k ↦ coeff (k - p), by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    have hcoeff : Summable (fun k ↦ ‖coeff k‖ ^ 2) := by
      have h := (lp.memℓp coeff).summable
        (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
      simpa using h
    have htranslated := (frequencyTranslation p).summable_iff.mpr hcoeff
    simpa only [Function.comp_apply, frequencyTranslation_apply, Real.rpow_two] using
      htranslated⟩

@[simp]
theorem translatePeriodicFourierL2_apply
    (p : SpatialFrequency) (coeff : PeriodicFourierL2) (k : SpatialFrequency) :
    translatePeriodicFourierL2 p coeff k = coeff (k - p) := rfl

/-- [proved-derived] Lattice translation is an exact isometry of the complete Fourier `ℓ²`
carrier. -/
theorem norm_translatePeriodicFourierL2
    (p : SpatialFrequency) (coeff : PeriodicFourierL2) :
    ‖translatePeriodicFourierL2 p coeff‖ = ‖coeff‖ := by
  have hleft := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
    (translatePeriodicFourierL2 p coeff)
  have hright := lp.norm_rpow_eq_tsum
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal) coeff
  have hsum :
      (∑' k, ‖coeff (k - p)‖ ^ 2) = ∑' k, ‖coeff k‖ ^ 2 := by
    simpa only [frequencyTranslation_apply] using
      (frequencyTranslation p).tsum_eq (fun k ↦ ‖coeff k‖ ^ 2)
  have hsquare : ‖translatePeriodicFourierL2 p coeff‖ ^ 2 = ‖coeff‖ ^ 2 := by
    calc
      ‖translatePeriodicFourierL2 p coeff‖ ^ 2 =
          ∑' k, ‖translatePeriodicFourierL2 p coeff k‖ ^ 2 := by
            simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hleft
      _ = ∑' k, ‖coeff (k - p)‖ ^ 2 := by
            simp only [translatePeriodicFourierL2_apply]
      _ = ∑' k, ‖coeff k‖ ^ 2 := hsum
      _ = ‖coeff‖ ^ 2 := by
            simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hright.symm
  nlinarith [norm_nonneg (translatePeriodicFourierL2 p coeff), norm_nonneg coeff]

/-! ## The complete discrete `ℓ¹ * ℓ² → ℓ²` Young passage -/

/-- [definition] Convolution is formed as the Banach-space sum of addressed translates.  The
definition is total, while the exact coefficient and norm theorems below require absolute
summability of the left population. -/
def l1L2FourierConvolution
    (left : SpatialFrequency → ℂ) (right : PeriodicFourierL2) : PeriodicFourierL2 :=
  ∑' p, left p • translatePeriodicFourierL2 p right

/-- [proved-derived] Absolute summability of the left population makes the complete population
of translated `ℓ²` passages summable in the Hilbert carrier. -/
theorem summable_l1L2FourierConvolution_passages
    {left : SpatialFrequency → ℂ}
    (hleft : Summable fun p ↦ ‖left p‖) (right : PeriodicFourierL2) :
    Summable fun p ↦ left p • translatePeriodicFourierL2 p right := by
  apply Summable.of_norm
  have hscaled : Summable fun p ↦ ‖left p‖ * ‖right‖ := hleft.mul_right ‖right‖
  simpa only [norm_smul, norm_translatePeriodicFourierL2] using hscaled

/-- [definition] Coordinate evaluation as a continuous linear receiver on Fourier `ℓ²`. -/
def periodicFourierL2Evaluation (k : SpatialFrequency) : PeriodicFourierL2 →L[ℂ] ℂ :=
  LinearMap.mkContinuous
    { toFun := fun coeff ↦ coeff k
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
    1 (fun coeff ↦ by
      simpa using lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0) coeff k)

@[simp]
theorem periodicFourierL2Evaluation_apply
    (k : SpatialFrequency) (coeff : PeriodicFourierL2) :
    periodicFourierL2Evaluation k coeff = coeff k := rfl

/-- [proved-derived] Exact infinite coefficient law for the discrete convolution. -/
theorem l1L2FourierConvolution_apply
    {left : SpatialFrequency → ℂ} (hleft : Summable fun p ↦ ‖left p‖)
    (right : PeriodicFourierL2) (k : SpatialFrequency) :
    l1L2FourierConvolution left right k =
      ∑' p, left p * right (k - p) := by
  have hsummable := summable_l1L2FourierConvolution_passages hleft right
  change periodicFourierL2Evaluation k (l1L2FourierConvolution left right) = _
  rw [l1L2FourierConvolution,
    (periodicFourierL2Evaluation k).map_tsum hsummable]
  simp only [periodicFourierL2Evaluation_apply, lp.coeFn_smul, Pi.smul_apply,
    translatePeriodicFourierL2_apply, smul_eq_mul]

/-- [proved-derived] The full discrete Young estimate with constant one. -/
theorem norm_l1L2FourierConvolution_le
    {left : SpatialFrequency → ℂ} (hleft : Summable fun p ↦ ‖left p‖)
    (right : PeriodicFourierL2) :
    ‖l1L2FourierConvolution left right‖ ≤
      (∑' p, ‖left p‖) * ‖right‖ := by
  have hsummable := summable_l1L2FourierConvolution_passages hleft right
  calc
    ‖l1L2FourierConvolution left right‖ ≤
        ∑' p, ‖left p • translatePeriodicFourierL2 p right‖ := by
      have hnorm :
          Summable fun p ↦ ‖left p • translatePeriodicFourierL2 p right‖ := by
        have hscaled : Summable fun p ↦ ‖left p‖ * ‖right‖ :=
          hleft.mul_right ‖right‖
        simpa only [norm_smul, norm_translatePeriodicFourierL2] using hscaled
      exact norm_tsum_le_tsum_norm
        hnorm
    _ = ∑' p, ‖left p‖ * ‖right‖ := by
      congr 1
      funext p
      rw [norm_smul, norm_translatePeriodicFourierL2]
    _ = (∑' p, ‖left p‖) * ‖right‖ := hleft.tsum_mul_right ‖right‖

/-! ## The derivative passage owned by the weighted `H³` carrier -/

/-- [proved-derived] One coordinate of the Stokes symbol is bounded by the complete third-order
inhomogeneous Sobolev weight. -/
theorem coordinate_stokes_symbol_sq_le_weight_three
    (coordinate : Fin 3) (k : SpatialFrequency) :
    (2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2 ≤ periodicSobolevWeight 3 k := by
  have hcoordinate : (k coordinate : ℝ) ^ 2 ≤ frequencySquared k := by
    unfold frequencySquared
    exact Finset.single_le_sum (fun i _ ↦ sq_nonneg (k i : ℝ)) (Finset.mem_univ coordinate)
  have heigen :
      (2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2 ≤ torusStokesEigenvalue k := by
    exact mul_le_mul_of_nonneg_left hcoordinate (sq_nonneg (2 * Real.pi))
  have hlambda := torusStokesEigenvalue_nonneg k
  have hone : 1 ≤ 1 + torusStokesEigenvalue k := by linarith
  have hcubic :
      1 + torusStokesEigenvalue k ≤ (1 + torusStokesEigenvalue k) ^ 3 := by
    nlinarith [sq_nonneg (1 + torusStokesEigenvalue k)]
  exact heigen.trans ((le_add_of_nonneg_left zero_le_one).trans hcubic)

/-- [definition] The exact periodic derivative multiplier `2π i k_j` applied to an `H³`
coefficient population and returned in the genuine Fourier `ℓ²` carrier. -/
def periodicSobolevThreeDerivative
    (coordinate : Fin 3) (coeff : PeriodicSobolevCoefficients 3) : PeriodicFourierL2 :=
  ⟨fun k ↦ (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * coeff.1 k, by
    apply memℓp_gen
    norm_num only [ENNReal.toReal_ofNat]
    refine Summable.of_nonneg_of_le (fun k ↦ by positivity) (fun k ↦ ?_) coeff.2
    have hsymbol := coordinate_stokes_symbol_sq_le_weight_three coordinate k
    simpa only [Real.rpow_two] using (show
        ‖(2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * coeff.1 k‖ ^
            (2 : ℕ) ≤ periodicSobolevWeight 3 k * ‖coeff.1 k‖ ^ 2 from by
      calc
        ‖(2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * coeff.1 k‖ ^ 2 =
            ((2 * Real.pi) ^ 2 * (k coordinate : ℝ) ^ 2) * ‖coeff.1 k‖ ^ 2 := by
              simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs,
                Complex.norm_ofNat, Complex.norm_I, Complex.norm_intCast, mul_one]
              rw [abs_of_pos Real.pi_pos]
              ring_nf
              rw [sq_abs]
              ring
        _ ≤ periodicSobolevWeight 3 k * ‖coeff.1 k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hsymbol (sq_nonneg _))⟩

@[simp]
theorem periodicSobolevThreeDerivative_apply
    (coordinate : Fin 3) (coeff : PeriodicSobolevCoefficients 3)
    (k : SpatialFrequency) :
    periodicSobolevThreeDerivative coordinate coeff k =
      (2 * (Real.pi : ℂ) * Complex.I * (k coordinate : ℂ)) * coeff.1 k := rfl

/-! ## The actual differentiated vector convolution on an honest Wiener aperture -/

/-- [definition] The additional aperture currently required to construct the quadratic
coefficient population: every velocity component is absolutely summable before the derivative
lands on the transported factor.  This predicate is deliberately separate from `H³`; the
missing weighted Sobolev embedding must prove it (and its weighted derivative variants), not
silently assume it. -/
def HasAbsolutelySummableComponents (state : PeriodicVectorSobolevThree) : Prop :=
  ∀ component, Summable fun k ↦ ‖(state component).1 k‖

/-- [definition] The complete unprojected Fourier population of `(advecting · ∇) transported`.
Each output component is a finite sum of the already-founded infinite `ℓ¹ * ℓ²` passages. -/
def h3AdvectiveConvolution
    (advecting transported : PeriodicVectorSobolevThree) : PeriodicVectorFourierL2 :=
  fun output ↦ ∑ coordinate : Fin 3,
    l1L2FourierConvolution
      (fun p ↦ (advecting coordinate).1 p)
      (periodicSobolevThreeDerivative coordinate (transported output))

/-- [proved-derived] Exact coefficient law on the complete frequency population.  No finite
mode set occurs: the inner sum is over every advecting frequency `p`, while `k-p` is the
transported frequency. -/
theorem h3AdvectiveConvolution_apply
    {advecting : PeriodicVectorSobolevThree}
    (hadvecting : HasAbsolutelySummableComponents advecting)
    (transported : PeriodicVectorSobolevThree)
    (output : Fin 3) (k : SpatialFrequency) :
    h3AdvectiveConvolution advecting transported output k =
      ∑ coordinate : Fin 3, ∑' p,
        (advecting coordinate).1 p *
          ((2 * (Real.pi : ℂ) * Complex.I * ((k - p) coordinate : ℂ)) *
            (transported output).1 (k - p)) := by
  change (∑ coordinate : Fin 3,
    l1L2FourierConvolution
      (fun p ↦ (advecting coordinate).1 p)
      (periodicSobolevThreeDerivative coordinate (transported output))) k = _
  simp only [lp.coeFn_sum, Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro coordinate _hcoordinate
  rw [l1L2FourierConvolution_apply (hadvecting coordinate)]
  apply tsum_congr
  intro p
  rw [periodicSobolevThreeDerivative_apply]

/-- [proved-derived] The Wiener aperture and the `H³` derivative passage give the exact
componentwise Young estimate for the quadratic interaction. -/
theorem norm_h3AdvectiveConvolution_component_le
    {advecting : PeriodicVectorSobolevThree}
    (hadvecting : HasAbsolutelySummableComponents advecting)
    (transported : PeriodicVectorSobolevThree) (output : Fin 3) :
    ‖h3AdvectiveConvolution advecting transported output‖ ≤
      ∑ coordinate : Fin 3,
        (∑' p, ‖(advecting coordinate).1 p‖) *
          ‖periodicSobolevThreeDerivative coordinate (transported output)‖ := by
  unfold h3AdvectiveConvolution
  calc
    ‖∑ coordinate : Fin 3,
        l1L2FourierConvolution
          (fun p ↦ (advecting coordinate).1 p)
          (periodicSobolevThreeDerivative coordinate (transported output))‖ ≤
        ∑ coordinate : Fin 3,
          ‖l1L2FourierConvolution
            (fun p ↦ (advecting coordinate).1 p)
            (periodicSobolevThreeDerivative coordinate (transported output))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ coordinate : Fin 3,
        (∑' p, ‖(advecting coordinate).1 p‖) *
          ‖periodicSobolevThreeDerivative coordinate (transported output)‖ := by
      apply Finset.sum_le_sum
      intro coordinate _hcoordinate
      exact norm_l1L2FourierConvolution_le (hadvecting coordinate) _

/-! ## The exact Leray face at each nonzero frequency -/

/-- [definition] The standard Fourier Leray projection.  At the zero mode it is the identity;
at a nonzero mode it removes the component parallel to the frequency vector. -/
def lerayProjectMode (k : SpatialFrequency) (mode : ComplexVector) : ComplexVector :=
  if k = 0 then mode
  else mode -
    ((complexDot (complexFrequencyVector k) mode) / (frequencySquared k : ℂ)) •
      complexFrequencyVector k

@[simp]
theorem lerayProjectMode_zero (mode : ComplexVector) :
    lerayProjectMode 0 mode = mode := by
  simp [lerayProjectMode]

/-- [proved-derived] Every projected mode satisfies the exact Fourier divergence constraint,
including the mean mode. -/
theorem complexDot_lerayProjectMode_eq_zero
    (k : SpatialFrequency) (mode : ComplexVector) :
    complexDot (complexFrequencyVector k) (lerayProjectMode k mode) = 0 := by
  by_cases hk : k = 0
  · subst k
    simp [complexDot, dotProduct, complexFrequencyVector]
  · have hsReal : frequencySquared k ≠ 0 := (frequencySquared_pos hk).ne'
    have hsComplex : (frequencySquared k : ℂ) ≠ 0 := by exact_mod_cast hsReal
    rw [lerayProjectMode, if_neg hk]
    simp only [complexDot, dotProduct_sub, dotProduct_smul, smul_eq_mul]
    change
      complexDot (complexFrequencyVector k) mode -
        (complexDot (complexFrequencyVector k) mode / (frequencySquared k : ℂ)) *
          complexDot (complexFrequencyVector k) (complexFrequencyVector k) = 0
    rw [complexDot_frequency_self]
    field_simp
    ring

/-- [definition] The actual Leray-projected quadratic coefficient at every addressed output
frequency.  The unprojected field is the complete `ℓ²` convolution constructed above; this
receiver applies the exact pressure-eliminating face mode by mode. -/
def lerayProjectedH3AdvectiveCoefficient
    (advecting transported : PeriodicVectorSobolevThree)
    (k : SpatialFrequency) : ComplexVector :=
  lerayProjectMode k
    (vectorCoefficientAt (h3AdvectiveConvolution advecting transported) k)

/-- [proved-derived] The projected nonlinear coefficient is modewise divergence-free by
construction, without assuming divergence freedom of either input. -/
theorem lerayProjectedH3AdvectiveCoefficient_divergenceFree
    (advecting transported : PeriodicVectorSobolevThree) (k : SpatialFrequency) :
    complexDot (complexFrequencyVector k)
      (lerayProjectedH3AdvectiveCoefficient advecting transported k) = 0 := by
  exact complexDot_lerayProjectMode_eq_zero k _

#print axioms norm_translatePeriodicFourierL2
#print axioms l1L2FourierConvolution_apply
#print axioms norm_l1L2FourierConvolution_le
#print axioms coordinate_stokes_symbol_sq_le_weight_three
#print axioms periodicSobolevThreeDerivative
#print axioms h3AdvectiveConvolution_apply
#print axioms norm_h3AdvectiveConvolution_component_le
#print axioms complexDot_lerayProjectMode_eq_zero
#print axioms lerayProjectedH3AdvectiveCoefficient_divergenceFree

end Soma.Holonics.Millennium.NavierStokesMildFourierNonlinearity
