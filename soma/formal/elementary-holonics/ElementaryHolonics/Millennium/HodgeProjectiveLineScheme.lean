import ElementaryHolonics.Millennium.HodgeProjectiveSpaceAmbient
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
# The algebraic projective line and its exact affine charts

This file specializes the common projective-space ambient to two homogeneous coordinates and
constructs the missing chart algebra explicitly.  Localization away from the second coordinate
has degree-zero ring exactly `ℂ[X]`: dehomogenization sends `[X₀:X₁]` to `X₀/X₁`, and
homogenization reconstructs every homogeneous numerator.  Consequently that affine chart is
smooth over the typed degree-zero base.  The coordinate-swap symmetry returns the other chart,
and the two charts cover `Proj`; hence the genuine scheme-theoretic projective line is smooth and
projective over `Spec ℂ`.

No analytic point comparison or Hodge conclusion is assumed here.  This closes the algebraic
geometry half of the first positive-dimensional receiver and leaves the exact analytification and
cycle-class identification as the next source bridge.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped Matrix

namespace Soma.Holonics.Millennium.HodgeProjectiveLineScheme

open Soma.Holonics.Millennium.HodgeSmoothProjectiveReceiver
open Soma.Holonics.Millennium.HodgeProjectiveSpaceAmbient

abbrev CoordinateRing := HodgeProjectiveSpaceAmbient.CoordinateRing 2
abbrev Grading := HodgeProjectiveSpaceAmbient.Grading 2
abbrev DegreeZero := HodgeProjectiveSpaceAmbient.DegreeZero 2

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev ProjectiveLineScheme := Proj Grading

/-- [definition] The second homogeneous coordinate, used as the denominator on one affine chart. -/
abbrev denominatorCoordinate : CoordinateRing := MvPolynomial.X (1 : Fin 2)

/-- [proved-standard; formal-checked] The selected denominator coordinate has degree one. -/
theorem denominatorCoordinate_mem_degree_one : denominatorCoordinate ∈ Grading 1 :=
  variable_mem_degree_one 2 1

/-- [definition] The degree-zero homogeneous localization on the second standard affine chart. -/
abbrev AwaySecond := HomogeneousLocalization.Away Grading denominatorCoordinate

/-- [definition] Substitute `X₀ ↦ X` and `X₁ ↦ 1`; this is the exact dehomogenization
current on homogeneous numerators. -/
def dehomogenize : CoordinateRing →+* Polynomial ℂ :=
  MvPolynomial.eval₂Hom Polynomial.C ![Polynomial.X, 1]

@[simp]
theorem dehomogenize_firstCoordinate :
    dehomogenize (MvPolynomial.X (0 : Fin 2)) = Polynomial.X := by
  simp [dehomogenize]

@[simp]
theorem dehomogenize_denominatorCoordinate :
    dehomogenize denominatorCoordinate = 1 := by
  simp [dehomogenize, denominatorCoordinate]

/-- [definition] Dehomogenization descends through localization because the selected denominator
is sent to the unit `1`. -/
def awaySecondToPolynomial : AwaySecond →+* Polynomial ℂ :=
  (Localization.awayLift dehomogenize denominatorCoordinate
      (by rw [dehomogenize_denominatorCoordinate]; exact isUnit_one)).comp
    (algebraMap AwaySecond (Localization (Submonoid.powers denominatorCoordinate)))

/-- [proved-standard; formal-checked] On a represented homogeneous fraction, the chart map is
exactly dehomogenization of its numerator; the power of `X₁` maps to one. -/
theorem awaySecondToPolynomial_mk (degree : ℕ) (numerator : CoordinateRing)
    (homogeneous : numerator ∈ Grading degree) :
    awaySecondToPolynomial
        (HomogeneousLocalization.Away.mk Grading denominatorCoordinate_mem_degree_one
          degree numerator (by simpa using homogeneous)) =
      dehomogenize numerator := by
  simp [awaySecondToPolynomial, dehomogenize,
    HomogeneousLocalization.Away.val_mk, Localization.awayLift_mk]

/-- [proved-standard; formal-checked] Dehomogenizing and re-homogenizing a homogeneous numerator
at its declared degree returns that numerator exactly. -/
theorem homogenize_dehomogenize_of_homogeneous {degree : ℕ}
    {numerator : CoordinateRing} (homogeneous : numerator.IsHomogeneous degree) :
    (dehomogenize numerator).homogenize degree = numerator := by
  apply Polynomial.homogenize_eq_of_isHomogeneous homogeneous
  rfl

/-- [proved-standard; formal-checked] Dehomogenization is injective on each declared homogeneous
piece. -/
theorem dehomogenize_eq_zero_of_homogeneous {degree : ℕ}
    {numerator : CoordinateRing} (homogeneous : numerator.IsHomogeneous degree)
    (dehomogenized_zero : dehomogenize numerator = 0) : numerator = 0 := by
  rw [← homogenize_dehomogenize_of_homogeneous homogeneous,
    dehomogenized_zero, Polynomial.homogenize_zero]

/-- [proved-standard; formal-checked] The affine-chart dehomogenization map has trivial kernel. -/
theorem awaySecondToPolynomial_injective :
    Function.Injective awaySecondToPolynomial := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply bot_unique
  intro fraction fraction_mem_kernel
  rw [RingHom.mem_ker] at fraction_mem_kernel
  obtain ⟨degree, numerator, homogeneous, represented⟩ :=
    HomogeneousLocalization.Away.mk_surjective Grading
      denominatorCoordinate_mem_degree_one fraction
  have homogeneousDegree : numerator ∈ Grading degree := by
    simpa using homogeneous
  rw [← represented,
    awaySecondToPolynomial_mk degree numerator homogeneousDegree] at fraction_mem_kernel
  rw [← represented]
  change HomogeneousLocalization.Away.mk Grading
      denominatorCoordinate_mem_degree_one degree numerator homogeneous = 0
  apply HomogeneousLocalization.mk_eq_zero_of_num
  apply Subtype.ext
  change numerator = 0
  apply dehomogenize_eq_zero_of_homogeneous
  · rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact homogeneous
  · exact fraction_mem_kernel

/-- [definition] The affine coordinate `X₀/X₁` inside the homogeneous localization. -/
def affineRatio : AwaySecond :=
  HomogeneousLocalization.Away.mk Grading denominatorCoordinate_mem_degree_one 1
    (MvPolynomial.X (0 : Fin 2)) (by
      change MvPolynomial.X (0 : Fin 2) ∈ Grading 1
      exact variable_mem_degree_one 2 0)

@[simp]
theorem awaySecondToPolynomial_affineRatio :
    awaySecondToPolynomial affineRatio = Polynomial.X := by
  have homogeneous :
      (MvPolynomial.X (0 : Fin 2) : CoordinateRing) ∈ Grading 1 :=
    variable_mem_degree_one 2 0
  change awaySecondToPolynomial
      (HomogeneousLocalization.Away.mk Grading
        denominatorCoordinate_mem_degree_one 1
        (MvPolynomial.X (0 : Fin 2)) homogeneous) = Polynomial.X
  exact (awaySecondToPolynomial_mk 1 _ homogeneous).trans
    dehomogenize_firstCoordinate

/-- [proved-standard; formal-checked] A degree-zero coefficient crosses the chart as the same
complex constant polynomial. -/
theorem awaySecondToPolynomial_fromZero (coefficient : DegreeZero) :
    awaySecondToPolynomial
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers denominatorCoordinate) coefficient) =
      Polynomial.C ((degreeZeroEquiv 2) coefficient) := by
  have homogeneous : (coefficient : CoordinateRing) ∈ Grading 0 := coefficient.property
  have represented :
      HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers denominatorCoordinate) coefficient =
        HomogeneousLocalization.Away.mk Grading
          denominatorCoordinate_mem_degree_one 0
          (coefficient : CoordinateRing) homogeneous := rfl
  rw [represented, awaySecondToPolynomial_mk 0 _ homogeneous]
  rw [HodgeProjectiveSpaceAmbient.homogeneous_zero_eq_constant 2 coefficient]
  simp only [dehomogenize, MvPolynomial.eval₂Hom_C]
  rfl

/-- [proved-standard; formal-checked] Every affine polynomial is the dehomogenization of an exact
degree-zero homogeneous fraction. -/
theorem awaySecondToPolynomial_surjective :
    Function.Surjective awaySecondToPolynomial := by
  intro polynomial
  induction polynomial using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨p', rfl⟩ := hp
      obtain ⟨q', rfl⟩ := hq
      exact ⟨p' + q', map_add _ _ _⟩
  | monomial degree coefficient =>
      let coefficientOccurrence : DegreeZero :=
        HodgeProjectiveSpaceAmbient.constantOccurrence 2 coefficient
      let coefficientFraction : AwaySecond :=
        HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers denominatorCoordinate) coefficientOccurrence
      refine ⟨coefficientFraction * affineRatio ^ degree, ?_⟩
      rw [map_mul, map_pow, awaySecondToPolynomial_affineRatio]
      have coefficientChart :
          awaySecondToPolynomial coefficientFraction = Polynomial.C coefficient := by
        rw [show coefficientFraction =
            HomogeneousLocalization.fromZeroRingHom Grading
              (Submonoid.powers denominatorCoordinate) coefficientOccurrence from rfl,
          awaySecondToPolynomial_fromZero]
        change Polynomial.C
            ((degreeZeroEquiv 2)
              (HodgeProjectiveSpaceAmbient.constantOccurrence 2 coefficient)) =
          Polynomial.C coefficient
        simp [HodgeProjectiveSpaceAmbient.degreeZeroEquiv,
          HodgeProjectiveSpaceAmbient.constantOccurrence]
      rw [coefficientChart]
      change Polynomial.C coefficient * Polynomial.X ^ degree =
        Polynomial.monomial degree coefficient
      exact Polynomial.C_mul_X_pow_eq_monomial

/-- [proved-standard; formal-checked] The second projective chart is exactly one affine line,
with both directions of reconstruction retained. -/
def awaySecondEquivPolynomial : AwaySecond ≃+* Polynomial ℂ :=
  RingEquiv.ofBijective awaySecondToPolynomial
    ⟨awaySecondToPolynomial_injective, awaySecondToPolynomial_surjective⟩

/-- [proved-standard; formal-checked] The chart equivalence respects the typed degree-zero base:
a degree-zero homogeneous coefficient becomes the same complex constant polynomial. -/
theorem awaySecondEquivPolynomial_fromZero (coefficient : DegreeZero) :
    awaySecondEquivPolynomial
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers denominatorCoordinate) coefficient) =
      Polynomial.C ((degreeZeroEquiv 2) coefficient) := by
  change awaySecondToPolynomial
      (HomogeneousLocalization.fromZeroRingHom Grading
        (Submonoid.powers denominatorCoordinate) coefficient) = _
  exact awaySecondToPolynomial_fromZero coefficient

/-- [proved-standard; formal-checked] The degree-zero ring equivalence is a smooth transport. -/
theorem degreeZeroToComplex_smooth :
    RingHom.Smooth (degreeZeroEquiv 2).toRingHom :=
  RingHom.Smooth.of_bijective (degreeZeroEquiv 2).bijective

/-- [proved-standard; formal-checked] The ordinary one-variable polynomial extension is smooth. -/
theorem complexToPolynomial_smooth :
    RingHom.Smooth (Polynomial.C : ℂ →+* Polynomial ℂ) := by
  change RingHom.Smooth (algebraMap ℂ (Polynomial ℂ))
  rw [RingHom.smooth_algebraMap]
  exact ⟨inferInstance, inferInstance⟩

/-- [proved-standard; formal-checked] The second homogeneous affine chart is smooth over the
typed degree-zero base. -/
theorem fromZeroRingHom_second_smooth : RingHom.Smooth
    (HomogeneousLocalization.fromZeroRingHom Grading
      (Submonoid.powers denominatorCoordinate)) := by
  let sourceMap := HomogeneousLocalization.fromZeroRingHom Grading
    (Submonoid.powers denominatorCoordinate)
  let chartEquiv := awaySecondEquivPolynomial
  have chartComposite :
      chartEquiv.toRingHom.comp sourceMap =
        (Polynomial.C : ℂ →+* Polynomial ℂ).comp
          (degreeZeroEquiv 2).toRingHom := by
    apply RingHom.ext
    intro coefficient
    exact awaySecondEquivPolynomial_fromZero coefficient
  have forwardSmooth : RingHom.Smooth (chartEquiv.toRingHom.comp sourceMap) := by
    rw [chartComposite]
    exact degreeZeroToComplex_smooth.comp complexToPolynomial_smooth
  have inverseSmooth : RingHom.Smooth chartEquiv.symm.toRingHom :=
    RingHom.Smooth.of_bijective chartEquiv.symm.bijective
  have returnedSmooth := forwardSmooth.comp inverseSmooth
  have returnComposite :
      chartEquiv.symm.toRingHom.comp
          (chartEquiv.toRingHom.comp sourceMap) = sourceMap := by
    ext coefficient
    simp
  rw [returnComposite] at returnedSmooth
  exact returnedSmooth

/-! ## The opposite chart by exact coordinate polarity -/

/-- [definition] The first homogeneous coordinate, used as denominator on the opposite chart. -/
abbrev firstCoordinate : CoordinateRing := MvPolynomial.X (0 : Fin 2)

/-- [proved-standard; formal-checked] The first coordinate also has degree one. -/
theorem firstCoordinate_mem_degree_one : firstCoordinate ∈ Grading 1 :=
  variable_mem_degree_one 2 0

/-- [definition] The degree-zero homogeneous localization on the first standard affine chart. -/
abbrev AwayFirst := HomogeneousLocalization.Away Grading firstCoordinate

/-- [definition] Exchange the two homogeneous coordinates while preserving total degree. -/
def coordinateSwap : Grading →+*ᵍ Grading where
  toRingHom :=
    (MvPolynomial.renameEquiv ℂ (Equiv.swap (0 : Fin 2) 1)).toRingHom
  map_mem := by
    intro degree polynomial homogeneous
    rw [MvPolynomial.mem_homogeneousSubmodule] at homogeneous ⊢
    exact homogeneous.rename_isHomogeneous

@[simp]
theorem coordinateSwap_firstCoordinate :
    coordinateSwap firstCoordinate = denominatorCoordinate := by
  simp [coordinateSwap, firstCoordinate, denominatorCoordinate]

@[simp]
theorem coordinateSwap_denominatorCoordinate :
    coordinateSwap denominatorCoordinate = firstCoordinate := by
  simp [coordinateSwap, firstCoordinate, denominatorCoordinate]

/-- [proved-standard; formal-checked] Exchanging the two coordinates twice returns every
homogeneous-coordinate polynomial exactly. -/
theorem coordinateSwap_involutive (polynomial : CoordinateRing) :
    coordinateSwap (coordinateSwap polynomial) = polynomial := by
  change MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1)
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) polynomial) = polynomial
  rw [MvPolynomial.rename_rename]
  have swapSquare :
      (Equiv.swap (0 : Fin 2) 1 : Fin 2 → Fin 2) ∘
          (Equiv.swap (0 : Fin 2) 1 : Fin 2 → Fin 2) = id := by
    funext index
    fin_cases index <;> rfl
  rw [swapSquare]
  simp

/-- [proved-standard; formal-checked] The graded coordinate exchange is itself an involution. -/
theorem coordinateSwap_comp_self :
    coordinateSwap.comp coordinateSwap = GradedRingHom.id Grading := by
  apply GradedRingHom.ext
  exact coordinateSwap_involutive

/-- [definition] The opposite dehomogenization uses the same chart current after the single
coordinate-polarity involution: `X₀ ↦ 1`, `X₁ ↦ X`. -/
def dehomogenizeFirst : CoordinateRing →+* Polynomial ℂ :=
  dehomogenize.comp coordinateSwap.toRingHom

@[simp]
theorem dehomogenizeFirst_firstCoordinate :
    dehomogenizeFirst firstCoordinate = 1 := by
  rw [dehomogenizeFirst, RingHom.comp_apply]
  change dehomogenize (coordinateSwap firstCoordinate) = 1
  rw [coordinateSwap_firstCoordinate, dehomogenize_denominatorCoordinate]

@[simp]
theorem dehomogenizeFirst_denominatorCoordinate :
    dehomogenizeFirst denominatorCoordinate = Polynomial.X := by
  rw [dehomogenizeFirst, RingHom.comp_apply]
  change dehomogenize (coordinateSwap denominatorCoordinate) = Polynomial.X
  rw [coordinateSwap_denominatorCoordinate, dehomogenize_firstCoordinate]

/-- [definition] The first-chart current descends through localization because `X₀` is sent to
the unit `1`. -/
def awayFirstToPolynomial : AwayFirst →+* Polynomial ℂ :=
  (Localization.awayLift dehomogenizeFirst firstCoordinate
      (by rw [dehomogenizeFirst_firstCoordinate]; exact isUnit_one)).comp
    (algebraMap AwayFirst (Localization (Submonoid.powers firstCoordinate)))

/-- [proved-standard; formal-checked] The first-chart current evaluates a represented
homogeneous fraction by exact dehomogenization of its numerator. -/
theorem awayFirstToPolynomial_mk (degree : ℕ) (numerator : CoordinateRing)
    (homogeneous : numerator ∈ Grading degree) :
    awayFirstToPolynomial
        (HomogeneousLocalization.Away.mk Grading firstCoordinate_mem_degree_one
          degree numerator (by simpa using homogeneous)) =
      dehomogenizeFirst numerator := by
  simp [awayFirstToPolynomial, dehomogenizeFirst,
    HomogeneousLocalization.Away.val_mk, Localization.awayLift_mk]

/-- [proved-standard; formal-checked] Opposite-chart dehomogenization is injective on every
declared homogeneous piece because the polarity exchange is involutive. -/
theorem dehomogenizeFirst_eq_zero_of_homogeneous {degree : ℕ}
    {numerator : CoordinateRing} (homogeneous : numerator.IsHomogeneous degree)
    (dehomogenized_zero : dehomogenizeFirst numerator = 0) : numerator = 0 := by
  have swappedHomogeneous : (coordinateSwap numerator).IsHomogeneous degree := by
    rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact coordinateSwap.map_mem (by
      rw [MvPolynomial.mem_homogeneousSubmodule]
      exact homogeneous)
  have swappedZero : coordinateSwap numerator = 0 := by
    apply dehomogenize_eq_zero_of_homogeneous swappedHomogeneous
    exact dehomogenized_zero
  have returnedZero := congrArg coordinateSwap swappedZero
  simpa [coordinateSwap_involutive] using returnedZero

/-- [proved-standard; formal-checked] The first affine-chart current has trivial kernel. -/
theorem awayFirstToPolynomial_injective :
    Function.Injective awayFirstToPolynomial := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply bot_unique
  intro fraction fraction_mem_kernel
  rw [RingHom.mem_ker] at fraction_mem_kernel
  obtain ⟨degree, numerator, homogeneous, represented⟩ :=
    HomogeneousLocalization.Away.mk_surjective Grading
      firstCoordinate_mem_degree_one fraction
  have homogeneousDegree : numerator ∈ Grading degree := by
    simpa using homogeneous
  rw [← represented,
    awayFirstToPolynomial_mk degree numerator homogeneousDegree] at fraction_mem_kernel
  rw [← represented]
  change HomogeneousLocalization.Away.mk Grading
      firstCoordinate_mem_degree_one degree numerator homogeneous = 0
  apply HomogeneousLocalization.mk_eq_zero_of_num
  apply Subtype.ext
  change numerator = 0
  apply dehomogenizeFirst_eq_zero_of_homogeneous
  · rw [← MvPolynomial.mem_homogeneousSubmodule]
    exact homogeneous
  · exact fraction_mem_kernel

/-- [definition] The affine coordinate `X₁/X₀` on the first chart. -/
def affineRatioFirst : AwayFirst :=
  HomogeneousLocalization.Away.mk Grading firstCoordinate_mem_degree_one 1
    denominatorCoordinate denominatorCoordinate_mem_degree_one

@[simp]
theorem awayFirstToPolynomial_affineRatioFirst :
    awayFirstToPolynomial affineRatioFirst = Polynomial.X := by
  change awayFirstToPolynomial
      (HomogeneousLocalization.Away.mk Grading
        firstCoordinate_mem_degree_one 1 denominatorCoordinate
        denominatorCoordinate_mem_degree_one) = Polynomial.X
  exact (awayFirstToPolynomial_mk 1 _ denominatorCoordinate_mem_degree_one).trans
    dehomogenizeFirst_denominatorCoordinate

/-- [proved-standard; formal-checked] Coordinate polarity fixes every degree-zero coefficient. -/
theorem coordinateSwap_constant (coefficient : ℂ) :
    coordinateSwap (MvPolynomial.C coefficient : CoordinateRing) =
      MvPolynomial.C coefficient := by
  simp [coordinateSwap]

/-- [proved-standard; formal-checked] Degree-zero coefficients cross the first chart unchanged. -/
theorem awayFirstToPolynomial_fromZero (coefficient : DegreeZero) :
    awayFirstToPolynomial
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers firstCoordinate) coefficient) =
      Polynomial.C ((degreeZeroEquiv 2) coefficient) := by
  have homogeneous : (coefficient : CoordinateRing) ∈ Grading 0 := coefficient.property
  have represented :
      HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers firstCoordinate) coefficient =
        HomogeneousLocalization.Away.mk Grading
          firstCoordinate_mem_degree_one 0
          (coefficient : CoordinateRing) homogeneous := rfl
  rw [represented, awayFirstToPolynomial_mk 0 _ homogeneous]
  rw [HodgeProjectiveSpaceAmbient.homogeneous_zero_eq_constant 2 coefficient]
  simp [dehomogenizeFirst, coordinateSwap_constant, dehomogenize]
  rfl

/-- [proved-standard; formal-checked] Every affine polynomial is represented on the first chart. -/
theorem awayFirstToPolynomial_surjective :
    Function.Surjective awayFirstToPolynomial := by
  intro polynomial
  induction polynomial using Polynomial.induction_on' with
  | add p q hp hq =>
      obtain ⟨p', rfl⟩ := hp
      obtain ⟨q', rfl⟩ := hq
      exact ⟨p' + q', map_add _ _ _⟩
  | monomial degree coefficient =>
      let coefficientOccurrence : DegreeZero :=
        HodgeProjectiveSpaceAmbient.constantOccurrence 2 coefficient
      let coefficientFraction : AwayFirst :=
        HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers firstCoordinate) coefficientOccurrence
      refine ⟨coefficientFraction * affineRatioFirst ^ degree, ?_⟩
      rw [map_mul, map_pow, awayFirstToPolynomial_affineRatioFirst]
      have coefficientChart :
          awayFirstToPolynomial coefficientFraction = Polynomial.C coefficient := by
        rw [show coefficientFraction =
            HomogeneousLocalization.fromZeroRingHom Grading
              (Submonoid.powers firstCoordinate) coefficientOccurrence from rfl,
          awayFirstToPolynomial_fromZero]
        change Polynomial.C
            ((degreeZeroEquiv 2)
              (HodgeProjectiveSpaceAmbient.constantOccurrence 2 coefficient)) =
          Polynomial.C coefficient
        simp [HodgeProjectiveSpaceAmbient.degreeZeroEquiv,
          HodgeProjectiveSpaceAmbient.constantOccurrence]
      rw [coefficientChart]
      change Polynomial.C coefficient * Polynomial.X ^ degree =
        Polynomial.monomial degree coefficient
      exact Polynomial.C_mul_X_pow_eq_monomial

/-- [proved-standard; formal-checked] The first standard projective chart is exactly an affine
line, reconstructed through the same polarity-parametrized current as the second chart. -/
def awayFirstEquivPolynomial : AwayFirst ≃+* Polynomial ℂ :=
  RingEquiv.ofBijective awayFirstToPolynomial
    ⟨awayFirstToPolynomial_injective, awayFirstToPolynomial_surjective⟩

/-- [proved-standard; formal-checked] The first chart equivalence respects the typed base. -/
theorem awayFirstEquivPolynomial_fromZero (coefficient : DegreeZero) :
    awayFirstEquivPolynomial
        (HomogeneousLocalization.fromZeroRingHom Grading
          (Submonoid.powers firstCoordinate) coefficient) =
      Polynomial.C ((degreeZeroEquiv 2) coefficient) :=
  awayFirstToPolynomial_fromZero coefficient

/-- [proved-standard; formal-checked] The first homogeneous affine chart is smooth over the
typed degree-zero base. -/
theorem fromZeroRingHom_first_smooth : RingHom.Smooth
    (HomogeneousLocalization.fromZeroRingHom Grading
      (Submonoid.powers firstCoordinate)) := by
  let sourceMap := HomogeneousLocalization.fromZeroRingHom Grading
    (Submonoid.powers firstCoordinate)
  let chartEquiv := awayFirstEquivPolynomial
  have chartComposite :
      chartEquiv.toRingHom.comp sourceMap =
        (Polynomial.C : ℂ →+* Polynomial ℂ).comp
          (degreeZeroEquiv 2).toRingHom := by
    apply RingHom.ext
    exact awayFirstEquivPolynomial_fromZero
  have forwardSmooth : RingHom.Smooth (chartEquiv.toRingHom.comp sourceMap) := by
    rw [chartComposite]
    exact degreeZeroToComplex_smooth.comp complexToPolynomial_smooth
  have inverseSmooth : RingHom.Smooth chartEquiv.symm.toRingHom :=
    RingHom.Smooth.of_bijective chartEquiv.symm.bijective
  have returnedSmooth := forwardSmooth.comp inverseSmooth
  have returnComposite :
      chartEquiv.symm.toRingHom.comp
          (chartEquiv.toRingHom.comp sourceMap) = sourceMap := by
    ext coefficient
    simp
  rw [returnComposite] at returnedSmooth
  exact returnedSmooth

/-! ## Global smooth projective carrier -/

/-- [proved-standard; formal-checked] The two exact affine currents cover projective one-space,
and each local structure map is smooth; therefore the complete projective structure map to its
degree-zero base is smooth. -/
theorem toSpecZero_smooth : Smooth (Proj.toSpecZero Grading) := by
  letI : IsZariskiLocalAtSource @Smooth :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Smooth)
  letI : MorphismProperty.RespectsIso @Smooth :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  rw [IsZariskiLocalAtSource.iff_of_iSup_eq_top (P := @Smooth)
    (fun index : Fin 2 =>
      Proj.basicOpen Grading (MvPolynomial.X index : CoordinateRing))
    (coordinateBasicOpens_iSup_eq_top 2)]
  intro index
  rw [← MorphismProperty.cancel_left_of_respectsIso (P := @Smooth)
      (Proj.basicOpenIsoSpec Grading (MvPolynomial.X index : CoordinateRing)
        (variable_mem_degree_one 2 index) (by norm_num)).inv,
    ← Category.assoc, ← Proj.awayι, Proj.awayι_toSpecZero,
    HasRingHomProperty.Spec_iff (P := @Smooth)]
  fin_cases index
  · exact fromZeroRingHom_first_smooth
  · exact fromZeroRingHom_second_smooth

/-- [proved-standard; formal-checked] The genuine standard projective-line presentation is smooth
over the complex receiver after rebasing its exact degree-zero coefficient line. -/
theorem presentation_structureMap_smooth :
    Smooth (HodgeProjectiveSpaceAmbient.presentation 2).structureMap := by
  haveI projectionSmooth : Smooth (Proj.toSpecZero Grading) := toSpecZero_smooth
  haveI embeddingSmooth : Smooth (𝟙 ProjectiveLineScheme) := inferInstance
  haveI baseTransportSmooth :
      Smooth (HodgeProjectiveSpaceAmbient.baseIso 2).hom := inferInstance
  change Smooth
    ((𝟙 ProjectiveLineScheme ≫ Proj.toSpecZero Grading) ≫
      (HodgeProjectiveSpaceAmbient.baseIso 2).hom)
  haveI firstPassageSmooth :
      Smooth (𝟙 ProjectiveLineScheme ≫ Proj.toSpecZero Grading) :=
    smooth_comp (𝟙 ProjectiveLineScheme) (Proj.toSpecZero Grading)
  exact @smooth_comp _ _
    (𝟙 ProjectiveLineScheme ≫ Proj.toSpecZero Grading) _
    (HodgeProjectiveSpaceAmbient.baseIso 2).hom
    firstPassageSmooth baseTransportSmooth

/-- [proved-standard; formal-checked] The first positive-dimensional source carrier is an actual
smooth projective complex scheme, not a detached topology or a certificate-shaped surrogate. -/
def carrier : SmoothProjectiveComplexScheme where
  X := ProjectiveLineScheme
  projective := HodgeProjectiveSpaceAmbient.presentation 2
  smooth := presentation_structureMap_smooth

/-- [proved-standard; formal-checked] The smooth projective-line carrier has an actual point. -/
theorem carrier_nonempty : Nonempty carrier.X :=
  projectiveScheme_nonempty (by norm_num)

section Audit

#print axioms awaySecondToPolynomial_mk
#print axioms homogenize_dehomogenize_of_homogeneous
#print axioms awaySecondToPolynomial_injective
#print axioms awaySecondToPolynomial_surjective
#print axioms awaySecondEquivPolynomial
#print axioms fromZeroRingHom_second_smooth
#print axioms coordinateSwap_involutive
#print axioms awayFirstToPolynomial_injective
#print axioms awayFirstToPolynomial_surjective
#print axioms awayFirstEquivPolynomial
#print axioms fromZeroRingHom_first_smooth
#print axioms toSpecZero_smooth
#print axioms presentation_structureMap_smooth
#print axioms carrier
#print axioms carrier_nonempty

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineScheme
