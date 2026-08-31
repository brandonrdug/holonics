import ElementaryHolonics.Millennium.HodgeSurfaceType11Period

/-!
# Smooth closed `(1,1)` currents on every finite power of the projective line

The completed two-factor validation is enlarged analytically to the genuine finite family
`(ℙ¹)^n`.  A single `Fin n` operation pulls the projective-line Fubini--Study certificate through
each coordinate projection.  Every rational coordinate current is smooth, closed, type `(1,1)`,
and overlap-compatible.  Its unit-winding period ledger reconstructs every source coefficient.

This file does not identify the coordinate ledger with singular cohomology of every power.  It
constructs the analytic source and its exact reconstruction receiver so that the remaining edge is
only the source-specific singular Künneth/cycle-class passage.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLinePowerType11

open Soma.Holonics.Millennium.HodgeProjectiveLineAtlas
open Soma.Holonics.Millennium.HodgeProjectiveLineHolomorphicAtlas
open Soma.Holonics.Millennium.HodgeProjectiveLineType11Form

/-- [definition] One affine chart of the finite projective-line power. -/
abbrev PowerPoint (factorCount : ℕ) := Fin factorCount → ℂ

/-- [definition] The independently addressed projective chart at every factor. -/
abbrev PowerChart (factorCount : ℕ) := Fin factorCount → AffineChart

/-- [definition] Rational coefficients of the factor Fubini--Study currents. -/
abbrev PowerCoefficients (factorCount : ℕ) := Fin factorCount → ℚ

/-- [definition] Coordinatewise complex structure on an affine power chart. -/
def powerComplexStructure {factorCount : ℕ} (tangent : PowerPoint factorCount) :
    PowerPoint factorCount :=
  fun index => Complex.I * tangent index

/-- [definition] Coordinatewise projective transition. -/
def powerTransition {factorCount : ℕ}
    (source target : PowerChart factorCount) (z : PowerPoint factorCount) :
    PowerPoint factorCount :=
  fun index => transition (source index) (target index) (z index)

/-- [definition] The complete overlap aperture, retaining every factor condition. -/
def PowerTransitionAdmissible {factorCount : ℕ}
    (source target : PowerChart factorCount) (z : PowerPoint factorCount) : Prop :=
  ∀ index, TransitionAdmissible (source index) (target index) (z index)

/-- [definition] Coordinatewise derivative transport across the power-chart transition. -/
def powerTransitionTangent {factorCount : ℕ}
    (source target : PowerChart factorCount)
    (z tangent : PowerPoint factorCount) : PowerPoint factorCount :=
  fun index => transitionTangent (source index) (target index) (z index) (tangent index)

/-- [definition] The real-linear projection to one addressed factor. -/
def powerFactorProjection {factorCount : ℕ} (index : Fin factorCount) :
    PowerPoint factorCount →L[ℝ] ℂ :=
  ContinuousLinearMap.proj index

@[simp]
theorem powerFactorProjection_apply {factorCount : ℕ}
    (index : Fin factorCount) (point : PowerPoint factorCount) :
    powerFactorProjection index point = point index := rfl

/-- [definition] The factor Fubini--Study form as a pointwise alternating current. -/
def powerFactorForm {factorCount : ℕ} (index : Fin factorCount)
    (z first second : PowerPoint factorCount) : ℝ :=
  fsForm (z index) (first index) (second index)

/-- [proved-derived; formal-checked] Every addressed factor form has type `(1,1)`. -/
theorem powerFactorForm_isType11 {factorCount : ℕ} (index : Fin factorCount)
    (z first second : PowerPoint factorCount) :
    powerFactorForm index z (powerComplexStructure first) (powerComplexStructure second) =
      powerFactorForm index z first second := by
  exact fsForm_isType11 (z index) (first index) (second index)

/-- [proved-derived; formal-checked] Every factor form obeys the complete power-chart overlap
law. -/
theorem powerFactorForm_transition {factorCount : ℕ} (index : Fin factorCount)
    (source target : PowerChart factorCount) (z : PowerPoint factorCount)
    (hadmitted : PowerTransitionAdmissible source target z)
    (first second : PowerPoint factorCount) :
    powerFactorForm index (powerTransition source target z)
        (powerTransitionTangent source target z first)
        (powerTransitionTangent source target z second) =
      powerFactorForm index z first second := by
  exact fsForm_transition (source index) (target index) (z index)
    (hadmitted index) (first index) (second index)

/-- [definition] The actual differential-form pullback to one factor of the affine power chart. -/
def powerFactorDifferentialForm {factorCount : ℕ} (index : Fin factorCount)
    (z : PowerPoint factorCount) :
    PowerPoint factorCount [⋀^Fin 2]→L[ℝ] ℝ :=
  (fsDifferentialForm (powerFactorProjection index z)).compContinuousLinearMap
    (powerFactorProjection index)

/-- [proved-derived; formal-checked] The bundled factor differential form realizes the pointwise
factor current. -/
theorem powerFactorDifferentialForm_apply {factorCount : ℕ} (index : Fin factorCount)
    (z first second : PowerPoint factorCount) :
    powerFactorDifferentialForm index z ![first, second] =
      powerFactorForm index z first second := by
  change fsDifferentialForm (z index)
      ((fun vector => vector index) ∘ ![first, second]) = _
  rw [show (fun vector : PowerPoint factorCount => vector index) ∘ ![first, second] =
      ![first index, second index] by
    ext position
    fin_cases position <;> rfl]
  exact fsDifferentialForm_apply (z index) (first index) (second index)

/-- [proved-derived; formal-checked] Every factor pullback is smooth. -/
theorem powerFactorDifferentialForm_contDiff {factorCount : ℕ}
    (index : Fin factorCount) :
    ContDiff ℝ ⊤ (powerFactorDifferentialForm index) := by
  unfold powerFactorDifferentialForm
  exact (ContinuousAlternatingMap.compContinuousLinearMapCLM
      (powerFactorProjection index)).contDiff.comp
    (fsDifferentialForm_contDiff.comp (powerFactorProjection index).contDiff)

/-- [proved-derived; formal-checked] Closedness transports through every factor projection. -/
theorem powerFactorDifferentialForm_closed {factorCount : ℕ}
    (index : Fin factorCount) (z : PowerPoint factorCount) :
    extDeriv (powerFactorDifferentialForm index) z = 0 := by
  have hpull := extDeriv_pullback
    (x := z) (n := 2) (r := ⊤)
    (fsDifferentialForm_contDiff.differentiable (by simp)).differentiableAt
    (powerFactorProjection index).contDiff.contDiffAt
    (by simp)
  have hderiv : ∀ point,
      fderiv ℝ (powerFactorProjection index) point = powerFactorProjection index :=
    fun _ => (powerFactorProjection index).hasFDerivAt.fderiv
  simp_rw [hderiv] at hpull
  rw [fsDifferentialForm_closed] at hpull
  have hzero :
      (0 : ℂ [⋀^Fin 3]→L[ℝ] ℝ).compContinuousLinearMap
        (powerFactorProjection index) = 0 := by
    ext vectors
    rfl
  rw [hzero] at hpull
  change extDeriv
    (fun point =>
      (fsDifferentialForm (powerFactorProjection index point)).compContinuousLinearMap
        (powerFactorProjection index)) z = 0
  exact hpull

/-- [definition] A rational linear combination of all addressed factor currents. -/
def powerType11Current {factorCount : ℕ} (coefficients : PowerCoefficients factorCount)
    (z first second : PowerPoint factorCount) : ℝ :=
  ∑ index, (coefficients index : ℝ) * powerFactorForm index z first second

/-- [definition] The same current as a genuine differential two-form. -/
def powerType11DifferentialForm {factorCount : ℕ}
    (coefficients : PowerCoefficients factorCount) (z : PowerPoint factorCount) :
    PowerPoint factorCount [⋀^Fin 2]→L[ℝ] ℝ :=
  ∑ index, (coefficients index : ℝ) • powerFactorDifferentialForm index z

/-- [proved-derived; formal-checked] The bundled finite sum realizes the pointwise current. -/
theorem powerType11DifferentialForm_apply {factorCount : ℕ}
    (coefficients : PowerCoefficients factorCount)
    (z first second : PowerPoint factorCount) :
    powerType11DifferentialForm coefficients z ![first, second] =
      powerType11Current coefficients z first second := by
  simp [powerType11DifferentialForm, powerType11Current,
    powerFactorDifferentialForm_apply]

/-- [proved-derived; formal-checked] Rational factor sums retain type `(1,1)`. -/
theorem powerType11Current_isType11 {factorCount : ℕ}
    (coefficients : PowerCoefficients factorCount)
    (z first second : PowerPoint factorCount) :
    powerType11Current coefficients z
        (powerComplexStructure first) (powerComplexStructure second) =
      powerType11Current coefficients z first second := by
  apply Finset.sum_congr rfl
  intro index _
  rw [powerFactorForm_isType11]

/-- [proved-derived; formal-checked] Rational factor sums retain exact overlap gluing. -/
theorem powerType11Current_transition {factorCount : ℕ}
    (coefficients : PowerCoefficients factorCount)
    (source target : PowerChart factorCount) (z : PowerPoint factorCount)
    (hadmitted : PowerTransitionAdmissible source target z)
    (first second : PowerPoint factorCount) :
    powerType11Current coefficients (powerTransition source target z)
        (powerTransitionTangent source target z first)
        (powerTransitionTangent source target z second) =
      powerType11Current coefficients z first second := by
  apply Finset.sum_congr rfl
  intro index _
  rw [powerFactorForm_transition index source target z hadmitted first second]

/-- [proved-derived; formal-checked] Every rational factor sum is smooth. -/
theorem powerType11DifferentialForm_contDiff {factorCount : ℕ}
    (coefficients : PowerCoefficients factorCount) :
    ContDiff ℝ ⊤ (powerType11DifferentialForm coefficients) := by
  apply ContDiff.sum
  intro index _
  exact (powerFactorDifferentialForm_contDiff index).const_smul (coefficients index : ℝ)

/-- [proved-derived; formal-checked] A finite sum of smooth closed factor currents is closed. -/
theorem powerType11DifferentialForm_closed {factorCount : ℕ}
    (coefficients : PowerCoefficients factorCount) (z : PowerPoint factorCount) :
    extDeriv (powerType11DifferentialForm coefficients) z = 0 := by
  classical
  let summand := fun index : Fin factorCount =>
    (coefficients index : ℝ) • powerFactorDifferentialForm index
  have hsmooth : ∀ index, ContDiff ℝ ⊤ (summand index) := fun index =>
    (powerFactorDifferentialForm_contDiff index).const_smul (coefficients index : ℝ)
  have hclosed : ∀ index, extDeriv (summand index) z = 0 := by
    intro index
    change extDeriv ((coefficients index : ℝ) • powerFactorDifferentialForm index) z = 0
    rw [extDeriv_fun_smul, powerFactorDifferentialForm_closed]
    simp
  have hzero : extDeriv
      (fun _ : PowerPoint factorCount =>
        (0 : PowerPoint factorCount [⋀^Fin 2]→L[ℝ] ℝ)) z = 0 := by
    change extDeriv
      (0 : PowerPoint factorCount →
        PowerPoint factorCount [⋀^Fin 2]→L[ℝ] ℝ) z = 0
    simpa using (extDeriv_fun_smul
      (x := z) (n := 2) (c := (0 : ℝ))
      (ω := fun _ : PowerPoint factorCount =>
        (0 : PowerPoint factorCount [⋀^Fin 2]→L[ℝ] ℝ)))
  have hsum : ∀ indices : Finset (Fin factorCount),
      extDeriv (fun point => indices.sum fun index => summand index point) z = 0 := by
    intro indices
    induction indices using Finset.induction_on with
    | empty => simpa using hzero
    | @insert index indices hindex induction =>
        have hfunction :
            (fun point => (insert index indices).sum fun factor => summand factor point) =
              fun point => summand index point +
                indices.sum fun factor => summand factor point := by
          funext point
          rw [Finset.sum_insert hindex]
        rw [hfunction]
        rw [extDeriv_fun_add
          ((hsmooth index).differentiable (by simp)).differentiableAt
          ((ContDiff.sum fun factor _ => hsmooth factor).differentiable
            (by simp)).differentiableAt]
        rw [hclosed index, induction, add_zero]
  change extDeriv (fun point => ∑ index, summand index point) z = 0
  exact hsum Finset.univ

/-- [definition] Exact rational evaluation of a factor current on a coordinate ruling ledger. -/
def powerRulingEvaluation {factorCount : ℕ}
    (coefficients homology : PowerCoefficients factorCount) : ℚ :=
  ∑ index, coefficients index * homology index

/-- [definition] The analytic unit-winding period functional. -/
def powerType11PeriodFunctional {factorCount : ℕ}
    (coefficients : PowerCoefficients factorCount) :
    Module.Dual ℚ (PowerCoefficients factorCount) where
  toFun homology := projectiveLineType11Certificate.integralWinding *
    powerRulingEvaluation coefficients homology
  map_add' left right := by
    simp [powerRulingEvaluation, mul_add, Finset.sum_add_distrib]
  map_smul' coefficient homology := by
    simp only [projectiveLineType11Certificate, one_mul, PowerCoefficients,
      powerRulingEvaluation, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    simp only [RingHom.id_apply]
    ring

/-- [proved-derived; formal-checked] The carried winding normalization leaves the exact dot
ledger. -/
theorem powerType11PeriodFunctional_eq_evaluation {factorCount : ℕ}
    (coefficients homology : PowerCoefficients factorCount) :
    powerType11PeriodFunctional coefficients homology =
      powerRulingEvaluation coefficients homology := by
  simp [powerType11PeriodFunctional]

/-- [definition] The addressed unit coordinate ruling. -/
def powerRulingBasis {factorCount : ℕ} (index : Fin factorCount) :
    PowerCoefficients factorCount :=
  Pi.single index 1

/-- [proved-derived; formal-checked] Period on an addressed coordinate ruling returns exactly the
source coefficient. -/
theorem powerType11Period_basis {factorCount : ℕ}
    (coefficients : PowerCoefficients factorCount) (index : Fin factorCount) :
    powerType11PeriodFunctional coefficients (powerRulingBasis index) =
      coefficients index := by
  classical
  rw [powerType11PeriodFunctional_eq_evaluation]
  unfold powerRulingEvaluation powerRulingBasis
  rw [Finset.sum_eq_single index]
  · simp
  · intro other _ hne
    simp [hne]
  · simp

/-- [proved-derived; formal-checked] The complete coordinate period family reconstructs the
analytic source coefficients. -/
theorem coefficients_eq_of_periods_eq {factorCount : ℕ}
    {left right : PowerCoefficients factorCount}
    (periodsEqual : ∀ index,
      powerType11PeriodFunctional left (powerRulingBasis index) =
        powerType11PeriodFunctional right (powerRulingBasis index)) :
    left = right := by
  funext index
  simpa only [powerType11Period_basis] using periodsEqual index

/-- [proved-derived; formal-checked] One source-indexed object retains the finite-power form,
smooth/closed/type/overlap laws, and its reconstructing period family. -/
structure PowerType11AnalyticCertificate {factorCount : ℕ}
    (coefficients : PowerCoefficients factorCount) where
  differentialForm : PowerPoint factorCount →
    PowerPoint factorCount [⋀^Fin 2]→L[ℝ] ℝ
  realizesCurrent : ∀ z first second,
    differentialForm z ![first, second] = powerType11Current coefficients z first second
  smooth : ContDiff ℝ ⊤ differentialForm
  closed : ∀ z, extDeriv differentialForm z = 0
  type11 : ∀ z first second,
    powerType11Current coefficients z
        (powerComplexStructure first) (powerComplexStructure second) =
      powerType11Current coefficients z first second
  overlap : ∀ source target z,
    PowerTransitionAdmissible source target z → ∀ first second,
      powerType11Current coefficients (powerTransition source target z)
          (powerTransitionTangent source target z first)
          (powerTransitionTangent source target z second) =
        powerType11Current coefficients z first second
  periods : Module.Dual ℚ (PowerCoefficients factorCount)
  periods_eq : periods = powerType11PeriodFunctional coefficients

/-- [proved-derived; formal-checked] Every finite factor population supplies the complete analytic
certificate. -/
def powerType11AnalyticCertificate {factorCount : ℕ}
    (coefficients : PowerCoefficients factorCount) :
    PowerType11AnalyticCertificate coefficients where
  differentialForm := powerType11DifferentialForm coefficients
  realizesCurrent := powerType11DifferentialForm_apply coefficients
  smooth := powerType11DifferentialForm_contDiff coefficients
  closed := powerType11DifferentialForm_closed coefficients
  type11 := powerType11Current_isType11 coefficients
  overlap := powerType11Current_transition coefficients
  periods := powerType11PeriodFunctional coefficients
  periods_eq := rfl

section Audit

#print axioms powerFactorDifferentialForm_closed
#print axioms powerType11DifferentialForm_contDiff
#print axioms powerType11DifferentialForm_closed
#print axioms powerType11Period_basis
#print axioms coefficients_eq_of_periods_eq
#print axioms powerType11AnalyticCertificate

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLinePowerType11
