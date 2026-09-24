import ElementaryHolonics.Millennium.NavierStokesAdaptiveRectangleH3Service
import ElementaryHolonics.Millennium.NavierStokesCriticalEnergySquareSeparator
import ElementaryHolonics.Millennium.NavierStokesScaling
import ElementaryHolonics.Millennium.NavierStokesTerminalCompactEndpointExhaustion

/-!
# The restart/matched endpoint trace and its first exact separator

**[proved-derived; formal-checked]**  The adjacent-shell restart payment does not introduce a
hidden multiplicity: it is exactly the sum of the complete dyadic shell population and its
one-step tail, hence at most twice the complete shell mass at the same initial face.

Along the explicit compact exhaustion, the matched cofinal service retains two different endpoint
traces.  The initial vorticity coefficient mass is evaluated at the left face, while the cubic
native `H³` chart spans the whole interval and therefore approaches the absent terminal face.
The exact scaling ledger assigns the latter trace weight `7/2` after its two time-length factors;
it is not a critical energy/enstrophy current.  The already-founded cubic-shell separator then
shows that even the stronger energy-paid frozen square receiver cannot uniformly pay the doubled
absolute shell mass which the restart word can present.

The final theorem gives the strongest direct endpoint factorization available here: raw uniform
bounds on the two actual traces imply one explicit uniform matched-service bound.  It does not
postulate, rename, or construct either trace bound, and it makes no terminal-regularity or
Navier--Stokes completion claim.
-/

noncomputable section

open Filter Real Set
open scoped BigOperators

namespace Soma.Holonics.Millennium.NavierStokesRestartMatchedEndpointTrace

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAdaptiveMatchedCofinalDiagonal
open Soma.Holonics.Millennium.NavierStokesCriticalEnergySquareSeparator
open Soma.Holonics.Millennium.NavierStokesDyadicShellProjectors
open Soma.Holonics.Millennium.NavierStokesFiniteLinearRadiusTailPassage
open Soma.Holonics.Millennium.NavierStokesH3BilinearNorm
open Soma.Holonics.Millennium.NavierStokesOpenLifespan
open Soma.Holonics.Millennium.NavierStokesPhaseLocalDyadicTerminalBridge
open Soma.Holonics.Millennium.NavierStokesScaling
open Soma.Holonics.Millennium.NavierStokesSmoothDyadicMildPackingEquivalence
open Soma.Holonics.Millennium.NavierStokesTerminalCompactEndpointExhaustion
open Soma.Holonics.Millennium.NavierStokesTorusFourier
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionRemainderBound
open Soma.Holonics.Millennium.NavierStokesVorticityDirectionCoherenceSummability

/-! ## The exact adjacent-shell restart trace -/

/-- The restart payment is literally the complete shell mass plus its one-step tail. -/
theorem smoothRestartCoefficientPayment_eq_shell_tsum_add_tail
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hsT : s < T) :
    smoothRestartCoefficientPayment solution hs hsT =
      (∑' scale : ℕ,
        openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨s, hs, hsT⟩ scale) +
      ∑' scale : ℕ,
        openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨s, hs, hsT⟩ (scale + 1) := by
  unfold smoothRestartCoefficientPayment
  rw [(summable_openPeriodicVorticityDyadicShellCoefficientMass
      solution ⟨s, hs, hsT⟩).tsum_add
    ((summable_nat_add_iff 1).2
      (summable_openPeriodicVorticityDyadicShellCoefficientMass
        solution ⟨s, hs, hsT⟩))]

/-- Adjacent shells cost at most a factor two over the complete shell population at the same
addressed time face. -/
theorem smoothRestartCoefficientPayment_le_two_mul_shellTsum
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hsT : s < T) :
    smoothRestartCoefficientPayment solution hs hsT ≤
      2 * (∑' scale : ℕ,
        openPeriodicVorticityDyadicShellCoefficientMass solution
          ⟨s, hs, hsT⟩ scale) := by
  let mass : ℕ → ℝ := fun scale ↦
    openPeriodicVorticityDyadicShellCoefficientMass solution
      ⟨s, hs, hsT⟩ scale
  have hmass : Summable mass :=
    summable_openPeriodicVorticityDyadicShellCoefficientMass solution ⟨s, hs, hsT⟩
  have hzero : 0 ≤ mass 0 :=
    openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution ⟨s, hs, hsT⟩ 0
  have hsplit : mass 0 + (∑' scale : ℕ, mass (scale + 1)) =
      ∑' scale : ℕ, mass scale := by
    simpa only [Finset.sum_range_one] using hmass.sum_add_tsum_nat_add 1
  have htail : (∑' scale : ℕ, mass (scale + 1)) ≤ ∑' scale : ℕ, mass scale := by
    exact (le_add_of_nonneg_left hzero).trans_eq hsplit
  rw [smoothRestartCoefficientPayment_eq_shell_tsum_add_tail]
  change (∑' scale : ℕ, mass scale) +
      (∑' scale : ℕ, mass (scale + 1)) ≤
    2 * ∑' scale : ℕ, mass scale
  linarith

/-- The complete sharp shell population is a subpopulation of the literal full vorticity
coefficient mass: the low cube is retained rather than silently discarded. -/
theorem tsum_openPeriodicVorticityDyadicShellCoefficientMass_le_fullMass
    {T nu : ℝ} {initial : InitialVelocity} {force velocity : VelocityField}
    {pressure : PressureField}
    (solution : OpenPeriodicSolutionOn T nu initial force velocity pressure)
    (t : Ioo 0 T) :
    (∑' scale : ℕ,
        openPeriodicVorticityDyadicShellCoefficientMass solution t scale) ≤
      openPeriodicFullVorticityCoefficientMass solution t := by
  let mass : SpatialFrequency → ℝ := fun frequency ↦
    complexVectorL1 (openPeriodicVorticityFourierMode solution t frequency)
  have hmass : Summable mass :=
    summable_complexVectorL1_openPeriodicVorticityFourierMode solution t
  apply Real.tsum_le_of_sum_range_le
    (openPeriodicVorticityDyadicShellCoefficientMass_nonneg solution t)
  intro depth
  have hpartition :
      (∑ frequency ∈ lowFrequencyModes, mass frequency) +
          (∑ level ∈ Finset.range depth,
            ∑ frequency ∈ dyadicFrequencyShell level, mass frequency) =
        ∑ frequency ∈ frequencyCube (dyadicRadius depth), mass frequency := by
    induction depth with
    | zero =>
        simp [dyadicRadius, lowFrequencyModes]
    | succ depth ih =>
        have hsubset :
            frequencyCube (dyadicRadius depth) ⊆
              frequencyCube (dyadicRadius (depth + 1)) :=
          frequencyCube_mono
            (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ depth))
        have hsplit := Finset.sum_sdiff (f := mass) hsubset
        calc
          (∑ frequency ∈ lowFrequencyModes, mass frequency) +
              (∑ level ∈ Finset.range (depth + 1),
                ∑ frequency ∈ dyadicFrequencyShell level, mass frequency) =
            ((∑ frequency ∈ lowFrequencyModes, mass frequency) +
                (∑ level ∈ Finset.range depth,
                  ∑ frequency ∈ dyadicFrequencyShell level, mass frequency)) +
              ∑ frequency ∈ dyadicFrequencyShell depth, mass frequency := by
                rw [Finset.sum_range_succ]
                ring
          _ = (∑ frequency ∈ frequencyCube (dyadicRadius depth), mass frequency) +
              ∑ frequency ∈ dyadicFrequencyShell depth, mass frequency := by rw [ih]
          _ = ∑ frequency ∈ frequencyCube (dyadicRadius (depth + 1)),
              mass frequency := by
            simpa only [dyadicFrequencyShell, add_comm] using hsplit
  calc
    (∑ level ∈ Finset.range depth,
        openPeriodicVorticityDyadicShellCoefficientMass solution t level) ≤
      (∑ frequency ∈ lowFrequencyModes, mass frequency) +
        (∑ level ∈ Finset.range depth,
          ∑ frequency ∈ dyadicFrequencyShell level, mass frequency) := by
      unfold openPeriodicVorticityDyadicShellCoefficientMass mass
      exact le_add_of_nonneg_left
        (Finset.sum_nonneg fun frequency _ ↦ complexVectorL1_nonneg _)
    _ = ∑ frequency ∈ frequencyCube (dyadicRadius depth), mass frequency := hpartition
    _ ≤ ∑' frequency : SpatialFrequency, mass frequency :=
      hmass.sum_le_tsum _ (fun frequency _ ↦ complexVectorL1_nonneg _)
    _ = openPeriodicFullVorticityCoefficientMass solution t := rfl

/-- The actual restart payment is bounded by twice the literal full coefficient mass at the
same addressed time. -/
theorem smoothRestartCoefficientPayment_le_two_mul_fullMass
    {T nu s : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hs : 0 < s) (hsT : s < T) :
    smoothRestartCoefficientPayment solution hs hsT ≤
      2 * openPeriodicFullVorticityCoefficientMass solution ⟨s, hs, hsT⟩ :=
  (smoothRestartCoefficientPayment_le_two_mul_shellTsum solution hs hsT).trans
    (mul_le_mul_of_nonneg_left
      (tsum_openPeriodicVorticityDyadicShellCoefficientMass_le_fullMass
        solution ⟨s, hs, hsT⟩)
      (by norm_num))

/-! ## The explicit exhaustion retains a terminal H³ trace -/

/-- The exact time length of the `n`th exhaustion rectangle. -/
theorem smoothTerminalExhaustion_intervalLength
    (T : ℝ) (n : ℕ) :
    smoothTerminalExhaustionRight T n -
        smoothTerminalExhaustionLeft T n =
      T * ((n : ℝ) / ((n : ℝ) + 1)) := by
  unfold smoothTerminalExhaustionRight smoothTerminalExhaustionLeft
    smoothTerminalExhaustionRadius
  field_simp
  ring

theorem smoothTerminalExhaustion_intervalLength_nonneg
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    0 ≤ smoothTerminalExhaustionRight T n -
      smoothTerminalExhaustionLeft T n := by
  exact sub_nonneg.mpr (smoothTerminalExhaustionLeft_le_right hT n)

theorem smoothTerminalExhaustion_intervalLength_le
    {T : ℝ} (hT : 0 < T) (n : ℕ) :
    smoothTerminalExhaustionRight T n -
        smoothTerminalExhaustionLeft T n ≤ T := by
  rw [smoothTerminalExhaustion_intervalLength]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hratio : (n : ℝ) / ((n : ℝ) + 1) ≤ 1 := by
    exact (div_le_one hden).2 (by linarith)
  simpa using mul_le_mul_of_nonneg_left hratio hT.le

/-- Along the explicit exhaustion, the same raw full-coefficient trace which appears in the
matched service uniformly pays the actual restart term.  No terminal face is invoked. -/
theorem smoothRestartCoefficientPayment_exhaustion_le_of_actualTraceBound
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (massBound : ℝ)
    (hmass : ∀ n : ℕ,
      openPeriodicFullVorticityCoefficientMass solution
          ⟨smoothTerminalExhaustionLeft T n,
            smoothTerminalExhaustionLeft_pos solution.terminal_pos n,
            (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
              (smoothTerminalExhaustionRight_lt solution.terminal_pos n)⟩ ≤ massBound) :
    ∀ n : ℕ,
      smoothRestartCoefficientPayment solution
          (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
          ((smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
            (smoothTerminalExhaustionRight_lt solution.terminal_pos n)) ≤
        2 * massBound := by
  intro n
  exact (smoothRestartCoefficientPayment_le_two_mul_fullMass solution
      (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
      ((smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
        (smoothTerminalExhaustionRight_lt solution.terminal_pos n))).trans
    (mul_le_mul_of_nonneg_left (hmass n) (by norm_num))

/-- The cubic `H³` term of the matched square service has positive parabolic weight after both
time-length factors are retained.  Thus it is not one of the weight-zero energy currents. -/
theorem matchedH3ExhaustionTrace_has_supercritical_weight :
    2 * (-2 : ℚ) + 3 * sobolevWeight 3 3 = 7 / 2 ∧
      2 * (-2 : ℚ) + 3 * sobolevWeight 3 3 ≠ 0 := by
  norm_num [sobolevWeight]

/-- Raw uniform bounds on the two actual traces return an explicit uniform matched-service
bound.  The theorem deliberately asks for the raw inequalities and introduces no renamed
terminal-control predicate. -/
theorem compactAdaptiveMatchedUniformPrefixSquareService_exhaustion_le_of_actualTraceBounds
    {T nu : ℝ} {initial : InitialVelocity} {velocity : VelocityField}
    {pressure : PressureField}
    (solution :
      OpenPeriodicSolutionOn T nu initial (0 : VelocityField) velocity pressure)
    (hnu : 0 < nu) (massBound h3Bound : ℝ)
    (hmassBound : 0 ≤ massBound)
    (hmass : ∀ n : ℕ,
      openPeriodicFullVorticityCoefficientMass solution
          ⟨smoothTerminalExhaustionLeft T n,
            smoothTerminalExhaustionLeft_pos solution.terminal_pos n,
            (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
              (smoothTerminalExhaustionRight_lt solution.terminal_pos n)⟩ ≤ massBound)
    (hh3 : ∀ n : ℕ,
      ‖compactOpenVelocityWeightedH3StateChart solution
          (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
          (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n)
          (smoothTerminalExhaustionRight_lt solution.terminal_pos n)‖ ≤ h3Bound) :
    ∀ n : ℕ,
      compactAdaptiveMatchedUniformPrefixSquareService solution
          (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
          (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n)
          (smoothTerminalExhaustionRight_lt solution.terminal_pos n) ≤
        nu⁻¹ * (1024 * T *
          ((1 / 2 : ℝ) * massBound ^ 2 +
            T * ((2519424 * periodicH3EmbeddingConstant) * h3Bound ^ 3))) := by
  intro n
  let a := smoothTerminalExhaustionLeft T n
  let b := smoothTerminalExhaustionRight T n
  have hlengthNonneg : 0 ≤ b - a :=
    smoothTerminalExhaustion_intervalLength_nonneg solution.terminal_pos n
  have hlength : b - a ≤ T :=
    smoothTerminalExhaustion_intervalLength_le solution.terminal_pos n
  have hmassNonneg := openPeriodicFullVorticityCoefficientMass_nonneg solution
    ⟨a, smoothTerminalExhaustionLeft_pos solution.terminal_pos n,
      (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
        (smoothTerminalExhaustionRight_lt solution.terminal_pos n)⟩
  have hmassSq :
      openPeriodicFullVorticityCoefficientMass solution
          ⟨a, smoothTerminalExhaustionLeft_pos solution.terminal_pos n,
            (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
              (smoothTerminalExhaustionRight_lt solution.terminal_pos n)⟩ ^ 2 ≤
        massBound ^ 2 :=
    (sq_le_sq₀ hmassNonneg hmassBound).2 (hmass n)
  have hchartNonneg : 0 ≤
      ‖compactOpenVelocityWeightedH3StateChart solution
        (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
        (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n)
        (smoothTerminalExhaustionRight_lt solution.terminal_pos n)‖ := norm_nonneg _
  have hchartCube :
      ‖compactOpenVelocityWeightedH3StateChart solution
          (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
          (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n)
          (smoothTerminalExhaustionRight_lt solution.terminal_pos n)‖ ^ 3 ≤
        h3Bound ^ 3 := by
    exact pow_le_pow_left₀ hchartNonneg (hh3 n) 3
  unfold compactAdaptiveMatchedUniformPrefixSquareService
  have hconstant : 0 ≤ 2519424 * periodicH3EmbeddingConstant :=
    mul_nonneg (by norm_num) periodicH3EmbeddingConstant_nonneg
  have hterminalNonneg : 0 ≤ T := solution.terminal_pos.le
  have hinner :
      (1 / 2 : ℝ) *
          openPeriodicFullVorticityCoefficientMass solution
            ⟨smoothTerminalExhaustionLeft T n,
              smoothTerminalExhaustionLeft_pos solution.terminal_pos n,
              (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n).trans_lt
                (smoothTerminalExhaustionRight_lt solution.terminal_pos n)⟩ ^ 2 +
        (smoothTerminalExhaustionRight T n - smoothTerminalExhaustionLeft T n) *
          ((2519424 * periodicH3EmbeddingConstant) *
            ‖compactOpenVelocityWeightedH3StateChart solution
              (smoothTerminalExhaustionLeft_pos solution.terminal_pos n)
              (smoothTerminalExhaustionLeft_le_right solution.terminal_pos n)
              (smoothTerminalExhaustionRight_lt solution.terminal_pos n)‖ ^ 3) ≤
      (1 / 2 : ℝ) * massBound ^ 2 +
        T * ((2519424 * periodicH3EmbeddingConstant) * h3Bound ^ 3) := by
    gcongr
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul (mul_le_mul_of_nonneg_left hlength (by norm_num)) hinner
      (add_nonneg
        (mul_nonneg (by norm_num) (sq_nonneg _))
        (mul_nonneg hlengthNonneg
          (mul_nonneg hconstant (pow_nonneg hchartNonneg 3))))
      (mul_nonneg (by positivity) solution.terminal_pos.le))
    (inv_nonneg.mpr hnu.le)

/-! ## The energy-square route cannot pay the restart shell receiver -/

/-- One interior shell is counted twice by the adjacent-shell restart word. -/
def criticalRestartShellPayment
    {level : ℕ} (carrier : CriticalEnergyShellSection level) : ℝ :=
  2 * criticalEnergyShellAbsoluteMass carrier

/-- The unit shell retains the exact doubled absolute population. -/
theorem unitCriticalEnergyShellSection_restartPayment (level : ℕ) :
    criticalRestartShellPayment (unitCriticalEnergyShellSection level) =
      2 * (criticalEnergyShellRadius level : ℝ) ^ 3 := by
  rw [criticalRestartShellPayment,
    unitCriticalEnergyShellSection_absoluteMass]

/-- No scale-independent coefficient factors the restart shell receiver through the strongest
energy-paid frozen square face. -/
theorem no_uniform_criticalRestartShellPayment_factorization_through_energyPaidFrozenSquare :
    ¬ ∃ coefficient : ℝ, ∀ (level : ℕ)
        (carrier : CriticalEnergyShellSection level),
      criticalRestartShellPayment carrier ≤
        coefficient * energyPaidFrozenShellSquareNorm carrier := by
  rintro ⟨coefficient, hcoefficient⟩
  apply no_uniform_absoluteMass_factorization_through_energyPaidFrozenSquare
  refine ⟨coefficient, ?_⟩
  intro level carrier
  have hnonneg : 0 ≤ criticalEnergyShellAbsoluteMass carrier := by
    unfold criticalEnergyShellAbsoluteMass
    exact Finset.sum_nonneg fun occurrence _ ↦ norm_nonneg _
  exact (le_mul_of_one_le_left hnonneg (by norm_num)).trans
    (hcoefficient level carrier)

section Audit

#print axioms smoothRestartCoefficientPayment_eq_shell_tsum_add_tail
#print axioms smoothRestartCoefficientPayment_le_two_mul_shellTsum
#print axioms tsum_openPeriodicVorticityDyadicShellCoefficientMass_le_fullMass
#print axioms smoothRestartCoefficientPayment_le_two_mul_fullMass
#print axioms smoothTerminalExhaustion_intervalLength
#print axioms smoothRestartCoefficientPayment_exhaustion_le_of_actualTraceBound
#print axioms matchedH3ExhaustionTrace_has_supercritical_weight
#print axioms compactAdaptiveMatchedUniformPrefixSquareService_exhaustion_le_of_actualTraceBounds
#print axioms no_uniform_criticalRestartShellPayment_factorization_through_energyPaidFrozenSquare

end Audit

end Soma.Holonics.Millennium.NavierStokesRestartMatchedEndpointTrace
