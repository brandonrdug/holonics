import ElementaryHolonics.Foundation.ReceiverHistoryCompression
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic

/-!
# Independent generator modes at a declared future receiver

The linear mode chart is an additional mathematical hypothesis. Alternation excludes a repeated
or dependent direction as a new independent mode; it does not forbid multiple occurrences,
nonunit amplitudes, or repeated application of a generator. Dynamic quotient exactness carries
an eliminated source direction through the admitted future family.
-/

namespace Soma.Holonics.Foundation.GeneratorModeQuotient

open scoped BigOperators
open Soma.Holonics.Millennium.Chronology

section IndependentModes

variable {Mode V Q : Type*} [Fintype Mode] [DecidableEq Mode]
  [AddCommGroup V] [Module ℝ V] [NormedAddCommGroup Q] [InnerProductSpace ℝ Q]

/-- Gram degeneracy is exactly dependence of the modes at this complete declared receiver. -/
theorem receiver_gram_zero_iff (encode : V →ₗ[ℝ] Q) (modes : Mode → V) :
    (Matrix.gram ℝ (fun i => encode (modes i))).det = 0 ↔
      ¬LinearIndependent ℝ (fun i => encode (modes i)) := by
  simpa only [not_not] using not_congr
    (Matrix.det_gram_ne_zero_iff_linearIndependent
      (𝕜 := ℝ) (v := fun i => encode (modes i)))

/-- Any alternating mode-volume receiver annihilates that dependent family. -/
theorem dependent_modes_excluded {Output : Type*} [AddCommGroup Output] [Module ℝ Output]
    (encode : V →ₗ[ℝ] Q) (modes : Mode → V)
    (volume : Q [⋀^Mode]→ₗ[ℝ] Output)
    (dependent : ¬LinearIndependent ℝ (fun i => encode (modes i))) :
    volume (fun i => encode (modes i)) = 0 :=
  volume.map_linearDependent _ dependent

theorem independent_mode_count_le [FiniteDimensional ℝ Q]
    (encode : V →ₗ[ℝ] Q) (modes : Mode → V)
    (independent : LinearIndependent ℝ (fun i => encode (modes i))) :
    Fintype.card Mode ≤ Module.finrank ℝ Q :=
  independent.fintype_card_le_finrank

end IndependentModes

section Elimination

variable {Mode V Q Generator : Type*} [Fintype Mode]
  [AddCommGroup V] [Module ℝ V] [AddCommGroup Q] [Module ℝ Q]

/-- Eliminating a dependent mode changes its coefficient representation, not its amplitude. -/
theorem eliminate_redundant_mode (encode : V →ₗ[ℝ] Q)
    (modes : Mode → V) (extra : V) (relation coefficients : Mode → ℝ) (amplitude : ℝ)
    (dependent : encode extra = ∑ i, relation i • encode (modes i)) :
    encode ((∑ i, coefficients i • modes i) + amplitude • extra) =
      encode (∑ i, (coefficients i + amplitude * relation i) • modes i) := by
  simp only [map_add, map_sum, map_smul, dependent, Finset.smul_sum,
    add_smul, mul_smul, Finset.sum_add_distrib]

/-- The same elimination is exact after every admitted generator word when encode descends. -/
theorem eliminated_mode_every_future (encode : V →ₗ[ℝ] Q)
    (fine : Generator → V → V) (coarse : Generator → Q → Q)
    (commutes : ∀ g x, encode (fine g x) = coarse g (encode x))
    (modes : Mode → V) (extra : V) (relation coefficients : Mode → ℝ) (amplitude : ℝ)
    (dependent : encode extra = ∑ i, relation i • encode (modes i)) (word : List Generator) :
    encode (transportWord fine word ((∑ i, coefficients i • modes i) + amplitude • extra)) =
      encode (transportWord fine word (∑ i, (coefficients i + amplitude * relation i) • modes i)) := by
  rw [generatorEquivarianceExtendsToEveryTransportWord fine coarse encode commutes,
    generatorEquivarianceExtendsToEveryTransportWord fine coarse encode commutes,
    eliminate_redundant_mode encode modes extra relation coefficients amplitude dependent]

end Elimination

/-- Exclusion of redundant representation does not make a generator's iteration idempotent. -/
theorem repeated_generator_can_change_amplitude :
    let double : ℚ → ℚ := fun x => 2 * x
    double (double 1) ≠ double 1 := by norm_num

#print axioms receiver_gram_zero_iff
#print axioms dependent_modes_excluded
#print axioms independent_mode_count_le
#print axioms eliminated_mode_every_future

end Soma.Holonics.Foundation.GeneratorModeQuotient
