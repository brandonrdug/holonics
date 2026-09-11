import Mathlib

/-!
# Generator admission and observation scope

Finite observations constrain a family of possible generators. They do not identify a unique
continuation in an unrestricted family. A declared constitutive family can supply the missing
constraint, and a source excitation can reveal previously invisible generator differences.
This is exterior verification, not an inference-time proof gate.
-/
namespace Soma.Holonics.Computation.GeneratorObservationScope

abbrev Generator := ℕ → ℚ

def compatible (population : Set Generator) (observed : Finset ℕ) (face : Generator) : Set Generator :=
  { g | g ∈ population ∧ ∀ n ∈ observed, g n = face n }

theorem more_observations_restrict (population : Set Generator) (face : Generator)
    {old newer : Finset ℕ} (included : old ⊆ newer) :
    compatible population newer face ⊆ compatible population old face := by
  intro g hg
  exact ⟨hg.1, fun n hn => hg.2 n (included hn)⟩

def geometric (n : ℕ) : ℚ := 2 ^ n

def finiteAlternative (count : ℕ) (parameter : ℚ) (n : ℕ) : ℚ :=
  geometric n + parameter * ∏ i ∈ Finset.range count, ((n : ℚ) - i)

theorem alternatives_agree_on_observed_prefix (count : ℕ) (parameter : ℚ)
    {n : ℕ} (before : n < count) : finiteAlternative count parameter n = geometric n := by
  have zero : (∏ i ∈ Finset.range count, ((n : ℚ) - i)) = 0 := by
    apply Finset.prod_eq_zero (Finset.mem_range.mpr before)
    simp
  simp [finiteAlternative, zero]

theorem alternatives_separate_next (count : ℕ) {left right : ℚ} (different : left ≠ right) :
    finiteAlternative count left count ≠ finiteAlternative count right count := by
  have nonzero : (∏ i ∈ Finset.range count, ((count : ℚ) - i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply sub_ne_zero.mpr
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_range.mp hi))
  intro equal
  unfold finiteAlternative at equal
  have product_zero : (left-right) * (∏ i ∈ Finset.range count, ((count : ℚ)-i)) = 0 := by
    nlinarith [equal]
  exact (mul_ne_zero (sub_ne_zero.mpr different) nonzero) product_zero

def quadratic (n : ℕ) : ℚ := 1 + n + (n : ℚ) * (n-1) / 2

theorem exponential_and_polynomial_same_three_faces :
    (∀ n : Fin 3, geometric n = quadratic n) ∧ geometric 3 ≠ quadratic 3 := by
  constructor
  · intro n; fin_cases n <;> norm_num [geometric, quadratic]
  · norm_num [geometric, quadratic]

def additiveDoubling : ℕ → ℚ
  | 0 => 1
  | n+1 => additiveDoubling n + additiveDoubling n

theorem addition_can_realize_exponential_growth (n : ℕ) : additiveDoubling n = geometric n := by
  induction n with
  | zero => norm_num [additiveDoubling, geometric]
  | succ n ih => simp [additiveDoubling, ih, geometric, pow_succ]; ring

/-- An actual constitutive constraint makes the next observation identify the multiplier. -/
theorem fixed_ratio_identified {amplitude left right : ℚ} (excited : amplitude ≠ 0)
    (same_next : amplitude * left = amplitude * right) :
    left = right ∧ ∀ n : ℕ, amplitude * left^n = amplitude * right^n := by
  have same : left = right := mul_left_cancel₀ excited same_next
  exact ⟨same, fun n => by rw [same]⟩

/-- At the unexcited face every multiplier is presently invisible. -/
theorem zero_source_hides_ratio (left right : ℚ) (n : ℕ) :
    (0 : ℚ) * left^n = (0 : ℚ) * right^n := by simp

/-- Any nonzero excitation separates distinct multipliers at the next receiver. -/
theorem nonzero_excitation_separates {amplitude left right : ℚ}
    (excited : amplitude ≠ 0) (different : left ≠ right) :
    amplitude * left ≠ amplitude * right := by
  intro same
  exact different (fixed_ratio_identified excited same).1

/-- Exact receiver separation can be activated by an arbitrarily small rational excitation.
A finite measurement tolerance is an additional receiver hypothesis. -/
theorem arbitrarily_small_excitation_separates {left right : ℚ} (different : left ≠ right)
    (bound : ℚ) (positive : 0 < bound) :
    ∃ amplitude : ℚ, 0 < amplitude ∧ amplitude < bound ∧
      amplitude * left ≠ amplitude * right := by
  have half_pos : 0 < bound / 2 := by linarith
  exact ⟨bound / 2, half_pos, by linarith,
    nonzero_excitation_separates (ne_of_gt half_pos) different⟩

end Soma.Holonics.Computation.GeneratorObservationScope
