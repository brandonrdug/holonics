import ElementaryHolonics.Mathematics.CopsonDeBruijnFiniteTail
import Mathlib.Analysis.Convex.StdSimplex

/-!
# The attained finite Copson--de Bruijn coefficient

For every nonempty finite length, the tail surface is continuous and strictly positive on the
compact nonnegative mass-one simplex.  Its attained minimum therefore defines the sharp finite
coefficient.  Homogeneity returns the inequality for every nonnegative finite section, while the
chosen minimizer proves optimality.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

open Set Finset
open scoped BigOperators NNReal Topology

/-- The nonempty finite simplex of length `N + 1`; the parameter is one below its length. -/
abbrev MassOneSection (N : ℕ) := stdSimplex ℝ≥0 (Fin (N + 1))

/-- Membership in the simplex is exactly the mass-one condition for nonnegative sections. -/
theorem MassOneSection.mass_eq_one {N : ℕ} (finite : MassOneSection N) :
    mass finite.1 = 1 := by
  exact finite.2.2

/-- The mass-one simplex has a canonical vertex. -/
def massOneVertex (N : ℕ) : MassOneSection N :=
  ⟨Pi.single (0 : Fin (N + 1)) 1, single_mem_stdSimplex ℝ≥0 0⟩

/-- Each finite suffix energy varies continuously with the section. -/
theorem continuous_tailEnergy {N : ℕ} (n : Fin N) :
    Continuous (fun finite : FiniteSection N ↦ tailEnergy finite n) := by
  unfold tailEnergy
  fun_prop

/-- Each finite suffix radius varies continuously with the section. -/
theorem continuous_tailRadius {N : ℕ} (n : Fin N) :
    Continuous (fun finite : FiniteSection N ↦ tailRadius finite n) := by
  unfold tailRadius
  exact NNReal.continuous_sqrt.comp (continuous_tailEnergy n)

/-- The complete finite tail surface is continuous. -/
theorem continuous_tailSurface (N : ℕ) :
    Continuous (tailSurface : FiniteSection N → ℝ≥0) := by
  unfold tailSurface
  apply continuous_finsetSum
  intro n _hn
  exact continuous_const.mul (continuous_tailRadius n)

/-- A positive-mass finite section has a strictly positive tail surface. -/
theorem tailSurface_pos_of_mass_pos {N : ℕ} {finite : FiniteSection N}
    (hmass : 0 < mass finite) : 0 < tailSurface finite := by
  have hsum : 0 < ∑ n, finite n := by simpa [mass] using hmass
  obtain ⟨n, _hn, hnpos⟩ :=
    (Finset.sum_pos_iff_of_nonneg (s := Finset.univ)
      (f := finite) (fun _ _ ↦ zero_le)).mp hsum
  have henergy : 0 < tailEnergy finite n := by
    unfold tailEnergy
    exact Finset.sum_pos' (fun _ _ ↦ zero_le)
      ⟨n, by simp, pow_pos hnpos 2⟩
  have hterm : 0 < startingIndexWeight n * tailRadius finite n := by
    apply mul_pos
    · unfold startingIndexWeight
      positivity
    · exact NNReal.sqrt_pos.2 henergy
  unfold tailSurface
  exact Finset.sum_pos' (fun _ _ ↦ zero_le) ⟨n, by simp, hterm⟩

/-- Every mass-one section has strictly positive tail surface. -/
theorem MassOneSection.tailSurface_pos {N : ℕ} (finite : MassOneSection N) :
    0 < tailSurface finite.1 :=
  tailSurface_pos_of_mass_pos (by
    rw [MassOneSection.mass_eq_one finite]
    exact zero_lt_one)

/-- The continuous tail surface attains a minimum on the compact mass-one simplex. -/
theorem exists_massOne_minimizer (N : ℕ) :
    ∃ finite : MassOneSection N, ∀ other : MassOneSection N,
      tailSurface finite.1 ≤ tailSurface other.1 := by
  have hcontinuous : Continuous (fun finite : MassOneSection N ↦ tailSurface finite.1) :=
    (continuous_tailSurface (N + 1)).comp continuous_subtype_val
  obtain ⟨finite, _hmem, hmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set (MassOneSection N))).exists_isMinOn
      ⟨massOneVertex N, Set.mem_univ _⟩ hcontinuous.continuousOn
  exact ⟨finite, fun other ↦ hmin (Set.mem_univ other)⟩

/-- One chosen minimizer of the finite mass-one tail surface. -/
def minimizingSection (N : ℕ) : MassOneSection N :=
  Classical.choose (exists_massOne_minimizer N)

/-- The attained minimum finite tail surface. -/
def minimumTailSurface (N : ℕ) : ℝ≥0 :=
  tailSurface (minimizingSection N).1

theorem minimumTailSurface_le (N : ℕ) (finite : MassOneSection N) :
    minimumTailSurface N ≤ tailSurface finite.1 :=
  Classical.choose_spec (exists_massOne_minimizer N) finite

theorem minimumTailSurface_pos (N : ℕ) : 0 < minimumTailSurface N :=
  MassOneSection.tailSurface_pos (minimizingSection N)

/--
The reciprocal of the attained finite mass-one minimum. Under conventional one-based mathematical
indexing, `finiteSharpCoefficient N` is `c_(N+1)`, not `c_N`.
-/
def finiteSharpCoefficient (N : ℕ) : ℝ≥0 :=
  (minimumTailSurface N)⁻¹

/-- The attained finite coefficient controls every section by homogeneity. -/
theorem mass_le_finiteSharpCoefficient_mul_tailSurface (N : ℕ)
    (finite : FiniteSection (N + 1)) :
    mass finite ≤ finiteSharpCoefficient N * tailSurface finite := by
  by_cases hmass : mass finite = 0
  · simp [hmass]
  · have hmasspos : 0 < mass finite := pos_iff_ne_zero.2 hmass
    let normalized : MassOneSection N :=
      ⟨(mass finite)⁻¹ • finite, fun _ ↦ zero_le, by
        rw [← mass, mass_smul]
        exact inv_mul_cancel₀ hmass⟩
    have hminimum : minimumTailSurface N ≤ tailSurface normalized.1 :=
      minimumTailSurface_le N normalized
    have hscaled : mass finite * minimumTailSurface N ≤ tailSurface finite := by
      calc
        mass finite * minimumTailSurface N ≤
            mass finite * tailSurface normalized.1 :=
          by simpa [mul_comm] using (mul_le_mul_left hminimum (mass finite))
        _ = tailSurface finite := by
          rw [show normalized.1 = (mass finite)⁻¹ • finite from rfl,
            tailSurface_smul]
          exact mul_inv_cancel_left₀ hmass _
    change mass finite ≤ (minimumTailSurface N)⁻¹ * tailSurface finite
    exact (le_inv_mul_iff₀ (minimumTailSurface_pos N)).2 (by
      simpa [mul_comm] using hscaled)

/-- The chosen minimizing section attains equality in the finite inequality. -/
theorem finiteSharpCoefficient_attained (N : ℕ) :
    mass (minimizingSection N).1 =
      finiteSharpCoefficient N * tailSurface (minimizingSection N).1 := by
  rw [MassOneSection.mass_eq_one (minimizingSection N)]
  change 1 = (minimumTailSurface N)⁻¹ * minimumTailSurface N
  exact (inv_mul_cancel₀ (minimumTailSurface_pos N).ne').symm

/-- No smaller coefficient controls every finite section of this length. -/
theorem finiteSharpCoefficient_le_of_controls (N : ℕ) (coefficient : ℝ≥0)
    (controls : ∀ finite : FiniteSection (N + 1),
      mass finite ≤ coefficient * tailSurface finite) :
    finiteSharpCoefficient N ≤ coefficient := by
  have hatMinimizer := controls (minimizingSection N).1
  rw [MassOneSection.mass_eq_one (minimizingSection N)] at hatMinimizer
  change (minimumTailSurface N)⁻¹ ≤ coefficient
  exact (inv_le_iff_one_le_mul₀ (minimumTailSurface_pos N)).2 (by
    simpa [minimumTailSurface, mul_comm] using hatMinimizer)

end Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

section Audit
open Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail
#print axioms tailSurface_pos_of_mass_pos
#print axioms continuous_tailSurface
#print axioms exists_massOne_minimizer
#print axioms minimumTailSurface_pos
#print axioms mass_le_finiteSharpCoefficient_mul_tailSurface
#print axioms finiteSharpCoefficient_attained
#print axioms finiteSharpCoefficient_le_of_controls
end Audit
