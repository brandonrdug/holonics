import ElementaryHolonics.Mathematics.CopsonDeBruijnFiniteSharp
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# The monotone finite sections and infinite Copson--de Bruijn boundary

Adjacent finite sections are related by a final zero coordinate.  This preserves every old
suffix, mass, and tail surface, so the attained finite sharp coefficients form a monotone family.
The infinite receiver is stated in `ℝ≥0∞`; divergent nonnegative sums therefore remain `⊤` rather
than being totalized to zero.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

open Finset
open scoped BigOperators NNReal ENNReal

/-- Append one genuinely silent coordinate to a nonempty finite section. -/
def zeroExtend {N : ℕ} (finite : FiniteSection (N + 1)) : FiniteSection (N + 2) :=
  Fin.snoc finite 0

@[simp] theorem zeroExtend_castSucc {N : ℕ} (finite : FiniteSection (N + 1))
    (n : Fin (N + 1)) :
    zeroExtend finite n.castSucc = finite n := by
  simp [zeroExtend]

@[simp] theorem zeroExtend_last {N : ℕ} (finite : FiniteSection (N + 1)) :
    zeroExtend finite (Fin.last (N + 1)) = 0 := by
  simp [zeroExtend]

/-- Appending a silent coordinate preserves every suffix which already existed. -/
theorem tailEnergy_zeroExtend_castSucc {N : ℕ} (finite : FiniteSection (N + 1))
    (n : Fin (N + 1)) :
    tailEnergy (zeroExtend finite) n.castSucc = tailEnergy finite n := by
  classical
  unfold tailEnergy
  rw [show (Finset.Ici n.castSucc : Finset (Fin (N + 2))) =
      Finset.univ.filter (fun k ↦ n.castSucc ≤ k) by ext; simp,
    show (Finset.Ici n : Finset (Fin (N + 1))) =
      Finset.univ.filter (fun k ↦ n ≤ k) by ext; simp,
    Finset.sum_filter, Finset.sum_filter]
  rw [Fin.sum_univ_castSucc]
  simp [zeroExtend]

/-- The newly appended suffix has zero energy. -/
@[simp] theorem tailEnergy_zeroExtend_last {N : ℕ} (finite : FiniteSection (N + 1)) :
    tailEnergy (zeroExtend finite) (Fin.last (N + 1)) = 0 := by
  simp [tailEnergy, zeroExtend]

/-- Appending a silent coordinate preserves every old tail radius. -/
theorem tailRadius_zeroExtend_castSucc {N : ℕ} (finite : FiniteSection (N + 1))
    (n : Fin (N + 1)) :
    tailRadius (zeroExtend finite) n.castSucc = tailRadius finite n := by
  simp [tailRadius, tailEnergy_zeroExtend_castSucc]

/-- The newly appended suffix has zero radius. -/
@[simp] theorem tailRadius_zeroExtend_last {N : ℕ} (finite : FiniteSection (N + 1)) :
    tailRadius (zeroExtend finite) (Fin.last (N + 1)) = 0 := by
  simp [tailRadius]

/-- Appending a silent coordinate preserves finite mass. -/
theorem mass_zeroExtend {N : ℕ} (finite : FiniteSection (N + 1)) :
    mass (zeroExtend finite) = mass finite := by
  simp [mass, zeroExtend, Fin.sum_univ_castSucc]

/-- Appending a silent coordinate preserves the complete finite tail surface. -/
theorem tailSurface_zeroExtend {N : ℕ} (finite : FiniteSection (N + 1)) :
    tailSurface (zeroExtend finite) = tailSurface finite := by
  rw [tailSurface, tailSurface, Fin.sum_univ_castSucc]
  simp [tailRadius_zeroExtend_castSucc, startingIndexWeight]

/-- The sharp finite coefficients are monotone under silent final extension. -/
theorem finiteSharpCoefficient_mono (N : ℕ) :
    finiteSharpCoefficient N ≤ finiteSharpCoefficient (N + 1) := by
  apply finiteSharpCoefficient_le_of_controls
  intro finite
  simpa [mass_zeroExtend, tailSurface_zeroExtend] using
    mass_le_finiteSharpCoefficient_mul_tailSurface (N + 1) (zeroExtend finite)

/-! ## The extended-nonnegative infinite receiver -/

/-- The first `N + 1` entries of an infinite nonnegative section. -/
def finitePrefix (a : ℕ → ℝ≥0) (N : ℕ) : FiniteSection (N + 1) :=
  fun n ↦ a n.val

/-- Infinite additive mass, valued in `ℝ≥0∞` so divergence remains visible. -/
def infiniteMass (a : ℕ → ℝ≥0) : ℝ≥0∞ :=
  ∑' n, (a n : ℝ≥0∞)

/-- Infinite suffix energy, expressed directly as a conditional nonnegative `tsum`. -/
def infiniteTailEnergy (a : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  ∑' k, if n ≤ k then (a k : ℝ≥0∞) ^ 2 else 0

/-- The extended-nonnegative square-root radius of an infinite suffix energy. -/
def infiniteTailRadius (a : ℕ → ℝ≥0) (n : ℕ) : ℝ≥0∞ :=
  infiniteTailEnergy a n ^ (1 / (2 : ℝ))

/-- The inverse square root of the one-based infinite starting index. -/
def infiniteStartingIndexWeight (n : ℕ) : ℝ≥0∞ :=
  (((n + 1 : ℕ) : ℝ≥0∞) ^ (1 / (2 : ℝ)))⁻¹

/-- The direct extended-nonnegative infinite Copson--de Bruijn tail surface. -/
def infiniteTailSurface (a : ℕ → ℝ≥0) : ℝ≥0∞ :=
  ∑' n, infiniteStartingIndexWeight n * infiniteTailRadius a n

/-- The supremum of the attained finite sharp coefficients. -/
def infiniteSharpBoundary : ℝ≥0∞ :=
  ⨆ N : ℕ, (finiteSharpCoefficient N : ℝ≥0∞)

/-- Coercing the mass of a finite prefix gives its extended-nonnegative partial sum. -/
theorem coe_mass_finitePrefix (a : ℕ → ℝ≥0) (N : ℕ) :
    (mass (finitePrefix a N) : ℝ≥0∞) =
      ∑ n ∈ Finset.range (N + 1), (a n : ℝ≥0∞) := by
  rw [mass, ENNReal.ofNNReal_finsetSum]
  simpa [finitePrefix] using
    (Fin.sum_univ_eq_sum_range (fun n ↦ (a n : ℝ≥0∞)) (N + 1))

/-- A coerced finite-prefix suffix energy is its corresponding conditional partial sum. -/
theorem coe_tailEnergy_finitePrefix (a : ℕ → ℝ≥0) (N : ℕ) (n : Fin (N + 1)) :
    (tailEnergy (finitePrefix a N) n : ℝ≥0∞) =
      ∑ k ∈ Finset.range (N + 1),
        if n.val ≤ k then (a k : ℝ≥0∞) ^ 2 else 0 := by
  classical
  unfold tailEnergy
  rw [show (Finset.Ici n : Finset (Fin (N + 1))) =
      Finset.univ.filter (fun k ↦ n ≤ k) by ext; simp,
    Finset.sum_filter, ENNReal.ofNNReal_finsetSum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro k _hk
  by_cases hnk : n ≤ k
  · simp [hnk, finitePrefix, ENNReal.coe_pow]
  · have hval : ¬n.val ≤ k.val := by simpa using hnk
    simp [hnk, hval]

/-- Every finite-prefix suffix energy is bounded by the direct infinite suffix energy. -/
theorem coe_tailEnergy_finitePrefix_le (a : ℕ → ℝ≥0) (N : ℕ) (n : Fin (N + 1)) :
    (tailEnergy (finitePrefix a N) n : ℝ≥0∞) ≤ infiniteTailEnergy a n.val := by
  rw [coe_tailEnergy_finitePrefix, infiniteTailEnergy]
  exact ENNReal.sum_le_tsum (Finset.range (N + 1))

/-- Every finite-prefix suffix radius is bounded by the direct infinite suffix radius. -/
theorem coe_tailRadius_finitePrefix_le (a : ℕ → ℝ≥0) (N : ℕ) (n : Fin (N + 1)) :
    (tailRadius (finitePrefix a N) n : ℝ≥0∞) ≤ infiniteTailRadius a n.val := by
  rw [tailRadius, NNReal.sqrt_eq_rpow, infiniteTailRadius,
    ENNReal.coe_rpow_of_nonneg _ (by positivity)]
  exact ENNReal.rpow_le_rpow (coe_tailEnergy_finitePrefix_le a N n) (by positivity)

/-- Coercion preserves the one-based starting-index weight. -/
theorem coe_startingIndexWeight (N : ℕ) (n : Fin N) :
    (startingIndexWeight n : ℝ≥0∞) = infiniteStartingIndexWeight n.val := by
  rw [startingIndexWeight, NNReal.sqrt_eq_rpow, infiniteStartingIndexWeight,
    ENNReal.coe_inv (by positivity), ENNReal.coe_rpow_of_nonneg _ (by positivity)]
  simp

/-- The surface of every finite prefix is bounded by the direct infinite surface. -/
theorem coe_tailSurface_finitePrefix_le (a : ℕ → ℝ≥0) (N : ℕ) :
    (tailSurface (finitePrefix a N) : ℝ≥0∞) ≤ infiniteTailSurface a := by
  rw [tailSurface, ENNReal.ofNNReal_finsetSum]
  calc
    (∑ n : Fin (N + 1),
        ((startingIndexWeight n * tailRadius (finitePrefix a N) n : ℝ≥0) : ℝ≥0∞))
        ≤ ∑ n ∈ Finset.range (N + 1),
            infiniteStartingIndexWeight n * infiniteTailRadius a n := by
          rw [← Fin.sum_univ_eq_sum_range]
          exact Finset.sum_le_sum fun n _ ↦ by
            rw [ENNReal.coe_mul, coe_startingIndexWeight]
            exact mul_le_mul_of_nonneg_left (coe_tailRadius_finitePrefix_le a N n) zero_le
    _ ≤ infiniteTailSurface a := by
      rw [infiniteTailSurface]
      exact ENNReal.sum_le_tsum (Finset.range (N + 1))

/-- Every attained finite coefficient is bounded by the infinite supremum. -/
theorem coe_finiteSharpCoefficient_le_infiniteSharpBoundary (N : ℕ) :
    (finiteSharpCoefficient N : ℝ≥0∞) ≤ infiniteSharpBoundary := by
  exact le_iSup (fun k : ℕ ↦ (finiteSharpCoefficient k : ℝ≥0∞)) N

/-- The infinite boundary controls each finite mass prefix against the full infinite surface. -/
theorem finitePrefix_mass_le_infiniteSharpBoundary_mul_surface (a : ℕ → ℝ≥0) (N : ℕ) :
    (∑ n ∈ Finset.range (N + 1), (a n : ℝ≥0∞)) ≤
      infiniteSharpBoundary * infiniteTailSurface a := by
  have hfinite := mass_le_finiteSharpCoefficient_mul_tailSurface N (finitePrefix a N)
  have hfiniteENN : (mass (finitePrefix a N) : ℝ≥0∞) ≤
      (finiteSharpCoefficient N : ℝ≥0∞) *
        (tailSurface (finitePrefix a N) : ℝ≥0∞) := by
    exact ENNReal.coe_le_coe.2 (by simpa using hfinite)
  rw [← coe_mass_finitePrefix]
  exact hfiniteENN.trans
    (mul_le_mul (coe_finiteSharpCoefficient_le_infiniteSharpBoundary N)
      (coe_tailSurface_finitePrefix_le a N) zero_le zero_le)

/-- The supremum of the finite sharp coefficients controls the direct infinite functional. -/
theorem infiniteMass_le_infiniteSharpBoundary_mul_tailSurface (a : ℕ → ℝ≥0) :
    infiniteMass a ≤ infiniteSharpBoundary * infiniteTailSurface a := by
  rw [infiniteMass, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n ↦ ?_
  cases n with
  | zero => simp
  | succ N =>
      simpa [Nat.succ_eq_add_one] using
        finitePrefix_mass_le_infiniteSharpBoundary_mul_surface a N

/-! ## Finite-support reflection and optimality -/

/-- Regard a finite section as an infinite section by adjoining only zero coordinates. -/
def finiteSupportExtension {N : ℕ} (finite : FiniteSection (N + 1)) : ℕ → ℝ≥0 :=
  fun n ↦ if h : n < N + 1 then finite ⟨n, h⟩ else 0

@[simp] theorem finiteSupportExtension_apply_of_lt {N : ℕ}
    (finite : FiniteSection (N + 1)) {n : ℕ} (hn : n < N + 1) :
    finiteSupportExtension finite n = finite ⟨n, hn⟩ := by
  simp [finiteSupportExtension, hn]

@[simp] theorem finiteSupportExtension_apply_of_le {N : ℕ}
    (finite : FiniteSection (N + 1)) {n : ℕ} (hn : N + 1 ≤ n) :
    finiteSupportExtension finite n = 0 := by
  simp [finiteSupportExtension, Nat.not_lt.mpr hn]

/-- Truncating a finite-support extension to its original length returns the supplied section. -/
@[simp] theorem finitePrefix_finiteSupportExtension {N : ℕ}
    (finite : FiniteSection (N + 1)) :
    finitePrefix (finiteSupportExtension finite) N = finite := by
  funext n
  simp [finitePrefix, finiteSupportExtension, n.isLt]

/-- The infinite mass of a finite-support extension is exactly the coerced finite mass. -/
theorem infiniteMass_finiteSupportExtension {N : ℕ}
    (finite : FiniteSection (N + 1)) :
    infiniteMass (finiteSupportExtension finite) = (mass finite : ℝ≥0∞) := by
  rw [infiniteMass, tsum_eq_sum (s := Finset.range (N + 1))]
  · rw [mass, ENNReal.ofNNReal_finsetSum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n _hn
    simp [finiteSupportExtension, n.isLt]
  · intro n hn
    have hnle : N + 1 ≤ n := by
      exact Nat.not_lt.mp (fun hnlt ↦ hn (Finset.mem_range.mpr hnlt))
    simp [finiteSupportExtension_apply_of_le finite hnle]

/-- Each old suffix energy is recovered exactly by the finite-support extension. -/
theorem infiniteTailEnergy_finiteSupportExtension {N : ℕ}
    (finite : FiniteSection (N + 1)) (n : Fin (N + 1)) :
    infiniteTailEnergy (finiteSupportExtension finite) n.val =
      (tailEnergy finite n : ℝ≥0∞) := by
  rw [infiniteTailEnergy, tsum_eq_sum (s := Finset.range (N + 1))]
  · have hprefix := coe_tailEnergy_finitePrefix (finiteSupportExtension finite) N n
    rw [finitePrefix_finiteSupportExtension] at hprefix
    exact hprefix.symm
  · intro k hk
    have hkle : N + 1 ≤ k := by
      exact Nat.not_lt.mp (fun hklt ↦ hk (Finset.mem_range.mpr hklt))
    by_cases hnk : n.val ≤ k
    · simp [hnk, finiteSupportExtension_apply_of_le finite hkle]
    · simp [hnk]

/-- A suffix beginning beyond the finite support has zero infinite energy. -/
theorem infiniteTailEnergy_finiteSupportExtension_eq_zero_of_le {N : ℕ}
    (finite : FiniteSection (N + 1)) {n : ℕ} (hn : N + 1 ≤ n) :
    infiniteTailEnergy (finiteSupportExtension finite) n = 0 := by
  unfold infiniteTailEnergy
  rw [ENNReal.tsum_eq_zero]
  intro k
  by_cases hnk : n ≤ k
  · have hkle : N + 1 ≤ k := hn.trans hnk
    simp [hnk, finiteSupportExtension_apply_of_le finite hkle]
  · simp [hnk]

/-- Each old suffix radius is recovered exactly by the finite-support extension. -/
theorem infiniteTailRadius_finiteSupportExtension {N : ℕ}
    (finite : FiniteSection (N + 1)) (n : Fin (N + 1)) :
    infiniteTailRadius (finiteSupportExtension finite) n.val =
      (tailRadius finite n : ℝ≥0∞) := by
  rw [infiniteTailRadius, infiniteTailEnergy_finiteSupportExtension, tailRadius,
    NNReal.sqrt_eq_rpow, ENNReal.coe_rpow_of_nonneg _ (by positivity)]

/-- Every infinite radius beginning beyond the finite support vanishes. -/
theorem infiniteTailRadius_finiteSupportExtension_eq_zero_of_le {N : ℕ}
    (finite : FiniteSection (N + 1)) {n : ℕ} (hn : N + 1 ≤ n) :
    infiniteTailRadius (finiteSupportExtension finite) n = 0 := by
  rw [infiniteTailRadius,
    infiniteTailEnergy_finiteSupportExtension_eq_zero_of_le finite hn]
  simp

/-- The direct infinite surface of a finite-support extension is exactly the coerced finite surface. -/
theorem infiniteTailSurface_finiteSupportExtension {N : ℕ}
    (finite : FiniteSection (N + 1)) :
    infiniteTailSurface (finiteSupportExtension finite) =
      (tailSurface finite : ℝ≥0∞) := by
  rw [infiniteTailSurface, tsum_eq_sum (s := Finset.range (N + 1))]
  · rw [tailSurface, ENNReal.ofNNReal_finsetSum, ← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n _hn
    rw [ENNReal.coe_mul, coe_startingIndexWeight,
      infiniteTailRadius_finiteSupportExtension]
  · intro n hn
    have hnle : N + 1 ≤ n := by
      exact Nat.not_lt.mp (fun hnlt ↦ hn (Finset.mem_range.mpr hnlt))
    rw [infiniteTailRadius_finiteSupportExtension_eq_zero_of_le finite hnle, mul_zero]

/-- Any coefficient controlling every infinite section bounds each attained finite coefficient. -/
theorem coe_finiteSharpCoefficient_le_of_controls_infinite (coefficient : ℝ≥0∞)
    (controls : ∀ a : ℕ → ℝ≥0,
      infiniteMass a ≤ coefficient * infiniteTailSurface a) (N : ℕ) :
    (finiteSharpCoefficient N : ℝ≥0∞) ≤ coefficient := by
  let finite := (minimizingSection N).1
  have hcontrol := controls (finiteSupportExtension finite)
  rw [infiniteMass_finiteSupportExtension, infiniteTailSurface_finiteSupportExtension] at hcontrol
  have hone : (1 : ℝ≥0∞) ≤ coefficient * (minimumTailSurface N : ℝ≥0∞) := by
    change (mass (minimizingSection N).1 : ℝ≥0∞) ≤
      coefficient * (tailSurface (minimizingSection N).1 : ℝ≥0∞) at hcontrol
    rw [MassOneSection.mass_eq_one (minimizingSection N)] at hcontrol
    exact hcontrol
  have hminimum : minimumTailSurface N ≠ 0 := (minimumTailSurface_pos N).ne'
  change ((minimumTailSurface N)⁻¹ : ℝ≥0) ≤ coefficient
  rw [ENNReal.coe_inv hminimum]
  calc
    ((minimumTailSurface N : ℝ≥0∞))⁻¹ =
        ((minimumTailSurface N : ℝ≥0∞))⁻¹ * 1 := (mul_one _).symm
    _ ≤ ((minimumTailSurface N : ℝ≥0∞))⁻¹ *
          (coefficient * (minimumTailSurface N : ℝ≥0∞)) :=
      mul_le_mul_of_nonneg_left hone zero_le
    _ = coefficient := by
      rw [mul_comm coefficient, ← mul_assoc,
        ENNReal.inv_mul_cancel (ENNReal.coe_ne_zero.2 hminimum) ENNReal.coe_ne_top, one_mul]

/-- Every universal infinite controlling coefficient bounds the supremal infinite boundary. -/
theorem infiniteSharpBoundary_le_of_controls (coefficient : ℝ≥0∞)
    (controls : ∀ a : ℕ → ℝ≥0,
      infiniteMass a ≤ coefficient * infiniteTailSurface a) :
    infiniteSharpBoundary ≤ coefficient := by
  rw [infiniteSharpBoundary]
  exact iSup_le fun N ↦ coe_finiteSharpCoefficient_le_of_controls_infinite coefficient controls N

/--
The supremum of finite sharp coefficients is exactly the least coefficient controlling every
infinite nonnegative section.
-/
theorem infiniteSharpBoundary_le_coefficient_iff_controls (coefficient : ℝ≥0∞) :
    infiniteSharpBoundary ≤ coefficient ↔
      ∀ a : ℕ → ℝ≥0, infiniteMass a ≤ coefficient * infiniteTailSurface a := by
  constructor
  · intro hboundary a
    exact (infiniteMass_le_infiniteSharpBoundary_mul_tailSurface a).trans
      (mul_le_mul_of_nonneg_right hboundary zero_le)
  · exact infiniteSharpBoundary_le_of_controls coefficient

end Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

section Audit
open Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail
#print axioms tailEnergy_zeroExtend_castSucc
#print axioms mass_zeroExtend
#print axioms tailSurface_zeroExtend
#print axioms finiteSharpCoefficient_mono
#print axioms infiniteMass_le_infiniteSharpBoundary_mul_tailSurface
#print axioms infiniteMass_finiteSupportExtension
#print axioms infiniteTailSurface_finiteSupportExtension
#print axioms infiniteSharpBoundary_le_of_controls
#print axioms infiniteSharpBoundary_le_coefficient_iff_controls
end Audit
