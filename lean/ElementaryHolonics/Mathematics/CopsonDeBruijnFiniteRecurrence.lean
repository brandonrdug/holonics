import ElementaryHolonics.Mathematics.CopsonDeBruijnInfiniteBoundary
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The finite Copson--de Bruijn Euler and recurrence passage

The finite sharp coefficient is already defined as the reciprocal of the attained minimum of the
tail surface on the nonnegative mass-one simplex.  This file opens that variational face in a real
ambient chart.  It proves that the chosen minimizer is interior, derives its Euler marginal
equations, and reads the resulting adjacent-tail balance as de Bruijn's finite recurrence.

The square root is differentiated only where the complete suffix energy is strictly positive.
The one newly appended zero suffix used in the interiority argument is handled as a one-sided
`sqrt (t ^ 2) = t` occurrence, never by differentiating `sqrt` at zero.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

open Set Finset Filter Topology
open scoped BigOperators NNReal

/-! ## A real ambient chart for the finite receiver -/

/-- The real ambient chart containing the nonnegative finite sections. -/
abbrev RealFiniteSection (N : ℕ) := Fin N → ℝ

/-- Coerce a nonnegative finite section into its real ambient chart. -/
def realSection {N : ℕ} (finite : FiniteSection N) : RealFiniteSection N :=
  fun i ↦ finite i

/-- Real suffix square energy. -/
def realTailEnergy {N : ℕ} (finite : RealFiniteSection N) (n : Fin N) : ℝ :=
  ∑ k ∈ Finset.Ici n, finite k ^ 2

/-- Real suffix radius. -/
def realTailRadius {N : ℕ} (finite : RealFiniteSection N) (n : Fin N) : ℝ :=
  Real.sqrt (realTailEnergy finite n)

/-- Real one-based inverse-square-root weight. -/
def realStartingIndexWeight {N : ℕ} (n : Fin N) : ℝ :=
  (Real.sqrt (n.val + 1))⁻¹

theorem realStartingIndexWeight_pos {N : ℕ} (n : Fin N) :
    0 < realStartingIndexWeight n := by
  unfold realStartingIndexWeight
  positivity

/-- The real ambient tail surface. -/
def realTailSurface {N : ℕ} (finite : RealFiniteSection N) : ℝ :=
  ∑ n, realStartingIndexWeight n * realTailRadius finite n

@[simp] theorem realTailEnergy_realSection {N : ℕ}
    (finite : FiniteSection N) (n : Fin N) :
    realTailEnergy (realSection finite) n = tailEnergy finite n := by
  simp [realTailEnergy, realSection, tailEnergy]

@[simp] theorem realTailRadius_realSection {N : ℕ}
    (finite : FiniteSection N) (n : Fin N) :
    realTailRadius (realSection finite) n = tailRadius finite n := by
  simp [realTailRadius, tailRadius]

@[simp] theorem realStartingIndexWeight_eq {N : ℕ} (n : Fin N) :
    realStartingIndexWeight n = startingIndexWeight n := by
  simp [realStartingIndexWeight, startingIndexWeight]

@[simp] theorem realTailSurface_realSection {N : ℕ} (finite : FiniteSection N) :
    realTailSurface (realSection finite) = tailSurface finite := by
  simp [realTailSurface, tailSurface]

/-- A positive final coordinate makes every suffix energy strictly positive. -/
theorem realTailEnergy_pos_of_last_pos {N : ℕ} (finite : FiniteSection (N + 1))
    (hlast : 0 < finite (Fin.last N)) (n : Fin (N + 1)) :
    0 < realTailEnergy (realSection finite) n := by
  rw [realTailEnergy_realSection]
  exact_mod_cast (show 0 < tailEnergy finite n by
    unfold tailEnergy
    apply Finset.sum_pos'
    · intro _ _
      positivity
    · refine ⟨Fin.last N, ?_, pow_pos hlast 2⟩
      exact Finset.mem_Ici.mpr (Fin.le_last n))

/-- The affine real line through a section in direction `direction`. -/
def sectionLine {N : ℕ} (finite direction : RealFiniteSection N) (t : ℝ) :
    RealFiniteSection N :=
  fun k ↦ finite k + t * direction k

@[simp] theorem sectionLine_zero {N : ℕ}
    (finite direction : RealFiniteSection N) :
    sectionLine finite direction 0 = finite := by
  funext k
  simp [sectionLine]

/-- The derivative of one suffix energy along an affine section line. -/
theorem hasDerivAt_realTailEnergy_sectionLine {N : ℕ}
    (finite direction : RealFiniteSection N) (n : Fin N) :
    HasDerivAt (fun t ↦ realTailEnergy (sectionLine finite direction t) n)
      (2 * ∑ k ∈ Finset.Ici n, finite k * direction k) 0 := by
  unfold realTailEnergy sectionLine
  have hterm : ∀ k ∈ Finset.Ici n,
      HasDerivAt (fun t : ℝ ↦ (finite k + t * direction k) ^ 2)
        (2 * (finite k * direction k)) 0 := by
    intro k _hk
    have hline : HasDerivAt (fun t : ℝ ↦ finite k + t * direction k)
        (direction k) 0 := by
      simpa using! ((hasDerivAt_id (0 : ℝ)).mul_const (direction k)).const_add (finite k)
    simpa only [pow_two] using! (hline.mul hline).congr_deriv (by ring)
  have hsum := HasDerivAt.fun_sum (u := Finset.Ici n) hterm
  simpa [Finset.mul_sum, mul_assoc] using hsum

/-- The derivative of one strictly positive suffix radius along a section line. -/
theorem hasDerivAt_realTailRadius_sectionLine {N : ℕ}
    (finite direction : RealFiniteSection N) (n : Fin N)
    (henergy : 0 < realTailEnergy finite n) :
    HasDerivAt (fun t ↦ realTailRadius (sectionLine finite direction t) n)
      ((∑ k ∈ Finset.Ici n, finite k * direction k) /
        realTailRadius finite n) 0 := by
  have hinner := hasDerivAt_realTailEnergy_sectionLine finite direction n
  have hsqrt := (Real.hasDerivAt_sqrt (by
    simpa using henergy.ne')).comp 0 hinner
  have hzero : realTailEnergy (sectionLine finite direction 0) n =
      realTailEnergy finite n := by rw [sectionLine_zero]
  rw [hzero] at hsqrt
  have hderiv : 1 / (2 * Real.sqrt (realTailEnergy finite n)) *
      (2 * ∑ k ∈ Finset.Ici n, finite k * direction k) =
        (∑ k ∈ Finset.Ici n, finite k * direction k) /
          realTailRadius finite n := by
    have hsqrtpos : 0 < Real.sqrt (realTailEnergy finite n) := Real.sqrt_pos.2 henergy
    rw [realTailRadius]
    field_simp
  rw [hderiv] at hsqrt
  change HasDerivAt (fun t ↦ realTailRadius (sectionLine finite direction t) n)
    ((∑ k ∈ Finset.Ici n, finite k * direction k) /
      realTailRadius finite n) 0 at hsqrt
  exact hsqrt

/-- The derivative of the complete tail surface along a line when every suffix is positive. -/
theorem hasDerivAt_realTailSurface_sectionLine {N : ℕ}
    (finite direction : RealFiniteSection N)
    (henergy : ∀ n, 0 < realTailEnergy finite n) :
    HasDerivAt (fun t ↦ realTailSurface (sectionLine finite direction t))
      (∑ n, realStartingIndexWeight n *
        ((∑ k ∈ Finset.Ici n, finite k * direction k) /
          realTailRadius finite n)) 0 := by
  unfold realTailSurface
  apply HasDerivAt.fun_sum
  intro n _hn
  exact (hasDerivAt_realTailRadius_sectionLine finite direction n (henergy n)).const_mul
    (realStartingIndexWeight n)

/-! ## Coordinate marginals and mass-transfer lines -/

/-- Move one unit of tangent current from `source` to `target`. -/
def pairDirection {N : ℕ} (source target : Fin N) : RealFiniteSection N :=
  fun k ↦ (if k = target then 1 else 0) - (if k = source then 1 else 0)

/-- The first variation in one coordinate on the strictly positive-suffix locus. -/
def realMarginal {N : ℕ} (finite : RealFiniteSection N) (i : Fin N) : ℝ :=
  finite i * ∑ n, if n ≤ i then
    realStartingIndexWeight n / realTailRadius finite n else 0

theorem sum_suffix_pairDirection {N : ℕ} (finite : RealFiniteSection N)
    (source target n : Fin N) :
    ∑ k ∈ Finset.Ici n, finite k * pairDirection source target k =
      (if n ≤ target then finite target else 0) -
        (if n ≤ source then finite source else 0) := by
  classical
  unfold pairDirection
  simp only [mul_sub]
  rw [Finset.sum_sub_distrib]
  simp

theorem hasDerivAt_realTailSurface_pairLine {N : ℕ}
    (finite : RealFiniteSection N) (source target : Fin N)
    (henergy : ∀ n, 0 < realTailEnergy finite n) :
    HasDerivAt
      (fun t ↦ realTailSurface (sectionLine finite (pairDirection source target) t))
      (realMarginal finite target - realMarginal finite source) 0 := by
  have h := hasDerivAt_realTailSurface_sectionLine finite
    (pairDirection source target) henergy
  apply h.congr_deriv
  simp_rw [sum_suffix_pairDirection]
  unfold realMarginal
  classical
  simp_rw [sub_div, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hnt : n ≤ target
    · simp [hnt]
      ring
    · simp [hnt]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _hn
    by_cases hns : n ≤ source
    · simp [hns]
      ring
    · simp [hns]

/-- Turn a real coordinate family into a nonnegative section by positive-part projection. -/
def nnrealSection {N : ℕ} (finite : RealFiniteSection N) : FiniteSection N :=
  fun i ↦ Real.toNNReal (finite i)

theorem realSection_nnrealSection_of_nonneg {N : ℕ} (finite : RealFiniteSection N)
    (hfinite : ∀ i, 0 ≤ finite i) :
    realSection (nnrealSection finite) = finite := by
  funext i
  exact Real.coe_toNNReal _ (hfinite i)

theorem sum_pairDirection {N : ℕ} (source target : Fin N) :
    ∑ k, pairDirection source target k = 0 := by
  classical
  simp [pairDirection]

theorem sectionLine_pairDirection_sum {N : ℕ} (finite : RealFiniteSection N)
    (source target : Fin N) (t : ℝ) :
    ∑ k, sectionLine finite (pairDirection source target) t k = ∑ k, finite k := by
  simp [sectionLine, Finset.sum_add_distrib, ← Finset.mul_sum, sum_pairDirection]

theorem sectionLine_pairDirection_nonneg {N : ℕ} (finite : FiniteSection N)
    {source target : Fin N} (hne : source ≠ target) {t : ℝ}
    (ht : |t| < min (finite source : ℝ) (finite target : ℝ)) (k : Fin N) :
    0 ≤ sectionLine (realSection finite) (pairDirection source target) t k := by
  have htLower : -(min (finite source : ℝ) (finite target : ℝ)) < t :=
    (abs_lt.mp ht).1
  have htUpper : t < min (finite source : ℝ) (finite target : ℝ) :=
    (abs_lt.mp ht).2
  classical
  by_cases hkt : k = target
  · subst k
    simp [sectionLine, realSection, pairDirection, hne.symm]
    have hmin : min (finite source : ℝ) (finite target : ℝ) ≤ finite target :=
      min_le_right _ _
    linarith
  · by_cases hks : k = source
    · subst k
      simp [sectionLine, realSection, pairDirection, hne]
      have hmin : min (finite source : ℝ) (finite target : ℝ) ≤ finite source :=
        min_le_left _ _
      linarith
    · simp [sectionLine, realSection, pairDirection, hkt, hks]

theorem mass_nnrealSection_sectionLine_pairDirection {N : ℕ}
    (finite : FiniteSection N) {source target : Fin N} {t : ℝ}
    (hnonneg : ∀ k, 0 ≤ sectionLine (realSection finite)
      (pairDirection source target) t k) :
    (mass (nnrealSection
      (sectionLine (realSection finite) (pairDirection source target) t)) : ℝ) =
        (mass finite : ℝ) := by
  rw [mass, mass]
  push_cast
  simp_rw [nnrealSection, Real.coe_toNNReal _ (hnonneg _)]
  simpa [realSection] using sectionLine_pairDirection_sum (realSection finite) source target t

theorem realTailSurface_nnrealSection_of_nonneg {N : ℕ} (finite : RealFiniteSection N)
    (hfinite : ∀ i, 0 ≤ finite i) :
    (tailSurface (nnrealSection finite) : ℝ) = realTailSurface finite := by
  rw [← realTailSurface_realSection, realSection_nnrealSection_of_nonneg finite hfinite]

/-- A positive pair of coordinates supplies a two-sided feasible mass-transfer neighborhood. -/
theorem minimizingSection_isLocalMin_pairLine (N : ℕ)
    {source target : Fin (N + 1)} (hne : source ≠ target)
    (hsource : 0 < (minimizingSection N).1 source)
    (htarget : 0 < (minimizingSection N).1 target) :
    IsLocalMin
      (fun t ↦ realTailSurface
        (sectionLine (realSection (minimizingSection N).1)
          (pairDirection source target) t)) 0 := by
  let finite := (minimizingSection N).1
  let radius : ℝ := min (finite source : ℝ) (finite target : ℝ)
  have hradius : 0 < radius := by
    exact lt_min (by exact_mod_cast hsource) (by exact_mod_cast htarget)
  show ∀ᶠ t in 𝓝 0, _
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hradius] with t ht
  have habs : |t| < radius := by
    simpa [Real.dist_eq] using ht
  have hnonneg : ∀ k, 0 ≤ sectionLine (realSection finite)
      (pairDirection source target) t k :=
    sectionLine_pairDirection_nonneg finite hne habs
  let candidate : MassOneSection N :=
    ⟨nnrealSection
        (sectionLine (realSection finite) (pairDirection source target) t),
      fun _ ↦ zero_le,
      by
        change mass (nnrealSection
          (sectionLine (realSection finite) (pairDirection source target) t)) = 1
        apply NNReal.eq
        have hmass := mass_nnrealSection_sectionLine_pairDirection finite hnonneg
        rw [MassOneSection.mass_eq_one (minimizingSection N)] at hmass
        exact hmass⟩
  have hminimum := minimumTailSurface_le N candidate
  change realTailSurface
      (sectionLine (realSection finite) (pairDirection source target) 0) ≤
    realTailSurface
      (sectionLine (realSection finite) (pairDirection source target) t)
  rw [sectionLine_zero, realTailSurface_realSection]
  rw [← realTailSurface_nnrealSection_of_nonneg _ hnonneg]
  exact hminimum

/-- At an interior minimizer, every coordinate has the same first variation. -/
theorem minimizingSection_marginal_eq (N : ℕ)
    (hpositive : ∀ i, 0 < (minimizingSection N).1 i)
    (left right : Fin (N + 1)) :
    realMarginal (realSection (minimizingSection N).1) left =
      realMarginal (realSection (minimizingSection N).1) right := by
  by_cases heq : left = right
  · simp [heq]
  have henergy : ∀ n,
      0 < realTailEnergy (realSection (minimizingSection N).1) n :=
    realTailEnergy_pos_of_last_pos _ (hpositive (Fin.last N))
  have hlocal := minimizingSection_isLocalMin_pairLine N heq
    (hpositive left) (hpositive right)
  have hderiv := hasDerivAt_realTailSurface_pairLine
    (realSection (minimizingSection N).1) left right henergy
  have hzero := hlocal.hasDerivAt_eq_zero hderiv
  linarith

/-- Euler's degree-one identity for the real tail surface. -/
theorem sum_coordinate_marginal_eq_realTailSurface {N : ℕ}
    (finite : RealFiniteSection N)
    (henergy : ∀ n, 0 < realTailEnergy finite n) :
    ∑ i, finite i * realMarginal finite i = realTailSurface finite := by
  classical
  unfold realMarginal realTailSurface
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  have hradius : 0 < realTailRadius finite n := by
    exact Real.sqrt_pos.2 (henergy n)
  calc
    ∑ i, finite i *
          (finite i * if n ≤ i then
            realStartingIndexWeight n / realTailRadius finite n else 0) =
        ∑ i ∈ Finset.Ici n,
          realStartingIndexWeight n / realTailRadius finite n * finite i ^ 2 := by
            simp_rw [mul_ite, mul_zero]
            rw [← Finset.sum_filter]
            rw [show Finset.univ.filter (fun i : Fin N ↦ n ≤ i) = Finset.Ici n by
              ext i
              simp]
            apply Finset.sum_congr rfl
            intro i _hi
            ring
    _ = realStartingIndexWeight n / realTailRadius finite n *
          realTailEnergy finite n := by
            rw [realTailEnergy, Finset.mul_sum]
    _ = realStartingIndexWeight n * realTailRadius finite n := by
            rw [show realTailEnergy finite n = realTailRadius finite n ^ 2 by
              rw [realTailRadius, Real.sq_sqrt (henergy n).le]]
            field_simp

/-! ## A lawful one-sided extension -/

/-- Scale every old coordinate by `1-t` and give the returned mass `t` to one new coordinate. -/
def scaledAppendDirection {N : ℕ} (finite : FiniteSection (N + 1)) :
    RealFiniteSection (N + 2) :=
  Fin.snoc (fun i ↦ -(finite i : ℝ)) 1

/-- The affine scale-and-append path through the silent extension of a finite section. -/
def scaledAppendLine {N : ℕ} (finite : FiniteSection (N + 1)) (t : ℝ) :
    RealFiniteSection (N + 2) :=
  sectionLine (realSection (zeroExtend finite)) (scaledAppendDirection finite) t

@[simp] theorem scaledAppendLine_castSucc {N : ℕ}
    (finite : FiniteSection (N + 1)) (t : ℝ) (i : Fin (N + 1)) :
    scaledAppendLine finite t i.castSucc = (1 - t) * finite i := by
  simp [scaledAppendLine, sectionLine, realSection, scaledAppendDirection, zeroExtend]
  ring

@[simp] theorem scaledAppendLine_last {N : ℕ}
    (finite : FiniteSection (N + 1)) (t : ℝ) :
    scaledAppendLine finite t (Fin.last (N + 1)) = t := by
  simp [scaledAppendLine, sectionLine, realSection, scaledAppendDirection, zeroExtend]

/-- Along an old suffix, the derivative of square energy at the silent extension is minus twice
the old suffix energy. -/
theorem sum_suffix_scaledAppendDirection {N : ℕ}
    (finite : FiniteSection (N + 1)) (n : Fin (N + 1)) :
    ∑ k ∈ Finset.Ici n.castSucc,
        realSection (zeroExtend finite) k * scaledAppendDirection finite k =
      -(tailEnergy finite n : ℝ) := by
  classical
  rw [show (Finset.Ici n.castSucc : Finset (Fin (N + 2))) =
      Finset.univ.filter (fun k ↦ n.castSucc ≤ k) by ext; simp,
    Finset.sum_filter, Fin.sum_univ_castSucc]
  simp [realSection, zeroExtend, scaledAppendDirection, tailEnergy]
  rw [← Finset.sum_filter]
  rw [show Finset.univ.filter (fun x : Fin (N + 1) ↦ n ≤ x) = Finset.Ici n by
    ext x
    simp]
  rw [Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-- The old suffix portion of the appended surface, excluding the new zero suffix. -/
def oldExtensionSurface {N : ℕ} (finite : FiniteSection (N + 1)) (t : ℝ) : ℝ :=
  ∑ n : Fin (N + 1), realStartingIndexWeight n.castSucc *
    realTailRadius (scaledAppendLine finite t) n.castSucc

/-- A smooth surrogate for the appended surface.  On the nonnegative side it is the actual
surface; at zero its new-suffix term is written linearly rather than as `sqrt (t^2)`. -/
def scaledAppendSurface {N : ℕ} (finite : FiniteSection (N + 1)) (t : ℝ) : ℝ :=
  oldExtensionSurface finite t +
    realStartingIndexWeight (Fin.last (N + 1)) * t

theorem hasDerivAt_oldExtensionSurface {N : ℕ}
    (finite : FiniteSection (N + 1))
    (hlast : 0 < finite (Fin.last N)) :
    HasDerivAt (oldExtensionSurface finite) (-(tailSurface finite : ℝ)) 0 := by
  unfold oldExtensionSurface
  have hterm : ∀ n ∈ (Finset.univ : Finset (Fin (N + 1))),
      HasDerivAt
        (fun t ↦ realStartingIndexWeight n.castSucc *
          realTailRadius (scaledAppendLine finite t) n.castSucc)
        (-(realStartingIndexWeight n * (tailRadius finite n : ℝ))) 0 := by
    intro n _hn
    have henergy : 0 < realTailEnergy
        (realSection (zeroExtend finite)) n.castSucc := by
      rw [realTailEnergy_realSection, tailEnergy_zeroExtend_castSucc]
      have h := realTailEnergy_pos_of_last_pos finite hlast n
      rw [realTailEnergy_realSection] at h
      exact_mod_cast h
    have hradius := hasDerivAt_realTailRadius_sectionLine
      (realSection (zeroExtend finite)) (scaledAppendDirection finite) n.castSucc henergy
    have hweighted := hradius.const_mul (realStartingIndexWeight n.castSucc)
    apply hweighted.congr_deriv
    rw [sum_suffix_scaledAppendDirection]
    rw [realTailRadius_realSection, tailRadius_zeroExtend_castSucc]
    rw [show realStartingIndexWeight n.castSucc = realStartingIndexWeight n by
      simp [realStartingIndexWeight]]
    have hrpos : 0 < (tailRadius finite n : ℝ) := by
      rw [← realTailRadius_realSection]
      exact Real.sqrt_pos.2 (realTailEnergy_pos_of_last_pos finite hlast n)
    have hsq : (tailEnergy finite n : ℝ) = (tailRadius finite n : ℝ) ^ 2 := by
      calc
        (tailEnergy finite n : ℝ) = realTailEnergy (realSection finite) n := by
          rw [realTailEnergy_realSection]
        _ = realTailRadius (realSection finite) n ^ 2 := by
          rw [realTailRadius, Real.sq_sqrt
            (realTailEnergy_pos_of_last_pos finite hlast n).le]
        _ = (tailRadius finite n : ℝ) ^ 2 := by rw [realTailRadius_realSection]
    rw [hsq]
    field_simp
  have hsum := HasDerivAt.fun_sum (u := (Finset.univ : Finset (Fin (N + 1)))) hterm
  apply hsum.congr_deriv
  rw [Finset.sum_neg_distrib]
  congr 1
  rw [tailSurface]
  push_cast
  apply Finset.sum_congr rfl
  intro n _hn
  simp

theorem hasDerivAt_scaledAppendSurface {N : ℕ}
    (finite : FiniteSection (N + 1))
    (hlast : 0 < finite (Fin.last N)) :
    HasDerivAt (scaledAppendSurface finite)
      (realStartingIndexWeight (Fin.last (N + 1)) - (tailSurface finite : ℝ)) 0 := by
  unfold scaledAppendSurface
  have hold := hasDerivAt_oldExtensionSurface finite hlast
  have hnew := (hasDerivAt_id (0 : ℝ)).const_mul
    (realStartingIndexWeight (Fin.last (N + 1)))
  convert! hold.add hnew using 1 <;> norm_num <;> ring

theorem scaledAppendLine_nonneg {N : ℕ} (finite : FiniteSection (N + 1))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (k : Fin (N + 2)) :
    0 ≤ scaledAppendLine finite t k := by
  refine Fin.lastCases ?_ (fun i ↦ ?_) k
  · simpa using ht0
  · rw [scaledAppendLine_castSucc]
    exact mul_nonneg (sub_nonneg.mpr ht1) (by positivity)

theorem sum_scaledAppendLine {N : ℕ} (finite : FiniteSection (N + 1))
    (hmass : mass finite = 1) (t : ℝ) :
    ∑ k, scaledAppendLine finite t k = 1 := by
  rw [Fin.sum_univ_castSucc]
  simp_rw [scaledAppendLine_castSucc]
  rw [← Finset.mul_sum]
  have hmassReal : ∑ i, (finite i : ℝ) = 1 := by
    exact_mod_cast hmass
  rw [hmassReal, scaledAppendLine_last]
  ring

theorem mass_nnrealSection_scaledAppendLine {N : ℕ}
    (finite : FiniteSection (N + 1)) (hmass : mass finite = 1)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    mass (nnrealSection (scaledAppendLine finite t)) = 1 := by
  apply NNReal.eq
  rw [mass]
  push_cast
  simp_rw [nnrealSection, Real.coe_toNNReal _ (scaledAppendLine_nonneg finite ht0 ht1 _)]
  exact sum_scaledAppendLine finite hmass t

theorem realTailRadius_scaledAppendLine_last {N : ℕ}
    (finite : FiniteSection (N + 1)) {t : ℝ} (ht : 0 ≤ t) :
    realTailRadius (scaledAppendLine finite t) (Fin.last (N + 1)) = t := by
  rw [realTailRadius]
  have henergy : realTailEnergy (scaledAppendLine finite t) (Fin.last (N + 1)) = t ^ 2 := by
    unfold realTailEnergy
    rw [show (Finset.Ici (Fin.last (N + 1)) : Finset (Fin (N + 2))) =
      {Fin.last (N + 1)} by
        ext k
        simp only [Finset.mem_Ici, Finset.mem_singleton]
        constructor
        · intro h
          exact Fin.le_antisymm (Fin.le_last k) h
        · intro h
          subst k
          exact le_rfl]
    simp
  rw [henergy, Real.sqrt_sq_eq_abs, abs_of_nonneg ht]

/-- On the nonnegative side, the smooth surrogate is exactly the appended finite surface. -/
theorem realTailSurface_scaledAppendLine {N : ℕ}
    (finite : FiniteSection (N + 1)) {t : ℝ} (ht : 0 ≤ t) :
    realTailSurface (scaledAppendLine finite t) = scaledAppendSurface finite t := by
  rw [realTailSurface, Fin.sum_univ_castSucc]
  rw [realTailRadius_scaledAppendLine_last finite ht]
  rfl

@[simp] theorem scaledAppendSurface_zero {N : ℕ}
    (finite : FiniteSection (N + 1)) :
    scaledAppendSurface finite 0 = (tailSurface finite : ℝ) := by
  rw [← realTailSurface_scaledAppendLine finite (le_refl 0)]
  have hline : scaledAppendLine finite 0 = realSection (zeroExtend finite) := by
    unfold scaledAppendLine
    rw [sectionLine_zero]
  rw [hline, realTailSurface_realSection, tailSurface_zeroExtend]

/-- The complete surface contains its first, unweighted suffix radius. -/
theorem first_tailRadius_le_tailSurface {N : ℕ} (finite : FiniteSection (N + 1)) :
    tailRadius finite 0 ≤ tailSurface finite := by
  unfold tailSurface
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset (Fin (N + 1))))
    (f := fun n ↦ startingIndexWeight n * tailRadius finite n)
    (fun n _hn ↦ mul_nonneg zero_le zero_le) (Finset.mem_univ (0 : Fin (N + 1)))
  simpa [startingIndexWeight] using h

/-- Mass one forces the first suffix radius above the inverse square root of the population. -/
theorem one_div_sqrt_card_le_first_tailRadius (N : ℕ) (finite : MassOneSection N) :
    1 / Real.sqrt (N + 1 : ℝ) ≤ (tailRadius finite.1 0 : ℝ) := by
  have hCauchy := sq_sum_le_card_mul_sum_sq
    (s := (Finset.univ : Finset (Fin (N + 1))))
    (f := fun i ↦ (finite.1 i : ℝ))
  have hmass : ∑ i, (finite.1 i : ℝ) = 1 := by
    exact_mod_cast MassOneSection.mass_eq_one finite
  have henergy : ∑ i, (finite.1 i : ℝ) ^ 2 = (tailEnergy finite.1 0 : ℝ) := by
    rw [tailEnergy]
    push_cast
    congr 1
    ext i
    simp
  rw [hmass, henergy] at hCauchy
  norm_num at hCauchy
  have hsqrtCard : 0 < Real.sqrt (N + 1 : ℝ) := by positivity
  have hradius : 0 ≤ (tailRadius finite.1 0 : ℝ) := by positivity
  have hsqrtCardSq : Real.sqrt (N + 1 : ℝ) ^ 2 = N + 1 := by
    rw [Real.sq_sqrt]
    positivity
  have hradiusSq : (tailRadius finite.1 0 : ℝ) ^ 2 = (tailEnergy finite.1 0 : ℝ) := by
    norm_cast
    exact NNReal.sq_sqrt _
  have hproduct : 1 ≤ Real.sqrt (N + 1 : ℝ) * (tailRadius finite.1 0 : ℝ) := by
    have hproductNonneg : 0 ≤
        Real.sqrt (N + 1 : ℝ) * (tailRadius finite.1 0 : ℝ) :=
      mul_nonneg hsqrtCard.le hradius
    by_contra hnot
    have hlt : Real.sqrt (N + 1 : ℝ) * (tailRadius finite.1 0 : ℝ) < 1 :=
      lt_of_not_ge hnot
    have hsqLt := (sq_lt_sq₀ hproductNonneg zero_le_one).2 hlt
    have hsqGe : 1 ≤
        (Real.sqrt (N + 1 : ℝ) * (tailRadius finite.1 0 : ℝ)) ^ 2 := by
      rw [mul_pow, hsqrtCardSq, hradiusSq]
      exact hCauchy
    linarith
  rw [div_le_iff₀ hsqrtCard]
  simpa [mul_comm] using hproduct

/-- The next one-based weight is strictly below every mass-one finite tail surface. -/
theorem next_weight_lt_tailSurface (N : ℕ) (finite : MassOneSection N) :
    realStartingIndexWeight (Fin.last (N + 1)) < (tailSurface finite.1 : ℝ) := by
  have hsqrtLt : Real.sqrt (N + 1 : ℝ) < Real.sqrt (N + 2 : ℝ) := by
    exact Real.sqrt_lt_sqrt (by positivity : (0 : ℝ) ≤ N + 1) (by norm_num)
  have hweight : 1 / Real.sqrt (N + 2 : ℝ) < 1 / Real.sqrt (N + 1 : ℝ) :=
    one_div_lt_one_div_of_lt (by positivity) hsqrtLt
  have hradius := one_div_sqrt_card_le_first_tailRadius N finite
  have hsurface : (tailRadius finite.1 0 : ℝ) ≤ (tailSurface finite.1 : ℝ) := by
    exact_mod_cast first_tailRadius_le_tailSurface finite.1
  calc
    realStartingIndexWeight (Fin.last (N + 1)) =
        1 / Real.sqrt (N + 2 : ℝ) := by
          have hlast : (((Fin.last (N + 1)).val : ℕ) : ℝ) = N + 1 := by simp
          rw [realStartingIndexWeight, hlast]
          congr 1
          ring
    _ < 1 / Real.sqrt (N + 1 : ℝ) := hweight
    _ ≤ (tailRadius finite.1 0 : ℝ) := hradius
    _ ≤ (tailSurface finite.1 : ℝ) := hsurface

/-- A negative derivative supplies an arbitrarily local positive point with smaller value. -/
theorem exists_pos_lt_of_hasDerivAt_neg {f : ℝ → ℝ} {derivative bound : ℝ}
    (hderiv : HasDerivAt f derivative 0) (hnegative : derivative < 0)
    (hbound : 0 < bound) :
    ∃ t : ℝ, 0 < t ∧ t < bound ∧ f t < f 0 := by
  have hslope : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      t⁻¹ * (f t - f 0) < 0 := by
    have htendsto := hderiv.tendsto_slope_zero_right
    have hevent := htendsto.eventually (Iio_mem_nhds hnegative)
    simpa only [zero_add, one_smul, smul_eq_mul] using hevent
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Set.Ioc 0 (bound / 2) :=
    Ioc_mem_nhdsGT (by linarith)
  obtain ⟨t, hslopeNeg, ht⟩ := (hslope.and hsmall).exists
  have htInv : 0 < t⁻¹ := inv_pos.mpr ht.1
  have hdiff : f t - f 0 < 0 := by
    rcases (mul_neg_iff.mp hslopeNeg) with hgood | hbad
    · exact hgood.2
    · exact False.elim ((not_lt_of_ge htInv.le) hbad.1)
  exact ⟨t, ht.1, by linarith [ht.2], sub_neg.mp hdiff⟩

/-- A positive final coordinate makes the next attained minimum strictly smaller. -/
theorem minimumTailSurface_succ_lt_of_last_pos (N : ℕ)
    (hlast : 0 < (minimizingSection N).1 (Fin.last N)) :
    minimumTailSurface (N + 1) < minimumTailSurface N := by
  let finite := (minimizingSection N).1
  have hderiv := hasDerivAt_scaledAppendSurface finite hlast
  have hnegative : realStartingIndexWeight (Fin.last (N + 1)) -
      (tailSurface finite : ℝ) < 0 :=
    sub_neg.mpr (next_weight_lt_tailSurface N (minimizingSection N))
  obtain ⟨t, ht0, ht1, hdecrease⟩ :=
    exists_pos_lt_of_hasDerivAt_neg hderiv hnegative zero_lt_one
  have hnonneg : ∀ k, 0 ≤ scaledAppendLine finite t k :=
    scaledAppendLine_nonneg finite ht0.le ht1.le
  let candidate : MassOneSection (N + 1) :=
    ⟨nnrealSection (scaledAppendLine finite t),
      fun _ ↦ zero_le,
      by
        change mass (nnrealSection (scaledAppendLine finite t)) = 1
        exact mass_nnrealSection_scaledAppendLine finite
          (MassOneSection.mass_eq_one (minimizingSection N)) ht0.le ht1.le⟩
  have hminimum := minimumTailSurface_le (N + 1) candidate
  apply NNReal.coe_lt_coe.mp
  calc
    (minimumTailSurface (N + 1) : ℝ) ≤ (tailSurface candidate.1 : ℝ) := by
      exact_mod_cast hminimum
    _ = realTailSurface (scaledAppendLine finite t) :=
      realTailSurface_nnrealSection_of_nonneg _ hnonneg
    _ = scaledAppendSurface finite t := realTailSurface_scaledAppendLine finite ht0.le
    _ < scaledAppendSurface finite 0 := hdecrease
    _ = (minimumTailSurface N : ℝ) := by simp [finite, minimumTailSurface]

/-- Remove the final coordinate from a nonempty successor-length section. -/
def dropLast {N : ℕ} (finite : FiniteSection (N + 2)) : FiniteSection (N + 1) :=
  fun i ↦ finite i.castSucc

theorem zeroExtend_dropLast_of_last_eq_zero {N : ℕ}
    (finite : FiniteSection (N + 2))
    (hlast : finite (Fin.last (N + 1)) = 0) :
    zeroExtend (dropLast finite) = finite := by
  funext i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simp [hlast]
  · simp [dropLast]

/-- The chosen minimizer has a positive final coordinate at every nonempty finite length. -/
theorem minimizingSection_last_pos : ∀ N : ℕ,
    0 < (minimizingSection N).1 (Fin.last N)
  | 0 => by
      have hmass := MassOneSection.mass_eq_one (minimizingSection 0)
      have hvalue : (minimizingSection 0).1 (0 : Fin 1) = 1 := by
        simpa [mass] using hmass
      have hlastValue : (minimizingSection 0).1 (Fin.last 0) = 1 := by
        simpa using hvalue
      rw [hlastValue]
      exact zero_lt_one
  | N + 1 => by
      have hstrict := minimumTailSurface_succ_lt_of_last_pos N
        (minimizingSection_last_pos N)
      by_contra hnot
      have hzero : (minimizingSection (N + 1)).1 (Fin.last (N + 1)) = 0 :=
        nonpos_iff_eq_zero.mp (not_lt.mp hnot)
      let shortened : MassOneSection N :=
        ⟨dropLast (minimizingSection (N + 1)).1,
          fun _ ↦ zero_le,
          by
            change mass (dropLast (minimizingSection (N + 1)).1) = 1
            have hmass := mass_zeroExtend (dropLast (minimizingSection (N + 1)).1)
            rw [zeroExtend_dropLast_of_last_eq_zero _ hzero] at hmass
            rw [← hmass]
            exact MassOneSection.mass_eq_one (minimizingSection (N + 1))⟩
      have hminimum := minimumTailSurface_le N shortened
      have hsurface := tailSurface_zeroExtend (dropLast (minimizingSection (N + 1)).1)
      rw [zeroExtend_dropLast_of_last_eq_zero _ hzero] at hsurface
      have hnotStrict : minimumTailSurface N ≤ minimumTailSurface (N + 1) := by
        calc
          minimumTailSurface N ≤ tailSurface shortened.1 := hminimum
          _ = tailSurface (minimizingSection (N + 1)).1 := hsurface.symm
          _ = minimumTailSurface (N + 1) := rfl
      exact (not_le_of_gt hstrict) hnotStrict

/-- The attained mass-one tail surface strictly decreases whenever one genuine coordinate is
added.  This is the unconditional form returned by the simultaneous last-positivity induction. -/
theorem minimumTailSurface_succ_lt (N : ℕ) :
    minimumTailSurface (N + 1) < minimumTailSurface N :=
  minimumTailSurface_succ_lt_of_last_pos N (minimizingSection_last_pos N)

theorem realMarginal_pos_of_coordinate_pos {N : ℕ}
    (finite : RealFiniteSection N) (i : Fin N)
    (hcoordinate : 0 < finite i)
    (henergy : ∀ n, 0 < realTailEnergy finite n) :
    0 < realMarginal finite i := by
  unfold realMarginal
  apply mul_pos hcoordinate
  apply Finset.sum_pos'
  · intro n _hn
    split_ifs
    · exact div_nonneg (realStartingIndexWeight_pos n).le
        (Real.sqrt_nonneg _)
    · exact le_rfl
  · refine ⟨i, Finset.mem_univ i, ?_⟩
    simp only [le_refl, ↓reduceIte]
    exact div_pos (realStartingIndexWeight_pos i) (Real.sqrt_pos.2 (henergy i))

theorem sectionLine_pairDirection_nonneg_of_target_zero {N : ℕ}
    (finite : FiniteSection N) {source target : Fin N}
    (hne : source ≠ target) (htarget : finite target = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (htSource : t ≤ finite source) (k : Fin N) :
    0 ≤ sectionLine (realSection finite) (pairDirection source target) t k := by
  classical
  by_cases hkt : k = target
  · subst k
    simp [sectionLine, realSection, pairDirection, hne.symm, htarget, ht0]
  · by_cases hks : k = source
    · subst k
      simp [sectionLine, realSection, pairDirection, hne]
      exact htSource
    · simp [sectionLine, realSection, pairDirection, hkt, hks]

/-- Every coordinate of the attained finite minimizer is strictly positive. -/
theorem minimizingSection_coordinate_pos (N : ℕ) (i : Fin (N + 1)) :
    0 < (minimizingSection N).1 i := by
  let finite := (minimizingSection N).1
  have hlast : 0 < finite (Fin.last N) := minimizingSection_last_pos N
  by_contra hnot
  have hzero : finite i = 0 := nonpos_iff_eq_zero.mp (not_lt.mp hnot)
  have hne : Fin.last N ≠ i := by
    intro heq
    have hlastZero : finite (Fin.last N) = 0 := by simpa [heq] using hzero
    rw [hlastZero] at hlast
    exact lt_irrefl 0 hlast
  have henergy : ∀ n, 0 < realTailEnergy (realSection finite) n :=
    realTailEnergy_pos_of_last_pos finite hlast
  have hmarginalZero : realMarginal (realSection finite) i = 0 := by
    simp [realMarginal, realSection, hzero]
  have hmarginalLast : 0 < realMarginal (realSection finite) (Fin.last N) :=
    realMarginal_pos_of_coordinate_pos _ _ (by exact_mod_cast hlast) henergy
  have hderiv := hasDerivAt_realTailSurface_pairLine (realSection finite)
    (Fin.last N) i henergy
  have hnegative : realMarginal (realSection finite) i -
      realMarginal (realSection finite) (Fin.last N) < 0 := by
    rw [hmarginalZero]
    linarith
  obtain ⟨t, ht0, htBound, hdecrease⟩ := exists_pos_lt_of_hasDerivAt_neg
    hderiv hnegative (by exact_mod_cast hlast)
  have hnonneg : ∀ k, 0 ≤ sectionLine (realSection finite)
      (pairDirection (Fin.last N) i) t k :=
    sectionLine_pairDirection_nonneg_of_target_zero finite hne hzero ht0.le htBound.le
  let candidate : MassOneSection N :=
    ⟨nnrealSection
        (sectionLine (realSection finite) (pairDirection (Fin.last N) i) t),
      fun _ ↦ zero_le,
      by
        change mass (nnrealSection
          (sectionLine (realSection finite) (pairDirection (Fin.last N) i) t)) = 1
        apply NNReal.eq
        have hmass := mass_nnrealSection_sectionLine_pairDirection finite hnonneg
        rw [MassOneSection.mass_eq_one (minimizingSection N)] at hmass
        exact hmass⟩
  have hminimum := minimumTailSurface_le N candidate
  have hminimumReal : realTailSurface (realSection finite) ≤
      realTailSurface
        (sectionLine (realSection finite) (pairDirection (Fin.last N) i) t) := by
    calc
      realTailSurface (realSection finite) = (tailSurface finite : ℝ) :=
        realTailSurface_realSection finite
      _ ≤ (tailSurface candidate.1 : ℝ) := by exact_mod_cast hminimum
      _ = realTailSurface
          (sectionLine (realSection finite) (pairDirection (Fin.last N) i) t) :=
        realTailSurface_nnrealSection_of_nonneg _ hnonneg
  have hzeroLine : sectionLine (realSection finite)
      (pairDirection (Fin.last N) i) 0 = realSection finite := sectionLine_zero _ _
  rw [hzeroLine] at hdecrease
  exact (not_lt_of_ge hminimumReal) hdecrease

/-- Every Euler marginal of the attained mass-one minimizer is its minimum tail surface. -/
theorem minimizingSection_euler (N : ℕ) (i : Fin (N + 1)) :
    realMarginal (realSection (minimizingSection N).1) i =
      (minimumTailSurface N : ℝ) := by
  let finite := realSection (minimizingSection N).1
  have hpositive : ∀ j, 0 < (minimizingSection N).1 j :=
    minimizingSection_coordinate_pos N
  have hmarginal : ∀ j, realMarginal finite j = realMarginal finite i := by
    intro j
    exact minimizingSection_marginal_eq N hpositive j i
  have henergy : ∀ n, 0 < realTailEnergy finite n :=
    realTailEnergy_pos_of_last_pos _ (hpositive (Fin.last N))
  have heuler := sum_coordinate_marginal_eq_realTailSurface finite henergy
  have hmass : ∑ j, finite j = 1 := by
    have hmassNN := MassOneSection.mass_eq_one (minimizingSection N)
    rw [mass] at hmassNN
    have hmassReal : ∑ j, ((minimizingSection N).1 j : ℝ) = 1 := by
      exact_mod_cast hmassNN
    simpa [finite, realSection] using hmassReal
  calc
    realMarginal finite i = (∑ j, finite j) * realMarginal finite i := by rw [hmass, one_mul]
    _ = ∑ j, finite j * realMarginal finite j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _hj
      rw [hmarginal j]
    _ = realTailSurface finite := heuler
    _ = (minimumTailSurface N : ℝ) := by
      simp [finite, minimumTailSurface]

/-! ## The finite de Bruijn recurrence -/

/-- The cumulative inverse-radius weight appearing in the Euler marginal. -/
def realCumulativeWeight {N : ℕ} (finite : RealFiniteSection N) (i : Fin N) : ℝ :=
  ∑ n ∈ Finset.Iic i, realStartingIndexWeight n / realTailRadius finite n

theorem realMarginal_eq_mul_cumulative {N : ℕ}
    (finite : RealFiniteSection N) (i : Fin N) :
    realMarginal finite i = finite i * realCumulativeWeight finite i := by
  unfold realMarginal realCumulativeWeight
  congr 1
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext n
    simp
  · intro n _hn
    rfl

theorem realCumulativeWeight_succ {N : ℕ}
    (finite : RealFiniteSection (N + 1)) (i : Fin N) :
    realCumulativeWeight finite i.succ =
      realCumulativeWeight finite i.castSucc +
        realStartingIndexWeight i.succ / realTailRadius finite i.succ := by
  unfold realCumulativeWeight
  rw [show (Finset.Iic i.succ : Finset (Fin (N + 1))) =
      insert i.succ (Finset.Iic i.castSucc) by
        ext n
        simp only [Finset.mem_Iic, Finset.mem_insert]
        constructor
        · intro h
          by_cases heq : n = i.succ
          · exact Or.inl heq
          · right
            have hneVal : n.val ≠ i.val + 1 := by
              intro hval
              apply heq
              apply Fin.ext
              exact hval
            change n.val ≤ i.val
            change n.val ≤ i.val + 1 at h
            omega
        · rintro (rfl | h)
          · exact le_rfl
          · exact h.trans (Fin.castSucc_le_succ i)]
  rw [Finset.sum_insert]
  · ac_rfl
  · simp

/-- The ratio of a suffix radius to its current positive coordinate.  Mathematical index `n+1`
is represented by Lean index `n`. -/
def finiteRecurrenceValue (N : ℕ) (i : Fin (N + 1)) : ℝ :=
  (tailRadius (minimizingSection N).1 i : ℝ) /
    ((minimizingSection N).1 i : ℝ)

theorem tailRadius_sq_eq_tailEnergy_real {N : ℕ}
    (finite : FiniteSection N) (i : Fin N) :
    (tailRadius finite i : ℝ) ^ 2 = (tailEnergy finite i : ℝ) := by
  norm_cast
  exact NNReal.sq_sqrt _

theorem coordinate_le_tailRadius {N : ℕ}
    (finite : FiniteSection N) (i : Fin N) :
    finite i ≤ tailRadius finite i := by
  rw [tailRadius, ← NNReal.sqrt_sq (finite i), NNReal.sqrt_le_sqrt]
  unfold tailEnergy
  exact Finset.single_le_sum
    (s := Finset.Ici i) (f := fun k ↦ finite k ^ 2)
    (fun k _hk ↦ by positivity) (Finset.mem_Ici.mpr le_rfl)

/-- Every recurrence value is admissible for the next principal square root. -/
theorem finiteRecurrenceValue_one_le (N : ℕ) (i : Fin (N + 1)) :
    1 ≤ finiteRecurrenceValue N i := by
  have hpositive : 0 < ((minimizingSection N).1 i : ℝ) := by
    exact_mod_cast minimizingSection_coordinate_pos N i
  rw [finiteRecurrenceValue, le_div_iff₀ hpositive]
  simpa using (show ((minimizingSection N).1 i : ℝ) ≤
    (tailRadius (minimizingSection N).1 i : ℝ) by
      exact_mod_cast coordinate_le_tailRadius (minimizingSection N).1 i)

/-- The first recurrence value is the attained finite sharp coefficient. -/
theorem finiteRecurrenceValue_initial (N : ℕ) :
    finiteRecurrenceValue N 0 = (finiteSharpCoefficient N : ℝ) := by
  let finite := (minimizingSection N).1
  have hcoordinate : 0 < (finite 0 : ℝ) := by
    exact_mod_cast minimizingSection_coordinate_pos N 0
  have hradius : 0 < (tailRadius finite 0 : ℝ) := by
    have hle : (finite 0 : ℝ) ≤ (tailRadius finite 0 : ℝ) := by
      exact_mod_cast coordinate_le_tailRadius finite 0
    exact hcoordinate.trans_le hle
  have hminimum : 0 < (minimumTailSurface N : ℝ) := by
    exact_mod_cast minimumTailSurface_pos N
  have heuler := minimizingSection_euler N (0 : Fin (N + 1))
  have heulerFirst : (finite 0 : ℝ) / (tailRadius finite 0 : ℝ) =
      (minimumTailSurface N : ℝ) := by
    simpa [realMarginal, realSection, finite, realStartingIndexWeight, div_eq_mul_inv] using heuler
  rw [finiteRecurrenceValue, finiteSharpCoefficient]
  change (tailRadius finite 0 : ℝ) / (finite 0 : ℝ) =
    ((minimumTailSurface N)⁻¹ : ℝ)
  field_simp [hcoordinate.ne', hradius.ne', hminimum.ne'] at heulerFirst ⊢
  nlinarith

theorem realStartingIndexWeight_succ {N : ℕ} (i : Fin N) :
    realStartingIndexWeight (i.succ : Fin (N + 1)) =
      1 / Real.sqrt (i.val + 2 : ℝ) := by
  unfold realStartingIndexWeight
  rw [inv_eq_one_div]
  congr 2
  norm_cast

/-- Adjacent Euler equations give the additive ratio increment in de Bruijn's recurrence. -/
theorem finiteRecurrenceValue_adjacent_difference {N : ℕ} (i : Fin N) :
    (tailRadius (minimizingSection N).1 i.succ : ℝ) /
          ((minimizingSection N).1 i.succ : ℝ) -
        (tailRadius (minimizingSection N).1 i.succ : ℝ) /
          ((minimizingSection N).1 i.castSucc : ℝ) =
      (finiteSharpCoefficient N : ℝ) / Real.sqrt (i.val + 2 : ℝ) := by
  let finite := (minimizingSection N).1
  let realFinite := realSection finite
  let previous : Fin (N + 1) := i.castSucc
  let next : Fin (N + 1) := i.succ
  have hPreviousEuler := minimizingSection_euler N previous
  have hNextEuler := minimizingSection_euler N next
  rw [realMarginal_eq_mul_cumulative] at hPreviousEuler hNextEuler
  have hCumulative := realCumulativeWeight_succ realFinite i
  have hPrevious : 0 < (finite previous : ℝ) := by
    exact_mod_cast minimizingSection_coordinate_pos N previous
  have hNext : 0 < (finite next : ℝ) := by
    exact_mod_cast minimizingSection_coordinate_pos N next
  have hRadius : 0 < (tailRadius finite next : ℝ) := by
    exact hNext.trans_le (by exact_mod_cast coordinate_le_tailRadius finite next)
  have hMinimum : 0 < (minimumTailSurface N : ℝ) := by
    exact_mod_cast minimumTailSurface_pos N
  have hSqrt : 0 < Real.sqrt (i.val + 2 : ℝ) := by positivity
  have hPreviousQ : realCumulativeWeight realFinite previous =
      (minimumTailSurface N : ℝ) / (finite previous : ℝ) := by
    rw [eq_div_iff hPrevious.ne']
    change (finite previous : ℝ) * realCumulativeWeight realFinite previous =
      (minimumTailSurface N : ℝ) at hPreviousEuler
    simpa [mul_comm] using hPreviousEuler
  have hNextQ : realCumulativeWeight realFinite next =
      (minimumTailSurface N : ℝ) / (finite next : ℝ) := by
    rw [eq_div_iff hNext.ne']
    change (finite next : ℝ) * realCumulativeWeight realFinite next =
      (minimumTailSurface N : ℝ) at hNextEuler
    simpa [mul_comm] using hNextEuler
  have hRadiusReal : realTailRadius realFinite next = (tailRadius finite next : ℝ) := by
    simp [realFinite]
  have hWeight : realStartingIndexWeight next = 1 / Real.sqrt (i.val + 2 : ℝ) := by
    simpa [next] using realStartingIndexWeight_succ i
  rw [hNextQ, hPreviousQ, hRadiusReal, hWeight] at hCumulative
  have hCoefficient : (finiteSharpCoefficient N : ℝ) =
      1 / (minimumTailSurface N : ℝ) := by
    simp [finiteSharpCoefficient, div_eq_mul_inv]
  rw [hCoefficient]
  change (tailRadius finite next : ℝ) / (finite next : ℝ) -
      (tailRadius finite next : ℝ) / (finite previous : ℝ) =
    (1 / (minimumTailSurface N : ℝ)) / Real.sqrt (i.val + 2 : ℝ)
  field_simp [hPrevious.ne', hNext.ne', hRadius.ne', hMinimum.ne', hSqrt.ne'] at hCumulative ⊢
  nlinarith only [hCumulative]

/-- Adjacent suffix balance is exactly the principal square-root term of the recurrence. -/
theorem finiteRecurrenceValue_sqrt_previous {N : ℕ} (i : Fin N) :
    Real.sqrt ((finiteRecurrenceValue N i.castSucc) ^ 2 - 1) =
      (tailRadius (minimizingSection N).1 i.succ : ℝ) /
        ((minimizingSection N).1 i.castSucc : ℝ) := by
  let finite := (minimizingSection N).1
  let previous : Fin (N + 1) := i.castSucc
  let next : Fin (N + 1) := i.succ
  have hPrevious : 0 < (finite previous : ℝ) := by
    exact_mod_cast minimizingSection_coordinate_pos N previous
  have hNextRadius : 0 ≤ (tailRadius finite next : ℝ) := by positivity
  have hRadicand : 0 ≤ (finiteRecurrenceValue N previous) ^ 2 - 1 := by
    have hone := finiteRecurrenceValue_one_le N previous
    nlinarith [sq_nonneg (finiteRecurrenceValue N previous - 1)]
  apply (Real.sqrt_eq_iff_eq_sq hRadicand
    (div_nonneg hNextRadius hPrevious.le)).2
  have hbalanceNN := tailEnergy_balance finite i
  have hbalance : (tailEnergy finite previous : ℝ) =
      (finite previous : ℝ) ^ 2 + (tailEnergy finite next : ℝ) := by
    exact_mod_cast hbalanceNN
  have hPreviousRadius := tailRadius_sq_eq_tailEnergy_real finite previous
  have hNextRadiusSq := tailRadius_sq_eq_tailEnergy_real finite next
  unfold finiteRecurrenceValue
  change ((tailRadius finite previous : ℝ) / (finite previous : ℝ)) ^ 2 - 1 =
    ((tailRadius finite next : ℝ) / (finite previous : ℝ)) ^ 2
  field_simp [hPrevious.ne']
  nlinarith

/-- The attained finite ratio sequence satisfies de Bruijn's recurrence.  Lean index `i.succ`
is mathematical index `i.val + 2`. -/
theorem finiteRecurrenceValue_step {N : ℕ} (i : Fin N) :
    finiteRecurrenceValue N i.succ =
      (finiteSharpCoefficient N : ℝ) / Real.sqrt (i.val + 2 : ℝ) +
        Real.sqrt ((finiteRecurrenceValue N i.castSucc) ^ 2 - 1) := by
  have hadjacent := finiteRecurrenceValue_adjacent_difference i
  have hsqrt := finiteRecurrenceValue_sqrt_previous i
  rw [hsqrt]
  unfold finiteRecurrenceValue
  linarith

/-- The final recurrence value is one because its suffix contains only its own coordinate. -/
theorem finiteRecurrenceValue_terminal (N : ℕ) :
    finiteRecurrenceValue N (Fin.last N) = 1 := by
  let finite := (minimizingSection N).1
  have hcoordinate : 0 < (finite (Fin.last N) : ℝ) := by
    exact_mod_cast minimizingSection_last_pos N
  have hradius : tailRadius finite (Fin.last N) = finite (Fin.last N) := by
    unfold tailRadius tailEnergy
    rw [show (Finset.Ici (Fin.last N) : Finset (Fin (N + 1))) = {Fin.last N} by
      ext k
      simp only [Finset.mem_Ici, Finset.mem_singleton]
      constructor
      · intro h
        exact Fin.le_antisymm (Fin.le_last k) h
      · intro h
        subst k
        exact le_rfl]
    simp
  rw [finiteRecurrenceValue, hradius]
  exact div_self hcoordinate.ne'

/-- A finite dependent recurrence prefix.  Admissibility is carried at every index, so the
principal square root in each successor law is never silently evaluated outside its real domain. -/
structure AdmissibleFiniteRecurrence (N : ℕ) (coefficient : ℝ) where
  value : Fin (N + 1) → ℝ
  admissible : ∀ i, 1 ≤ value i
  initial : value 0 = coefficient
  step : ∀ i : Fin N,
    value i.succ = coefficient / Real.sqrt (i.val + 2 : ℝ) +
      Real.sqrt ((value i.castSucc) ^ 2 - 1)
  terminal : value (Fin.last N) = 1

/-- The attained finite sharp coefficient returns its complete admissible recurrence prefix. -/
def attainedFiniteRecurrence (N : ℕ) :
    AdmissibleFiniteRecurrence N (finiteSharpCoefficient N : ℝ) where
  value := finiteRecurrenceValue N
  admissible := finiteRecurrenceValue_one_le N
  initial := finiteRecurrenceValue_initial N
  step := finiteRecurrenceValue_step
  terminal := finiteRecurrenceValue_terminal N

section Audit

#print axioms minimumTailSurface_succ_lt
#print axioms minimizingSection_coordinate_pos
#print axioms minimizingSection_euler
#print axioms finiteRecurrenceValue_one_le
#print axioms finiteRecurrenceValue_initial
#print axioms finiteRecurrenceValue_step
#print axioms finiteRecurrenceValue_terminal
#print axioms attainedFiniteRecurrence

end Audit

end Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail
