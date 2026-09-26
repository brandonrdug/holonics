import Holonics.Transport.NavigatorTraceFaces
import Holonics.Physics.CompositeMassEnergy
import Mathlib.Tactic

/-!
# Site kinds: a navigator site is a rotation, a null lock or a boost, read from its matrix

[definition] A navigator site is a two-state material `M` read through its two conserved faces,
the trace `a = tr M` and the determinant `q = det M` (`Geometry/LocalFactor.companion`,
`Transport/NavigatorTraceFaces`). Its factor is `1 − aT + qT²`, its characteristic polynomial is
`λ² − aλ + q` (`det_sub_eq`), and its **discriminant face** is `a² − 4q`. The null-cone record §4
classifies a site of **positive determinant** by that face; a site of negative determinant
reverses orientation (a reflection, such as the Swing) and a site of zero determinant is singular
(degenerate). Neither of those two has a kind among the three:

```text
reflection q < 0         two real eigenvalues of opposite sign; the site reverses orientation
degenerate q = 0         0 is an eigenvalue; the site is singular
rotation   q > 0, a² < 4q  no real eigenvalue; the factor's form x² − axy + qy² is definite
null       q > 0, a² = 4q  the traceless part is nilpotent: a shear (the lock) or a scalar
boost      q > 0, a² > 4q  two distinct real eigenvalues of one sign; at q = 1 they are k, k⁻¹
```

The Lorentz factor of a site is projective: `γ² = tr²/(4 det)` is unchanged by rescaling the
material (`lorentz_factor_sq_smul`), and only at `det = 1` is `γ = tr/2`.

[proved-derived; formal-checked] What is proved.

1. **The traceless part squares to the discriminant.** For every two-state material,
   `(M − (tr M/2)·1)² = ((tr M)² − 4 det M)/4 · 1` (`traceless_sq`).
2. **The kinds are proved from the matrix** over `ℝ`, not read off the definition:
   - rotation ⇔ `M` has no real eigenvalue (`rotation_iff_no_real_eigenvalue`), ⇔ the factor's
     binary form is positive definite (`rotation_iff_definite`), and for `q > 0` ⇔ the factor has
     no real root (`rotation_iff_no_real_root`); for integer faces the factor then splits through
     the Weil root of squared modulus `q` (`rotation_splits_through_weil_root`);
   - null ⇔ `det M > 0` and the traceless part is nilpotent (`null_iff_traceless_nilpotent`), and a
     companion site's traceless part is never zero (`companion_traceless_ne_zero`): a null
     companion is the lock, a shear;
   - boost ⇔ `M` has two distinct real eigenvalues of one sign (`boost_iff_two_real_eigenvalues`);
   - reflection ⇔ `M` has real eigenvalues of opposite signs (`reflection_iff_opposite_eigenvalues`);
   - degenerate ⇔ `0` is an eigenvalue (`degenerate_iff_zero_eigenvalue`).
   Every material has exactly one kind (`siteKind` is total), so for `det M > 0` the three
   characterizations are exhaustive and exclusive (`site_trichotomy`).
3. **A boost with `det = 1`, `tr > 2`** has a real Doppler ratio `k > 1` with `tr = k + k⁻¹`, an
   eigenvalue of the site, whose Lorentz faces `γ = tr/2`, `γβ = (k − k⁻¹)/2` satisfy
   `γ² − (γβ)² = 1` and `(γβ)² = (a² − 4)/4` (`boost_doppler_ratio`); the site then acts as the
   `unitBoost` of `Physics/CompositeMassEnergy` and preserves the Lorentz norm
   (`boost_site_is_a_lorentz_boost`). The rational ratio `k = 3` gives `(γ, β) = (5/3, 4/5)`
   (`rational_doppler_three`).
4. **Joined to the machine's trace faces.** The kind is conserved by phase carriage
   (`carried_site_kind`, from `NavigatorTraceFaces`), and a companion site has its factor's kind
   (`companion_siteKind`).
5. **The trace counts of a determinant-one integer site.** With `t_n = tr(Mⁿ)` (the recurrence
   `Geometry/TraceSequence.trace`, `trace_pow_eq`), `|t_n| ≤ 2` for every `n` exactly when the
   site is not a boost (`bounded_iff_not_boost`); a boost's counts grow, `n + 2 ≤ |t_n|`
   (`boost_counts_grow`); with `k + k⁻¹ = a`, `t_n = kⁿ + k⁻ⁿ` and `kⁿ ≤ t_n ≤ 2kⁿ` for `k ≥ 1`
   (`boost_counts_are_doppler_powers`, `boost_counts_sandwich`), so the growth rate is exactly the
   rapidity: `(1/n) log t_n → log k` (`boost_count_rate`). For a nonnegative integer adjacency,
   `t_n` counts its closed walks of length `n`, and the rate is the entropy of that graph. On the
   two-clock torus the reading is different: `det(Mⁿ − 1) = 2 − t_n` (`det_pow_sub_one`), whose
   absolute value is the classical count of period-`n` points (the Lefschetz reading, not
   formalized here), with the same rate `log k` for `k > 1` (`torus_count_rate`).
6. **Hasse sites are rotations.** An integer trace at a prime determinant within the Hasse interval
   `a² ≤ 4p` never sits on the null cone (`hasse_site_is_rotation`); this generalizes
   `TraceSequence.theHasseIntervalAtTwoIsStrict` from `p = 2` to every prime.

[counterexample; formal-checked] The cat map `[[2,1],[1,1]]` is a boost with `γ = 3/2` and
`(γβ)² = 5/4`, which is not a rational square (`catMap_boost`): a boost's Doppler ratio is a
quadratic constraint identity, rational only when `(tr² − 4)/4` is a rational square. The Swing
`[[0,1],[1,0]]` has `det = −1` and two fixed eigenvalues `±1`: it is a reflection, not a boost
(`swing_is_reflection`). The kind is a class function and not an action certificate:
`identityTwo` and `unipotentTwo` are both null (`identity_and_shear_are_both_null`).

No `axiom`, no `sorry`.
-/

namespace Holonics.Compression.Landmark.SiteKind

open Matrix
open Holonics.Geometry.LocalFactor Holonics.Transport.NavigatorTraceFaces
open Holonics.Transport.HelicalPairInteraction

/-! ## 1. The traceless part squares to the discriminant -/

section Traceless

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- [definition] The discriminant face of a site with trace face `a` and determinant face `q`. -/
def discriminant (a q : K) : K := a ^ 2 - 4 * q

/-- [proved-derived; formal-checked] **The traceless part of a two-state site squares to a quarter
of its discriminant:** `(M − (tr M/2)·1)² = ((tr M)² − 4 det M)/4 · 1`. -/
theorem traceless_sq (M : Matrix (Fin 2) (Fin 2) K) :
    (M - (M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) K)) ^ 2
      = (discriminant M.trace M.det / 4) • (1 : Matrix (Fin 2) (Fin 2) K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
      discriminant] <;> ring

end Traceless

/-! ## 2. The trichotomy -/

/-- [definition] The kinds of a navigator site: three for a positive determinant, and the
reflection and degenerate readings outside them. -/
inductive Kind
  | rotation
  | null
  | boost
  | reflection
  | degenerate
deriving DecidableEq, Repr

section Kind

variable {K : Type*} [Field K] [LinearOrder K]

/-- [definition] The kind of a site with trace face `a` and determinant face `q`: the sign of `q`,
then the sign of the discriminant `a² − 4q`. -/
def siteKind (a q : K) : Kind :=
  if q < 0 then .reflection else if q = 0 then .degenerate
  else if a ^ 2 < 4 * q then .rotation else if a ^ 2 = 4 * q then .null else .boost

theorem siteKind_of_neg {a q : K} (hq : q < 0) : siteKind a q = .reflection := by
  simp [siteKind, hq]

theorem siteKind_of_zero (a : K) : siteKind a (0 : K) = .degenerate := by
  simp [siteKind]

theorem siteKind_of_pos {a q : K} (hq : 0 < q) :
    siteKind a q =
      if a ^ 2 < 4 * q then .rotation else if a ^ 2 = 4 * q then .null else .boost := by
  simp [siteKind, not_lt.mpr hq.le, hq.ne']

theorem siteKind_eq_reflection_iff (a q : K) : siteKind a q = .reflection ↔ q < 0 := by
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · simp [siteKind_of_neg hq, hq]
  · simp [siteKind_of_zero]
  · rw [siteKind_of_pos hq]
    simp only [not_lt.mpr hq.le, iff_false]
    split_ifs <;> simp

theorem siteKind_eq_degenerate_iff (a q : K) : siteKind a q = .degenerate ↔ q = 0 := by
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · simp [siteKind_of_neg hq, hq.ne]
  · simp [siteKind_of_zero]
  · rw [siteKind_of_pos hq]
    simp only [hq.ne', iff_false]
    split_ifs <;> simp

theorem siteKind_eq_rotation_iff [IsStrictOrderedRing K] (a q : K) :
    siteKind a q = .rotation ↔ a ^ 2 < 4 * q := by
  have ha : 0 ≤ a ^ 2 := sq_nonneg a
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · simp only [siteKind_of_neg hq, reduceCtorEq, false_iff, not_lt]
    linarith
  · simp only [siteKind_of_zero, reduceCtorEq, false_iff, not_lt]
    linarith
  · rw [siteKind_of_pos hq]
    rcases lt_trichotomy (a ^ 2) (4 * q) with h | h | h
    · simp [h]
    · simp [h]
    · simp [not_lt.mpr h.le, h.ne']

theorem siteKind_eq_null_iff (a q : K) : siteKind a q = .null ↔ 0 < q ∧ a ^ 2 = 4 * q := by
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · simp only [siteKind_of_neg hq, reduceCtorEq, false_iff, not_and]
    exact fun h => absurd h (not_lt.mpr hq.le)
  · simp [siteKind_of_zero]
  · rw [siteKind_of_pos hq]
    rcases lt_trichotomy (a ^ 2) (4 * q) with h | h | h
    · simp [h, h.ne]
    · simp [h, hq]
    · simp [not_lt.mpr h.le, h.ne']

theorem siteKind_eq_boost_iff (a q : K) : siteKind a q = .boost ↔ 0 < q ∧ 4 * q < a ^ 2 := by
  rcases lt_trichotomy q 0 with hq | rfl | hq
  · simp only [siteKind_of_neg hq, reduceCtorEq, false_iff, not_and]
    exact fun h => absurd h (not_lt.mpr hq.le)
  · simp [siteKind_of_zero]
  · rw [siteKind_of_pos hq]
    rcases lt_trichotomy (a ^ 2) (4 * q) with h | h | h
    · simp [h, not_lt.mpr h.le]
    · simp [h]
    · simp [not_lt.mpr h.le, h.ne', h, hq]

/-- [proved-derived; formal-checked] The kind is even in the trace: `−M` (the site composed with
the half-turn `e^{iπ}`) has the kind of `M`. -/
theorem siteKind_neg (a q : K) : siteKind (-a) q = siteKind a q := by
  simp [siteKind]

/-- [proved-derived; formal-checked] **Rotation ⇔ the factor's binary form is definite.** -/
theorem rotation_iff_definite [IsStrictOrderedRing K] (a q : K) :
    a ^ 2 < 4 * q ↔ ∀ x y : K, (x ≠ 0 ∨ y ≠ 0) → 0 < x ^ 2 - a * x * y + q * y ^ 2 := by
  constructor
  · intro h x y hxy
    have hsq : x ^ 2 - a * x * y + q * y ^ 2 = (x - a * y / 2) ^ 2 + (q - a ^ 2 / 4) * y ^ 2 := by
      ring
    rw [hsq]
    rcases eq_or_ne y 0 with hy | hy
    · subst hy
      have hx : x ≠ 0 := hxy.resolve_right (by simp)
      simp only [mul_zero, zero_div, sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow, add_zero]
      positivity
    · have h1 : 0 < q - a ^ 2 / 4 := by linarith
      have h2 : 0 < y ^ 2 := by positivity
      nlinarith [sq_nonneg (x - a * y / 2)]
  · intro h
    have := h (a / 2) 1 (Or.inr one_ne_zero)
    nlinarith [this]

/-- [proved-derived; formal-checked] **The discriminant vanishes ⇔ the traceless part is
nilpotent.** -/
theorem disc_zero_iff_traceless_nilpotent [IsStrictOrderedRing K]
    (M : Matrix (Fin 2) (Fin 2) K) :
    M.trace ^ 2 = 4 * M.det ↔ (M - (M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) K)) ^ 2 = 0 := by
  rw [traceless_sq]
  constructor
  · intro h
    simp [discriminant, h]
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    simp [discriminant] at h00
    linarith

/-- [proved-derived; formal-checked] **Null ⇔ a positive determinant and a nilpotent traceless
part.** -/
theorem null_iff_traceless_nilpotent [IsStrictOrderedRing K] (M : Matrix (Fin 2) (Fin 2) K) :
    siteKind M.trace M.det = .null ↔
      0 < M.det ∧ (M - (M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) K)) ^ 2 = 0 := by
  rw [siteKind_eq_null_iff, disc_zero_iff_traceless_nilpotent]

omit [LinearOrder K] in
/-- [proved-derived; formal-checked] A companion site's traceless part is never zero, so a null
companion is a shear (a nonzero nilpotent), never a scalar: the lock. -/
theorem companion_traceless_ne_zero (a q : K) :
    companion a q - (a / 2) • (1 : Matrix (Fin 2) (Fin 2) K) ≠ 0 := by
  intro h
  have h10 := congrFun (congrFun h 1) 0
  simp [companion] at h10

/-- [counterexample; formal-checked] The kind is a class function, not an action certificate: the
identity and the unipotent shear share their trace faces and are both null. -/
theorem identity_and_shear_are_both_null :
    siteKind identityTwo.trace identityTwo.det = .null ∧
      siteKind unipotentTwo.trace unipotentTwo.det = .null ∧ identityTwo ≠ unipotentTwo := by
  refine ⟨?_, ?_, ?_⟩
  · rw [siteKind_eq_null_iff]; simp [identityTwo]; norm_num
  · rw [siteKind_eq_null_iff]
    simp [unipotentTwo, Matrix.trace_fin_two, Matrix.det_fin_two]; norm_num
  · intro h
    have := congrFun (congrFun h 0) 1
    simp [identityTwo, unipotentTwo] at this

end Kind

/-! ### Rotation over the reals: no real root -/

/-- [proved-derived; formal-checked] **Rotation ⇔ the factor `1 − aT + qT²` has no real root**
(for `q > 0`). -/
theorem rotation_iff_no_real_root (a q : ℝ) (hq : 0 < q) :
    a ^ 2 < 4 * q ↔ ∀ T : ℝ, 1 - a * T + q * T ^ 2 ≠ 0 := by
  constructor
  · intro h T hT
    have := (rotation_iff_definite a q).mp h 1 T (Or.inl one_ne_zero)
    have e : (1 : ℝ) ^ 2 - a * 1 * T + q * T ^ 2 = 1 - a * T + q * T ^ 2 := by ring
    rw [e, hT] at this
    exact lt_irrefl 0 this
  · intro h
    by_contra hc
    have hc : 4 * q ≤ a ^ 2 := not_lt.mp hc
    have hd : 0 ≤ a ^ 2 - 4 * q := by linarith
    apply h ((a - Real.sqrt (a ^ 2 - 4 * q)) / (2 * q))
    have hs : Real.sqrt (a ^ 2 - 4 * q) * Real.sqrt (a ^ 2 - 4 * q) = a ^ 2 - 4 * q :=
      Real.mul_self_sqrt hd
    field_simp
    nlinarith [hs]

/-- [proved-derived; formal-checked] **A rotation site splits through the Weil root** of squared
modulus `q` (the placement face, `LocalFactor.theFactorSplitsThroughTheWeilRoot`). -/
theorem rotation_splits_through_weil_root (a q : ℤ)
    (h : siteKind (a : ℚ) (q : ℚ) = .rotation) (T : ℂ) :
    1 - (a : ℂ) * T + (q : ℂ) * T ^ 2
        = (1 - Holonics.Geometry.TraceSequence.alpha a q * T)
          * (1 - (starRingEnd ℂ) (Holonics.Geometry.TraceSequence.alpha a q) * T) ∧
      Complex.normSq (Holonics.Geometry.TraceSequence.alpha a q) = q := by
  rw [siteKind_eq_rotation_iff] at h
  have hz : a ^ 2 < 4 * q := by exact_mod_cast h
  have hr : (a : ℝ) ^ 2 ≤ 4 * (q : ℝ) := by exact_mod_cast hz.le
  exact ⟨theFactorSplitsThroughTheWeilRoot a q hr T,
    Holonics.Geometry.TraceSequence.theRootHasSquaredModulusQ a q hr⟩

/-! ### The kinds from the matrix -/

section CharacteristicPolynomial

variable {R : Type*} [CommRing R]

/-- [proved-derived; formal-checked] The characteristic polynomial of a two-state site:
`det(λ·1 − M) = λ² − (tr M)λ + det M`. -/
theorem det_sub_eq (M : Matrix (Fin 2) (Fin 2) R) (l : R) :
    (l • (1 : Matrix (Fin 2) (Fin 2) R) - M).det = l ^ 2 - M.trace * l + M.det := by
  simp [Matrix.det_fin_two, Matrix.trace_fin_two]
  ring

end CharacteristicPolynomial

/-- [proved-derived; formal-checked] **Rotation ⇔ no real eigenvalue.** -/
theorem rotation_iff_no_real_eigenvalue (M : Matrix (Fin 2) (Fin 2) ℝ) :
    siteKind M.trace M.det = .rotation ↔
      ∀ l : ℝ, (l • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det ≠ 0 := by
  rw [siteKind_eq_rotation_iff]
  simp only [det_sub_eq]
  constructor
  · intro h l hl
    nlinarith [sq_nonneg (l - M.trace / 2)]
  · intro h
    by_contra hc
    have hd : 0 ≤ M.trace ^ 2 - 4 * M.det := by linarith [not_lt.mp hc]
    have hs := Real.mul_self_sqrt hd
    apply h ((M.trace + Real.sqrt (M.trace ^ 2 - 4 * M.det)) / 2)
    linear_combination (1 / 4 : ℝ) * hs

/-- Two distinct real eigenvalues of a two-state site add to its trace and multiply to its
determinant. -/
theorem eigenvalues_sum_prod (M : Matrix (Fin 2) (Fin 2) ℝ) {l₁ l₂ : ℝ} (hne : l₁ ≠ l₂)
    (h₁ : (l₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det = 0)
    (h₂ : (l₂ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det = 0) :
    l₁ + l₂ = M.trace ∧ l₁ * l₂ = M.det := by
  rw [det_sub_eq] at h₁ h₂
  have hsub : (l₁ - l₂) * (l₁ + l₂ - M.trace) = 0 := by linear_combination h₁ - h₂
  have hsum : l₁ + l₂ = M.trace := by
    have := (mul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hne)
    linarith
  refine ⟨hsum, ?_⟩
  have : M.det = M.trace * l₁ - l₁ ^ 2 := by linarith
  rw [this, ← hsum]
  ring

/-- The two real roots of `λ² − aλ + q` when `a² − 4q ≥ 0`. -/
theorem real_eigenvalues (M : Matrix (Fin 2) (Fin 2) ℝ) (hd : 0 ≤ M.trace ^ 2 - 4 * M.det)
    (sign : ℝ) (hsign : sign = 1 ∨ sign = -1) :
    ((((M.trace + sign * Real.sqrt (M.trace ^ 2 - 4 * M.det)) / 2) •
      (1 : Matrix (Fin 2) (Fin 2) ℝ)) - M).det = 0 := by
  rw [det_sub_eq]
  have hs := Real.mul_self_sqrt hd
  have hsq : sign ^ 2 = 1 := by rcases hsign with rfl | rfl <;> norm_num
  linear_combination (sign ^ 2 / 4 : ℝ) * hs + (M.trace ^ 2 - 4 * M.det) / 4 * hsq

/-- [proved-derived; formal-checked] **Boost ⇔ two distinct real eigenvalues of one sign.** -/
theorem boost_iff_two_real_eigenvalues (M : Matrix (Fin 2) (Fin 2) ℝ) :
    siteKind M.trace M.det = .boost ↔
      ∃ l₁ l₂ : ℝ, l₁ ≠ l₂ ∧ 0 < l₁ * l₂ ∧
        (l₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det = 0 ∧
        (l₂ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det = 0 := by
  rw [siteKind_eq_boost_iff]
  constructor
  · rintro ⟨hq, hd⟩
    have hd' : 0 ≤ M.trace ^ 2 - 4 * M.det := by linarith
    have hspos : 0 < Real.sqrt (M.trace ^ 2 - 4 * M.det) := Real.sqrt_pos.mpr (by linarith)
    refine ⟨(M.trace + 1 * Real.sqrt (M.trace ^ 2 - 4 * M.det)) / 2,
      (M.trace + (-1) * Real.sqrt (M.trace ^ 2 - 4 * M.det)) / 2, ?_, ?_,
      real_eigenvalues M hd' 1 (Or.inl rfl), real_eigenvalues M hd' (-1) (Or.inr rfl)⟩
    · intro h
      linarith
    · have hs := Real.mul_self_sqrt hd'
      nlinarith
  · rintro ⟨l₁, l₂, hne, hpos, h₁, h₂⟩
    obtain ⟨hsum, hprod⟩ := eigenvalues_sum_prod M hne h₁ h₂
    refine ⟨hprod ▸ hpos, ?_⟩
    have : M.trace ^ 2 - 4 * M.det = (l₁ - l₂) ^ 2 := by rw [← hsum, ← hprod]; ring
    have : 0 < (l₁ - l₂) ^ 2 := by positivity [sub_ne_zero.mpr hne]
    linarith

/-- [proved-derived; formal-checked] **Reflection ⇔ real eigenvalues of opposite signs.** -/
theorem reflection_iff_opposite_eigenvalues (M : Matrix (Fin 2) (Fin 2) ℝ) :
    siteKind M.trace M.det = .reflection ↔
      ∃ l₁ l₂ : ℝ, l₁ < 0 ∧ 0 < l₂ ∧
        (l₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det = 0 ∧
        (l₂ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det = 0 := by
  rw [siteKind_eq_reflection_iff]
  constructor
  · intro hq
    have hd' : 0 ≤ M.trace ^ 2 - 4 * M.det := by nlinarith [sq_nonneg M.trace]
    have habs : |M.trace| < Real.sqrt (M.trace ^ 2 - 4 * M.det) := by
      rw [Real.lt_sqrt (abs_nonneg _), sq_abs]
      linarith
    refine ⟨(M.trace + (-1) * Real.sqrt (M.trace ^ 2 - 4 * M.det)) / 2,
      (M.trace + 1 * Real.sqrt (M.trace ^ 2 - 4 * M.det)) / 2, ?_, ?_,
      real_eigenvalues M hd' (-1) (Or.inr rfl), real_eigenvalues M hd' 1 (Or.inl rfl)⟩
    · have := le_abs_self M.trace
      linarith
    · have := neg_abs_le M.trace
      linarith
  · rintro ⟨l₁, l₂, h1, h2, e₁, e₂⟩
    obtain ⟨-, hprod⟩ := eigenvalues_sum_prod M (by linarith) e₁ e₂
    rw [← hprod]
    exact mul_neg_of_neg_of_pos h1 h2

/-- [proved-derived; formal-checked] **Degenerate ⇔ `0` is an eigenvalue.** -/
theorem degenerate_iff_zero_eigenvalue (M : Matrix (Fin 2) (Fin 2) ℝ) :
    siteKind M.trace M.det = .degenerate ↔
      ((0 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det = 0 := by
  rw [siteKind_eq_degenerate_iff, det_sub_eq]
  constructor <;> intro h <;> linarith

/-- [proved-derived; formal-checked] **The trichotomy from the matrix.** A site of positive
determinant has no real eigenvalue, or a nilpotent traceless part, or two distinct real eigenvalues
of one sign, and exactly one of these. -/
theorem site_trichotomy (M : Matrix (Fin 2) (Fin 2) ℝ) (hq : 0 < M.det) :
    let R := ∀ l : ℝ, (l • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det ≠ 0
    let N := (M - (M.trace / 2) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) ^ 2 = 0
    let B := ∃ l₁ l₂ : ℝ, l₁ ≠ l₂ ∧ 0 < l₁ * l₂ ∧
      (l₁ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det = 0 ∧
      (l₂ • (1 : Matrix (Fin 2) (Fin 2) ℝ) - M).det = 0
    (R ∨ N ∨ B) ∧ ¬ (R ∧ N) ∧ ¬ (R ∧ B) ∧ ¬ (N ∧ B) := by
  intro R N B
  have hR : R ↔ siteKind M.trace M.det = .rotation := (rotation_iff_no_real_eigenvalue M).symm
  have hN : N ↔ siteKind M.trace M.det = .null := by
    rw [null_iff_traceless_nilpotent]
    exact ⟨fun h => ⟨hq, h⟩, fun h => h.2⟩
  have hB : B ↔ siteKind M.trace M.det = .boost := (boost_iff_two_real_eigenvalues M).symm
  rw [hR, hN, hB]
  have hnr : siteKind M.trace M.det ≠ .reflection := by
    rw [Ne, siteKind_eq_reflection_iff]; linarith
  have hnd : siteKind M.trace M.det ≠ .degenerate := by
    rw [Ne, siteKind_eq_degenerate_iff]; exact hq.ne'
  cases h : siteKind M.trace M.det <;> simp_all

/-- [proved-derived; formal-checked] **The Lorentz factor of a site is projective**:
`γ² = tr²/(4 det)` is unchanged by rescaling the material, while `tr/2` is not. -/
theorem lorentz_factor_sq_smul {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K) {s : K}
    (hs : s ≠ 0) :
    (s • M).trace ^ 2 / (4 * (s • M).det) = M.trace ^ 2 / (4 * M.det) := by
  rw [Matrix.trace_smul, Matrix.det_smul, Fintype.card_fin, smul_eq_mul]
  by_cases hd : M.det = 0
  · simp [hd]
  · field_simp

/-- [counterexample; formal-checked] **The Swing is a reflection, not a boost.** `[[0,1],[1,0]]`
has `det = −1` and the real eigenvalues `−1 < 0 < 1`. -/
theorem swing_is_reflection :
    siteKind (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ).trace
      (!![0, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℚ).det = .reflection := by
  rw [siteKind_eq_reflection_iff]
  simp [Matrix.det_fin_two]

/-! ## 3. The boost: a Doppler ratio and its Lorentz faces -/

/-- [proved-derived; formal-checked] **A boost site of determinant one has a real Doppler ratio.**
With `det M = 1` and `tr M > 2` there is `k > 1` with `tr M = k + k⁻¹`, an eigenvalue of `M`
(`det(k·1 − M) = 0`), whose Lorentz faces `γ = tr/2` and `γβ = (k − k⁻¹)/2` satisfy
`γ² − (γβ)² = 1` and `(γβ)² = (tr² − 4)/4`. -/
theorem boost_doppler_ratio (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det = 1)
    (htr : 2 < M.trace) :
    ∃ k : ℝ, 1 < k ∧ M.trace = k + k⁻¹ ∧ ((k • (1 : Matrix (Fin 2) (Fin 2) ℝ)) - M).det = 0 ∧
      (M.trace / 2) ^ 2 - ((k - k⁻¹) / 2) ^ 2 = 1 ∧
      ((k - k⁻¹) / 2) ^ 2 = discriminant M.trace M.det / 4 := by
  have hq : 4 * (1 : ℝ) < M.trace ^ 2 := by nlinarith
  obtain ⟨x, hx, hx2⟩ :=
    Holonics.Geometry.TraceSequence.theOvershootProducesARealRootBeyondTheCircle M.trace 1 hq
      (by linarith)
  have hxpos : 0 < x := by nlinarith
  have hx1 : 1 < x := by nlinarith
  have hinv : x⁻¹ = M.trace - x := by
    have hx0 : x ≠ 0 := hxpos.ne'
    field_simp
    linarith
  refine ⟨x, hx1, by rw [hinv]; ring, ?_, ?_, ?_⟩
  · rw [Matrix.det_fin_two]
    have hd := hdet
    rw [Matrix.det_fin_two] at hd
    have ht : M.trace = M 0 0 + M 1 1 := Matrix.trace_fin_two M
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one,
      Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
      Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, zero_sub]
    rw [ht] at hx
    nlinarith [hx, hd]
  · rw [hinv]; ring_nf; nlinarith [hx]
  · rw [hinv, discriminant, hdet]; ring_nf; nlinarith [hx]

/-- [proved-derived; formal-checked] **A boost site is a Lorentz boost.** Its Doppler ratio `k`
supplies `CompositeMassEnergy.unitBoost` with `γ = tr/2` and `β = (k − k⁻¹)/(k + k⁻¹)`, and that
boost preserves the Lorentz norm of every four-momentum
(`multiplicativeScale_unitBoost_preserves_lorentzNorm`). -/
theorem boost_site_is_a_lorentz_boost (M : Matrix (Fin 2) (Fin 2) ℝ) (hdet : M.det = 1)
    (htr : 2 < M.trace) :
    ∃ k : ℝ, 1 < k ∧ M.trace / 2 = (k + k⁻¹) / 2 ∧
      ∀ P : Holonics.Physics.HolonicMassShellFace.FourMomentum,
        Holonics.Physics.HolonicMassShellFace.lorentzPairing 1
            (Holonics.Physics.CompositeMassEnergy.unitBoost ((k - k⁻¹) / (k + k⁻¹))
              (M.trace / 2) P)
            (Holonics.Physics.CompositeMassEnergy.unitBoost ((k - k⁻¹) / (k + k⁻¹))
              (M.trace / 2) P) =
          Holonics.Physics.HolonicMassShellFace.lorentzPairing 1 P P := by
  obtain ⟨k, hk, htk, -, -, -⟩ := boost_doppler_ratio M hdet htr
  refine ⟨k, hk, by rw [htk], fun P => ?_⟩
  rw [htk]
  exact Holonics.Physics.CompositeMassEnergy.multiplicativeScale_unitBoost_preserves_lorentzNorm
    k (by linarith) P

/-- [proved-derived; formal-checked] **The rational Doppler ratio `k = 3`.** The site
`companion (10/3) 1` is a boost with `γ = 5/3` and `β = (k − k⁻¹)/(k + k⁻¹) = 4/5`, the rational
boost of `CompositeMassEnergy.rational_boost_parameters`; no logarithm is evaluated. -/
theorem rational_doppler_three :
    siteKind (companion (10 / 3 : ℚ) 1).trace (companion (10 / 3 : ℚ) 1).det = .boost ∧
      (companion (10 / 3 : ℚ) 1).trace / 2 = 5 / 3 ∧
      ((3 : ℚ) + 3⁻¹) = 10 / 3 ∧ ((3 : ℚ) - 3⁻¹) / (3 + 3⁻¹) = 4 / 5 ∧
      ((5 / 3 : ℚ) ^ 2) * (1 - (4 / 5 : ℚ) ^ 2) = 1 := by
  obtain ⟨htr, hdet⟩ := theCompanionHasTraceAndDeterminant (10 / 3 : ℚ) 1
  rw [htr, hdet, siteKind_eq_boost_iff]
  norm_num

/-- [definition] The cat map of the two-clock torus. -/
def catMap : Matrix (Fin 2) (Fin 2) ℚ := !![2, 1; 1, 1]

/-- [counterexample; formal-checked] **The cat map is a boost whose Doppler ratio is not
rational.** `tr = 3`, `det = 1`, `γ = 3/2`, `(γβ)² = γ² − 1 = 5/4`, and no rational squares to
`5/4` (its ratio is `k = φ²`, a quadratic constraint identity). -/
theorem catMap_boost :
    catMap.trace = 3 ∧ catMap.det = 1 ∧ siteKind catMap.trace catMap.det = .boost ∧
      (catMap.trace / 2) ^ 2 - 1 = 5 / 4 ∧ ¬ ∃ r : ℚ, r ^ 2 = 5 / 4 := by
  have htr : catMap.trace = 3 := by simp [catMap, Matrix.trace_fin_two]; norm_num
  have hdet : catMap.det = 1 := by simp [catMap, Matrix.det_fin_two]; norm_num
  refine ⟨htr, hdet, ?_, ?_, ?_⟩
  · rw [htr, hdet, siteKind_eq_boost_iff]; norm_num
  · rw [htr]; norm_num
  · rintro ⟨r, hr⟩
    have h5q : (2 * r) ^ 2 = (5 : ℚ) := by linear_combination 4 * hr
    have h5 : ((2 * r : ℚ) : ℝ) ^ 2 = 5 := by exact_mod_cast h5q
    have hirr : Irrational (Real.sqrt 5) := by
      simpa using Nat.Prime.irrational_sqrt (p := 5) (by norm_num)
    apply hirr
    refine ⟨|2 * r|, ?_⟩
    rw [Rat.cast_abs, ← h5, Real.sqrt_sq_eq_abs]

/-! ## 4. Joined to the machine's trace faces -/

section Joined

variable {K : Type*} [Field K] [LinearOrder K]

/-- [proved-derived; formal-checked] **Phase carriage conserves the site kind**, since it
conserves the trace and the determinant (`NavigatorTraceFaces`). -/
theorem carried_site_kind (S P : (Matrix (Fin 2) (Fin 2) K)ˣ) (d : ℤ) :
    siteKind ((phaseTransport S P d : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K).trace
        ((phaseTransport S P d : (Matrix (Fin 2) (Fin 2) K)ˣ) : Matrix (Fin 2) (Fin 2) K).det
      = siteKind (P : Matrix (Fin 2) (Fin 2) K).trace (P : Matrix (Fin 2) (Fin 2) K).det := by
  have htr := carried_material_conserves_trace_sequence S P d 1
  simp only [pow_one] at htr
  rw [htr, carried_material_conserves_determinant]

/-- [proved-derived; formal-checked] A companion site has its factor's kind. -/
theorem companion_siteKind (a q : K) :
    siteKind (companion a q).trace (companion a q).det = siteKind a q := by
  obtain ⟨htr, hdet⟩ := theCompanionHasTraceAndDeterminant a q
  rw [htr, hdet]

end Joined

/-! ## 5. The kind is a face of the closed-word counts -/

section Counts

open Holonics.Geometry.TraceSequence

/-- [proved-derived; formal-checked] Reversing the trace reverses every odd count:
`t_n(−a, q) = (−1)ⁿ t_n(a, q)`. -/
theorem trace_neg (a q : ℤ) (n : ℕ) : trace (-a) q n = (-1) ^ n * trace a q n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    rw [trace_succ_succ, trace_succ_succ, ih1, ih2]
    ring

/-- [proved-derived; formal-checked] A boost of trace at least three has strictly growing closed-word
counts: `n + 2 ≤ t_n` and `t_n + 1 ≤ t_(n+1)`. -/
theorem boost_counts_grow_pos (a : ℤ) (ha : 3 ≤ a) (n : ℕ) :
    (n : ℤ) + 2 ≤ trace a 1 n ∧ trace a 1 n + 1 ≤ trace a 1 (n + 1) := by
  induction n with
  | zero => simp; omega
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨by push_cast; omega, ?_⟩
    rw [trace_succ_succ]
    nlinarith

/-- [proved-derived; formal-checked] **A boost's closed-word counts grow:** `4 < a²` gives
`n + 2 ≤ |t_n|` at determinant one. -/
theorem boost_counts_grow (a : ℤ) (ha : 4 < a ^ 2) (n : ℕ) : (n : ℤ) + 2 ≤ |trace a 1 n| := by
  rcases le_or_gt 3 a with h | h
  · have := (boost_counts_grow_pos a h n).1
    rw [abs_of_nonneg (by omega)]
    exact this
  · have ha' : 3 ≤ -a := by nlinarith
    have := (boost_counts_grow_pos (-a) ha' n).1
    have hneg : trace a 1 n = (-1) ^ n * trace (-a) 1 n := by
      rw [show a = -(-a) by ring, trace_neg, neg_neg]
    rw [hneg, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, abs_of_nonneg (by omega)]
    exact this

/-- [proved-derived; formal-checked] **Bounded closed-word counts ⇔ not a boost.** At determinant
one, `|t_n| ≤ 2` for every `n` exactly when `a² ≤ 4` (rotation or null). -/
theorem bounded_iff_not_boost (a : ℤ) : (∀ n, |trace a 1 n| ≤ 2) ↔ a ^ 2 ≤ 4 := by
  constructor
  · intro h
    by_contra hc
    have hc : 4 < a ^ 2 := not_le.mp hc
    have := boost_counts_grow a hc 1
    have := h 1
    push_cast at *
    omega
  · intro h n
    have hr : ((a : ℤ) : ℝ) ^ 2 ≤ 4 * ((1 : ℤ) : ℝ) := by push_cast; exact_mod_cast h
    have hb := theLevelOneBoundGivesEveryLevel a 1 hr n
    rw [Int.cast_one, one_pow, mul_one] at hb
    have hz : trace a 1 n ^ 2 ≤ 4 := by exact_mod_cast hb
    rw [abs_le]
    constructor <;> nlinarith

/-- [proved-derived; formal-checked] **The closed-word counts of a boost are Doppler powers:** with
`k + k⁻¹ = a`, `t_n = kⁿ + k⁻ⁿ`. -/
theorem boost_counts_are_doppler_powers (a : ℤ) (k : ℝ) (hk0 : k ≠ 0) (hk : k + k⁻¹ = a)
    (n : ℕ) : (trace a 1 n : ℝ) = k ^ n + k⁻¹ ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => norm_num
  | one => simp [hk]
  | more n ih1 ih2 =>
    rw [trace_succ_succ]
    push_cast
    rw [ih1, ih2, ← hk]
    have hkj : k * k⁻¹ = 1 := mul_inv_cancel₀ hk0
    linear_combination (k ^ n + k⁻¹ ^ n) * hkj

/-- [proved-derived; formal-checked] **The trace counts are sandwiched by Doppler powers:**
`kⁿ ≤ t_n ≤ 2kⁿ` for `k ≥ 1`. -/
theorem boost_counts_sandwich (a : ℤ) (k : ℝ) (hk1 : 1 ≤ k) (hk : k + k⁻¹ = a) (n : ℕ) :
    k ^ n ≤ (trace a 1 n : ℝ) ∧ (trace a 1 n : ℝ) ≤ 2 * k ^ n := by
  have hk0 : k ≠ 0 := by positivity
  rw [boost_counts_are_doppler_powers a k hk0 hk n]
  have hinv : k⁻¹ ^ n ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hk1)
  have hpow : 1 ≤ k ^ n := one_le_pow₀ hk1
  constructor
  · have : 0 ≤ k⁻¹ ^ n := by positivity
    linarith
  · linarith

/-- [proved-derived; formal-checked] **The growth rate of the counts is the rapidity:**
`(1/n) log t_n → log k` for `k ≥ 1` with `k + k⁻¹ = a`. -/
theorem boost_count_rate (a : ℤ) (k : ℝ) (hk1 : 1 ≤ k) (hk : k + k⁻¹ = a) :
    Filter.Tendsto (fun n : ℕ => Real.log (trace a 1 n) / n) Filter.atTop
      (nhds (Real.log k)) := by
  have hkpos : 0 < k := by linarith
  have hupper : Filter.Tendsto (fun n : ℕ => Real.log k + Real.log 2 / n) Filter.atTop
      (nhds (Real.log k)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).const_add (Real.log k)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨hlo, -⟩ := boost_counts_sandwich a k hk1 hk n
    have hlog : Real.log (k ^ n) ≤ Real.log (trace a 1 n) :=
      Real.log_le_log (by positivity) hlo
    rw [Real.log_pow] at hlog
    rw [le_div_iff₀ hn']
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    obtain ⟨hlo, hhi⟩ := boost_counts_sandwich a k hk1 hk n
    have hlog : Real.log (trace a 1 n) ≤ Real.log (2 * k ^ n) :=
      Real.log_le_log (lt_of_lt_of_le (by positivity) hlo) hhi
    rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow] at hlog
    rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
    linarith

/-- [proved-derived; formal-checked] Cayley–Hamilton for a two-state site: `tr(Mⁿ)` is the trace
recurrence of its faces. -/
theorem trace_pow_eq (M : Matrix (Fin 2) (Fin 2) ℤ) (n : ℕ) :
    (M ^ n).trace = trace M.trace M.det n := by
  have hch : M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℤ) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [sq, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two,
        Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Matrix.one_apply] <;>
      simp <;> ring
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp
  | more n ih1 ih2 =>
    rw [trace_succ_succ, ← ih1, ← ih2, show n + 2 = n + 2 from rfl, pow_add, hch, Matrix.mul_sub,
      Matrix.mul_smul, Matrix.mul_smul, Matrix.mul_one, ← pow_succ, Matrix.trace_sub,
      Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

/-- [proved-derived; formal-checked] **The torus reading.** For a determinant-one site,
`det(Mⁿ − 1) = 2 − t_n`; on the two-clock torus its absolute value is the classical count of
period-`n` points (the Lefschetz reading, not formalized here), not `t_n`. -/
theorem det_pow_sub_one (M : Matrix (Fin 2) (Fin 2) ℤ) (hdet : M.det = 1) (n : ℕ) :
    (M ^ n - 1).det = 2 - trace M.trace 1 n := by
  have hN : ∀ N : Matrix (Fin 2) (Fin 2) ℤ, (N - 1).det = N.det - N.trace + 1 := by
    intro N
    simp [Matrix.det_fin_two, Matrix.trace_fin_two]
    ring
  rw [hN, Matrix.det_pow, hdet, one_pow, trace_pow_eq, hdet]
  ring

/-- [proved-derived; formal-checked] **The torus count has the same rate:**
`(1/n) log |t_n − 2| → log k` for `k > 1` with `k + k⁻¹ = a`. -/
theorem torus_count_rate (a : ℤ) (k : ℝ) (hk1 : 1 < k) (hk : k + k⁻¹ = a) :
    Filter.Tendsto (fun n : ℕ => Real.log |(trace a 1 n : ℝ) - 2| / n) Filter.atTop
      (nhds (Real.log k)) := by
  have hkpos : 0 < k := by linarith
  have hk0 : k ≠ 0 := hkpos.ne'
  have hupper : Filter.Tendsto (fun n : ℕ => Real.log k + Real.log 2 / n) Filter.atTop
      (nhds (Real.log k)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).const_add (Real.log k)
  have hlower : Filter.Tendsto (fun n : ℕ => Real.log k - Real.log 2 / n) Filter.atTop
      (nhds (Real.log k)) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).const_sub (Real.log k)
  have hbig : ∀ᶠ n : ℕ in Filter.atTop, 4 ≤ k ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt hk1).eventually_ge_atTop 4
  have hform : ∀ n, (trace a 1 n : ℝ) - 2 = k ^ n + k⁻¹ ^ n - 2 := fun n => by
    rw [boost_counts_are_doppler_powers a k hk0 hk n]
  have hinv : ∀ n : ℕ, k⁻¹ ^ n ≤ 1 := fun n =>
    pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hk1.le)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · filter_upwards [Filter.eventually_ge_atTop 1, hbig] with n hn hkn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hge : k ^ n / 2 ≤ |(trace a 1 n : ℝ) - 2| := by
      rw [hform]
      have : 0 ≤ k⁻¹ ^ n := by positivity
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hlog := Real.log_le_log (by positivity) hge
    rw [Real.log_div (by positivity) two_ne_zero, Real.log_pow] at hlog
    rw [le_div_iff₀ hn', sub_mul, div_mul_cancel₀ _ hn'.ne']
    linarith
  · filter_upwards [Filter.eventually_ge_atTop 1, hbig] with n hn hkn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hpos : 0 < |(trace a 1 n : ℝ) - 2| := by
      rw [hform]
      have : 0 ≤ k⁻¹ ^ n := by positivity
      rw [abs_of_nonneg (by linarith)]
      linarith
    have hle : |(trace a 1 n : ℝ) - 2| ≤ 2 * k ^ n := by
      rw [hform]
      have : 0 ≤ k⁻¹ ^ n := by positivity
      rw [abs_of_nonneg (by linarith)]
      linarith [hinv n]
    have hlog := Real.log_le_log hpos hle
    rw [Real.log_mul two_ne_zero (by positivity), Real.log_pow] at hlog
    rw [div_le_iff₀ hn', add_mul, div_mul_cancel₀ _ hn'.ne']
    linarith

end Counts

/-! ## 6. Hasse sites are rotations -/

/-- [proved-derived; formal-checked] **A Hasse site is a rotation.** An integer trace `a` at a prime
determinant `p` within the Hasse interval `a² ≤ 4p` has `a² < 4p`: equality would make `p` a
square. -/
theorem hasse_site_is_rotation (p : ℕ) (hp : p.Prime) (a : ℤ) (h : a ^ 2 ≤ 4 * p) :
    siteKind (a : ℚ) (p : ℚ) = .rotation := by
  rw [siteKind_eq_rotation_iff]
  have hne : a ^ 2 ≠ 4 * (p : ℤ) := by
    intro heq
    have h2 : (2 : ℤ) ∣ a := by
      have : (2 : ℤ) ∣ a ^ 2 := ⟨2 * p, by rw [heq]; ring⟩
      exact Int.Prime.dvd_pow' (by norm_num) this
    obtain ⟨b, rfl⟩ := h2
    have hb : b ^ 2 = (p : ℤ) := by nlinarith
    have hbn : (b.natAbs) * (b.natAbs) = p := by
      have : ((b.natAbs * b.natAbs : ℕ) : ℤ) = (p : ℤ) := by
        push_cast
        rw [abs_mul_abs_self]
        linear_combination hb
      exact_mod_cast this
    have hb1 : b.natAbs ≠ 1 := by
      intro h1
      rw [h1] at hbn
      rw [← hbn] at hp
      exact Nat.not_prime_one hp
    exact Nat.not_prime_mul hb1 hb1 (hbn ▸ hp)
  have hlt : a ^ 2 < 4 * (p : ℤ) := lt_of_le_of_ne h hne
  exact_mod_cast hlt

section Audit
#print axioms traceless_sq
#print axioms rotation_iff_definite
#print axioms rotation_iff_no_real_root
#print axioms null_iff_traceless_nilpotent
#print axioms boost_doppler_ratio
#print axioms boost_site_is_a_lorentz_boost
#print axioms catMap_boost
#print axioms carried_site_kind
#print axioms bounded_iff_not_boost
#print axioms boost_counts_sandwich
#print axioms boost_count_rate
#print axioms trace_pow_eq
#print axioms det_pow_sub_one
#print axioms torus_count_rate
#print axioms rotation_iff_no_real_eigenvalue
#print axioms boost_iff_two_real_eigenvalues
#print axioms reflection_iff_opposite_eigenvalues
#print axioms degenerate_iff_zero_eigenvalue
#print axioms site_trichotomy
#print axioms lorentz_factor_sq_smul
#print axioms swing_is_reflection
#print axioms hasse_site_is_rotation
end Audit

end Holonics.Compression.Landmark.SiteKind
