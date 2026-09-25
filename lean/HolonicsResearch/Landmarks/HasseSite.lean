import HolonicsResearch.Millennium.GaussCoefficient
import HolonicsResearch.Millennium.FamilyWitness
import HolonicsResearch.Millennium.FiveTwist
import Holonics.Compression.Landmark.SiteKind

/-!
# Hasse sites: the literal point counts of the congruent-number curves are rotations

[definition] Rebuild step 3 (#145), the null-cone record §4. At a good prime `p` the local factor
of `E_n : y² = x³ − n²x` is the site `1 − a_p T + p T²` (`Millennium/LocalFactor.companion`), with
trace face `a_p = p − #E_n^aff(𝔽_p)`, the literal point count of
`Millennium/BirchSwinnertonDyer.traceOfFrobenius` computed over `ZMod p`, and determinant face `p`.
`Compression/Landmark/SiteKind.hasse_site_is_rotation` says a site with prime determinant inside
the Hasse interval is a rotation. This module supplies the Hasse interval from the tree's own point
counts, so the join is unconditional on this family.

[proved-derived; formal-checked] What is proved.

1. **Hasse's bound at `n = 1`** (`hasse_bound_one`): `a_p² ≤ 4p` for every odd prime. At
   `p ≡ 3 (mod 4)` the count is balanced, `a_p = 0` (`theCoefficientVanishesOnTheBlindFrames`). At
   `p ≡ 1 (mod 4)` the curve sum is the Jacobsthal sum `jac(−1) = χ(i)·jac(1)` with `i² = −1`
   (`GaussCoefficient.charSum_eq_jac`, `jac_mul_sq`), and the two-squares ledger
   `jac(1)² + jac(r)² = 4p` (`jac_sq_ledger`) bounds it.
2. **Hasse's bound on every twist** (`hasse_bound`): for `p ∤ 2n`, `a_p(E_n) = χ_p(n)·a_p(E_1)`
   (`FamilyWitness.theTraceTwistLawAtEveryModulus`) and `χ_p(n)² = 1`.
3. **The Hasse site is a rotation** (`congruent_site_is_rotation`): the site has positive determinant
   `p` and negative discriminant face `a_p² − 4p`, through `hasse_site_is_rotation`. Its factor
   splits through the Weil root `α` with `|α|² = p` (`congruent_factor_splits`), the Riemann
   hypothesis of the local factor.
4. **An instance on independent data** (`thirteen_site`): the kernel-computed point count
   `a₁₃(E₅) = −6` (`FiveTwist.theTwistInstanceAtThirteen`) gives the rotation `36 < 52` with Weil
   root `−3 + 2i`, `|α|² = 9 + 4 = 13`.

[counterexample; formal-checked] **Primality of the determinant is load-bearing.** At the square
determinant `q = 4 = 2²`, the traces `±4` sit exactly on the null cone, `(±4)² = 4·4`
(`hasse_boundary_at_square_determinant`): the Hasse interval's edge is reachable only when `q` is a
square, which is why `hasse_site_is_rotation` asks for a prime.

No `axiom`, no `sorry`.
-/

namespace Holonics.Landmarks.HasseSite

open Holonics.Millennium.BirchSwinnertonDyer
open Holonics.Millennium.GaussCoefficient
open Holonics.Compression.Landmark.SiteKind (discriminant)

variable {p : ℕ} [Fact p.Prime]

/-- [proved-derived; formal-checked] **Hasse's bound for `y² = x³ − x`** at every odd prime, from
the literal point count. -/
theorem hasse_bound_one (hp2 : p ≠ 2) : (traceOfFrobenius 1 p) ^ 2 ≤ 4 * (p : ℤ) := by
  have hodd : p % 2 = 1 := (Fact.out : p.Prime).eq_two_or_odd.resolve_left hp2
  have h14 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  rcases h14 with h1 | h3
  · have hchar : ringChar (ZMod p) ≠ 2 := by
      rw [ZMod.ringChar_zmod_n]
      exact hp2
    obtain ⟨i0, hi⟩ : IsSquare (-1 : ZMod p) := by
      rw [ZMod.exists_sq_eq_neg_one_iff]
      omega
    have hi0 : i0 ≠ 0 := by
      intro h
      rw [h, mul_zero] at hi
      exact one_ne_zero (neg_eq_zero.mp hi)
    have hjac : jac p (-1) = quadraticChar (ZMod p) i0 * jac p 1 := by
      have h := jac_mul_sq hi0 (1 : ZMod p)
      rwa [mul_one, sq, ← hi] at h
    obtain ⟨r, hrns⟩ := FiniteField.exists_nonsquare (F := ZMod p) hchar
    have hr : quadraticChar (ZMod p) r = -1 := quadraticChar_neg_one_iff_not_isSquare.mpr hrns
    have hled := jac_sq_ledger hp2 h1 hr
    have hsq : quadraticChar (ZMod p) i0 ^ 2 = 1 := quadraticChar_sq_one hi0
    rw [trace_eq_neg_charSum hp2, charSum_eq_jac, hjac]
    have : (-(quadraticChar (ZMod p) i0 * jac p 1)) ^ 2 = jac p 1 ^ 2 := by
      rw [neg_sq, mul_pow, hsq, one_mul]
    rw [this]
    nlinarith [sq_nonneg (jac p r)]
  · rw [theCoefficientVanishesOnTheBlindFrames 1 p h3]
    positivity

/-- [proved-derived; formal-checked] **Hasse's bound on every twist**: `a_p(E_n)² ≤ 4p` for every
odd prime `p ∤ n`. -/
theorem hasse_bound (n : ℕ) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) :
    (traceOfFrobenius n p) ^ 2 ≤ 4 * (p : ℤ) := by
  have hn0 : ((n : ℕ) : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact hpn
  rw [Holonics.Millennium.FamilyWitness.theTraceTwistLawAtEveryModulus n hp2 hpn, mul_pow,
    quadraticChar_sq_one hn0, one_mul]
  exact hasse_bound_one hp2

/-- [proved-derived; formal-checked] **The local site of a congruent-number curve is a rotation**:
positive determinant `p` and negative discriminant face, through
`SiteKind.hasse_site_is_rotation`. -/
theorem congruent_site_is_rotation (n : ℕ) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) :
    0 < (p : ℚ) ∧ discriminant ((traceOfFrobenius n p : ℤ) : ℚ) (p : ℚ) < 0 := by
  refine ⟨by exact_mod_cast (Fact.out : p.Prime).pos, ?_⟩
  have h := Holonics.Compression.Landmark.SiteKind.hasse_site_is_rotation p Fact.out _
    (hasse_bound n hp2 hpn)
  rw [Holonics.Compression.Landmark.SiteKind.siteKind_eq_rotation_iff] at h
  rw [discriminant]
  linarith

/-- [proved-derived; formal-checked] **The factor splits through the Weil root**:
`1 − a_p T + p T² = (1 − αT)(1 − ᾱT)` with `|α|² = p`. -/
theorem congruent_factor_splits (n : ℕ) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) (T : ℂ) :
    1 - ((traceOfFrobenius n p : ℤ) : ℂ) * T + ((p : ℤ) : ℂ) * T ^ 2
        = (1 - Holonics.Millennium.TraceSequence.alpha (traceOfFrobenius n p) p * T)
          * (1 - (starRingEnd ℂ) (Holonics.Millennium.TraceSequence.alpha
              (traceOfFrobenius n p) p) * T) ∧
      Complex.normSq (Holonics.Millennium.TraceSequence.alpha (traceOfFrobenius n p) p) = p := by
  have hb : ((traceOfFrobenius n p : ℤ) : ℝ) ^ 2 ≤ 4 * (((p : ℤ)) : ℝ) := by
    exact_mod_cast hasse_bound n hp2 hpn
  exact ⟨Holonics.Millennium.LocalFactor.theFactorSplitsThroughTheWeilRoot _ _ hb T,
    Holonics.Millennium.TraceSequence.theRootHasSquaredModulusQ _ _ hb⟩

/-- [proved-derived; formal-checked] **The thirteen instance**: the kernel-computed count
`a₁₃(E₅) = −6` is a rotation site, `36 < 52`, whose Weil root is `−3 + 2i`, of squared modulus
`13`. -/
theorem thirteen_site :
    traceOfFrobenius 5 13 = -6 ∧ discriminant ((-6 : ℤ) : ℚ) ((13 : ℕ) : ℚ) = -16 ∧
      Holonics.Millennium.TraceSequence.alpha (-6) 13 = ⟨-3, 2⟩ ∧
      Complex.normSq ⟨-3, 2⟩ = 13 := by
  refine ⟨Holonics.Millennium.FiveTwist.theTwistInstanceAtThirteen, by
    rw [discriminant]; norm_num, ?_, by simp [Complex.normSq]; norm_num⟩
  unfold Holonics.Millennium.TraceSequence.alpha
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  apply Complex.ext
  · simp
    norm_num
  · simp only
    push_cast
    rw [show 4 * (13 : ℝ) - (-6) ^ 2 = 16 by norm_num, h16]
    norm_num

/-- [counterexample; formal-checked] **At a square determinant the Hasse edge is reached**: the
traces `±4` at `q = 4` sit on the null cone. -/
theorem hasse_boundary_at_square_determinant :
    discriminant (4 : ℚ) 4 = 0 ∧ discriminant (-4 : ℚ) 4 = 0 ∧ ¬ (4 : ℕ).Prime := by
  refine ⟨by rw [discriminant]; norm_num, by rw [discriminant]; norm_num, by norm_num⟩

section Audit
#print axioms hasse_bound_one
#print axioms hasse_bound
#print axioms congruent_site_is_rotation
#print axioms congruent_factor_splits
#print axioms thirteen_site
#print axioms hasse_boundary_at_square_determinant
end Audit

end Holonics.Landmarks.HasseSite
