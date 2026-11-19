import Holonics.Foundation.FractalString
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The Cantor string's tube: dimension `log 2/log 3`, and a content that oscillates with period `log 3`

[definition] Source: #410's box "Fractal strings: Lapidus–Pomerance (1993) and Lapidus–Maier (1995) (Minkowski
content, spectral counting, Tauberian machinery, inverse counterexample at ½); Herichi–Lapidus weighted shift;
Makarov (1985); Cantor-complement gaps of `Foundation/FractalPacking`". This module takes the part that is finite and
checkable on the one string the tree holds: the Cantor string's tube volume and its Minkowski content. The owner it
extends is `Foundation/FractalString`, whose paragraph "The Cantor string" supplies the holes (`cantorGap`, `2^n`
of them of length `3^(−(n+1))` at depth `n`: `cantor_gap_length`, `cantor_depth_gaps`, from
`FractalPacking.length_words`), the Moran dimension `D = log 2/log 3` (`cantor_moran_dimension`,
`cantor_dimension_mem`) and the complex dimensions `D + 2πik/log 3` (`cantor_complex_dimensions`). The record
`2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS`
states Lapidus–Pomerance's direct theorem for a Minkowski measurable string and, as standard, that lattice ratios give
persistent oscillation while nonlattice ratios give Minkowski measurability (Lapidus–van Frankenhuijsen, *Fractal
Geometry, Complex Dimensions and Zeta Functions*, 2nd ed., Springer 2013, Ch. 8). Atlas rows read:
`fractal.cantor-gap-zeta` (its scope line: the exhaustion of the Cantor complement is not proved),
`fractal.self-similar-zeta`, `fractal.string-counts`, `fractal.minkowski-spectral-asymptotic` (the direct theorem,
which assumes measurability) and `rh.inverse-spectral-fractal-string`. The Cantor string is the lattice string the
tree holds, and here its tube volume is read directly: the content does not exist, because the normalized tube volume
oscillates with the period `log 3` of the complex dimensions.

What is proved. Throughout, `D = cantorDim = log 2/log 3`, and the tube is read at the scales `0 < ε ≤ ½`.

1. [proved-standard; formal-checked] **The tube of one hole** (`volume_hole_tube`): the Lebesgue measure of
   `{x ∈ (a, b) : x − a < ε ∨ b − x < ε}` is `min(2ε, b − a)`, the term the string's tube volume sums.
2. [definition] **The tube volume of a string** (`tubeVolume`): `V(ε) = Σ_j min(2ε, ℓ_j)`, a `tsum`, summable for a
   summable family of nonnegative lengths (`summable_tube`). [proved-standard; formal-checked] Only finitely many holes
   are at least `2ε` long (`finite_long_holes`), and the tube splits at the scale (`tubeVolume_split`):
   `V(ε) = 2ε·N(ε) + Σ_(ℓ_j < 2ε) ℓ_j`, with `N(ε)` the owner's `geometricCount` at `x = 1/(2ε)` on the finite
   family of those holes.
3. [proved-derived; formal-checked] **The Cantor string by depth with multiplicity** (`cantorLength`,
   `cantorString`, `cantorTube`): the family on `Σ n, Fin 2^n` with `⟨n, i⟩ ↦ 3^(−(n+1))`. Its depth-`n` holes are
   the holes of `FractalPacking`'s words of length `n`, as lists (`cantorString_depth`, from `cantor_depth_gaps`),
   with the same tube at each depth (`cantor_depth_tube`); its total length is one (`summable_cantor_mass`,
   `cantor_total_length`, `summable_cantorString`), and its tube volume is the depth series
   `V(ε) = Σ_n 2^n min(2ε, 3^(−(n+1)))` (`summable_cantorTube`, `cantorString_fibre`, `tubeVolume_cantorString`).
4. [proved-standard; formal-checked] **The tube on each band** (`cantorTube_band`, `exists_band`): for
   `3^(−(m+1)) < 2ε ≤ 3^(−m)`, `V(ε) = 2ε(2^m − 1) + (2/3)^m`, and every `ε ∈ (0, ½]` lies on a band. There the
   long holes are the depths below `m`, `N(ε) = 2^m − 1` of them (`cantorLongHoles`, `mem_cantorLongHoles`,
   `cantor_geometricCount_band`, `cantorTube_band_split`). **Self-similarity** (`cantorTube_third`):
   `V(ε/3) = (2/3)(V(ε) + ε)`, read off the series by setting its first hole aside.
5. [proved-standard; formal-checked] **Minkowski dimension `D`** (`cantorTube_bounds`,
   `tendsto_log_cantorTube_div_log`): `ε^(1−D) ≤ V(ε) ≤ 2^(2−D)·ε^(1−D)`, hence `log V(ε)/log ε → 1 − D` as
   `ε → 0⁺`; with `3^D = 2` (`three_rpow_cantorDim`) and `3^(1−D) = 3/2` (`three_rpow_one_sub_cantorDim`).
6. [proved-standard; formal-checked] **The content oscillates** (`normalizedTube`, `normalizedTube_third`,
   `normalizedTube_band`, `tendsto_normalizedTube_half_third_pow`, `tendsto_normalizedTube_quarter_third_pow`,
   `quarter_limit_lt_half_limit`, `normalizedTube_not_tendsto`). Write `f(ε) = ε^(D−1)·V(ε)`. Then
   `f(ε/3) = f(ε) + ε^D`; on a band, `f(c·3^(−m)/2) = ((c + 1) − c·2^(−m))·(2/c)^(1−D)` for `c ∈ (1/3, 1]`; along
   `ε_m = 3^(−m)/2`, `f → 2^(2−D)`, and along `ε′_m = 3^(−m)/4`, `f → (3/2)·4^(1−D)`, which is smaller, so `f` has
   no limit at `0⁺`. The inequality `(3/2)·4^(1−D) < 2^(2−D)` is `2^(1−D) < 4/3`, that is `2^D > 3/2`, that is
   `D² + D > 1`, which holds because `D > 5/8`, read from `2^8 = 256 > 243 = 3^5` (`cantorDim_gt_five_eighths`,
   `cantorDim_sq_add_gt_one`, `two_rpow_one_sub_cantorDim_lt`). The margin is narrow: `D² + D > 1` is
   `D > (√5 − 1)/2`, which reads `0.618` at three digits, against `D`, which reads `0.631`.
7. [proved-standard; formal-checked] **The upper and lower contents** (`bandProfile`, `bandProfile_eq`,
   `bandProfile_le`, `profile_ge`, `bandProfile_ge`, `isGreatest_bandProfile`, `isLeast_bandProfile`,
   `normalizedTube_band_le`, `bandProfile_sub_le_normalizedTube_band`, `limsup_normalizedTube`,
   `liminf_normalizedTube`). With `g(c) = (1 + c)(2/c)^(1−D)`, the largest value of `g` on `[1/3, 1]` is
   `2^(2−D) = g(1) = g(1/3)` (Bernoulli's inequality in the log chart `c = 3^(−t)`), its least value is
   `g((1 − D)/D)` (the weighted arithmetic–geometric mean inequality), and these are the `limsup` and the `liminf` of
   `f` at `0⁺`: the upper Minkowski content reads `2.583` and the lower `2.495` at three decimals.
8. [proved-derived; formal-checked] **The correction along the orbit** (`normalizedTube_third_pow`,
   `correction_eq`, `normalizedTube_third_pow_sub_le`): `f(ε·3^(−k)) = f(ε) + Σ_(i<k) (ε·3^(−i))^D
   = f(ε) + 2(1 − 2^(−k))·ε^D`, so `0 ≤ f(ε·3^(−k)) − f(ε) ≤ ε^D/(1 − 2^(−1))`.

**The period is the reciprocal spacing of the complex dimensions.** In the log chart `t = −log ε`,
`normalizedTube_third` reads `f(t + log 3) = f(t) + e^(−Dt)`: `f` is periodic of period `log 3` up to a correction
whose sum along the orbit is at most `2ε^D` (`normalizedTube_third_pow_sub_le`). A function of period `log 3` in `t`
carries the frequencies `2πk/log 3`, `k ∈ ℤ`, which are the imaginary parts of the complex dimensions
`D + 2πik/log 3` of `cantor_complex_dimensions`; their spacing is `2π/log 3`, and the period is `2π` over that
spacing, `log 3 = 2π/(2π/log 3)`. The real part `D` is the exponent that normalizes the tube, `V(ε) ≍ ε^(1−D)`
(`cantorTube_bounds`), and the rotation part is what `f` keeps: the upper and lower contents differ.

What is not claimed.
- Lapidus–Pomerance's direct spectral theorem `N_ν(x) = |Ω|x − c_D·M·x^D + o(x^D)` and its Tauberian machinery
  (atlas `fractal.minkowski-spectral-asymptotic`), and their criterion that a string is Minkowski measurable if and
  only if `ℓ_j ∼ L·j^(−1/D)`.
- The measurability of nonlattice self-similar strings (renewal theory; the owner's golden string,
  `goldenStringZeta_eq`) and the lattice criterion for general self-similar strings: only the Cantor string is read.
- Lapidus–Maier's inverse spectral problem `(ISP)_D` and its failure at `½` (atlas
  `rh.inverse-spectral-fractal-string`), Herichi–Lapidus's weighted shift and spectral operator, and Makarov's
  theorem (1985). They stay owed in the box.
- The tube volume is the string's formula `Σ_j min(2ε, ℓ_j)`. That it is the Lebesgue measure of the inner
  `ε`-neighbourhood of the boundary of the Cantor set's complement in `[0, 1]` needs the holes placed as disjoint open
  intervals that exhaust that complement (the scope line of `fractal.cantor-gap-zeta`) and countable additivity over
  them; only the one-hole law (`volume_hole_tube`) is proved.
- The explicit tube formula, with the residues at the complex dimensions as the Fourier coefficients of `f`'s
  periodic part, and the closed form `g((1 − D)/D) = 2^(1−D)·D^(−D)·(1 − D)^(D−1)` of the lower content.
- The Minkowski dimension is read here as `1 − lim log V(ε)/log ε`; its definition through the upper and lower
  contents taken in every exponent is not built.

**Computational object.** The helical pair interaction, read on the holes: each hole is the gap a pair of sibling
cells leaves at the restriction that produces them, and a receiver at grain `ε` reads a hole as `min(2ε, ℓ)`, its two
boundary layers where the hole is wider than `2ε` and the whole hole where it is not. Of the winding guide's six
objects: the helix (in the log chart the scale `ε = c·3^(−m)/2` is a whole winding `m` and a phase `c ∈ (1/3, 1]`,
and `f` returns to its value at the same phase one winding down, up to the correction `ε^D`), faces and placement
(the normalized tube `f` is a face read at the receiver's grain, and a complex dimension is a dilation exponent `D`
with a rotation of period `2π/log 3`), and the tower thread (the self-similar restriction of `FractalPacking`, one
level per hand, gives `V(ε/3) = (2/3)(V(ε) + ε)`). The pair beyond the sibling gap, the cell holonomy and the tube
stay attached; the Minkowski tube, a neighbourhood of a boundary, is not the guide's tube (a transfer between
cross-section charts) and uses none of it.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.FractalStringTube

open Filter Topology
open Holonics.Foundation.FractalString Holonics.Foundation.FractalPacking

/-! ## The tube of one hole -/

section Hole

/-- [proved-standard; formal-checked] **One hole's tube**: points of `(a, b)` within `ε` of an end: `min(2ε, b − a)`. -/
theorem volume_hole_tube {a b ε : ℝ} (hε : 0 < ε) :
    MeasureTheory.volume {x ∈ Set.Ioo a b | x - a < ε ∨ b - x < ε} =
      ENNReal.ofReal (min (2 * ε) (b - a)) := by
  rcases le_or_gt (2 * ε) (b - a) with h | h
  · have hset : {x ∈ Set.Ioo a b | x - a < ε ∨ b - x < ε} =
        Set.Ioo a (a + ε) ∪ Set.Ioo (b - ε) b := by
      ext x
      simp only [Set.mem_Ioo, Set.mem_union]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3 | h3⟩
        · exact Or.inl ⟨h1, by linarith⟩
        · exact Or.inr ⟨by linarith, h2⟩
      · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
        · exact ⟨⟨h1, by linarith⟩, Or.inl (by linarith)⟩
        · exact ⟨⟨by linarith, h2⟩, Or.inr (by linarith)⟩
    have hdisj : Disjoint (Set.Ioo a (a + ε)) (Set.Ioo (b - ε) b) := by
      rw [Set.disjoint_left]
      intro x hx hx'
      simp only [Set.mem_Ioo] at hx hx'
      linarith
    rw [hset, MeasureTheory.measure_union hdisj measurableSet_Ioo, Real.volume_Ioo, Real.volume_Ioo,
      min_eq_left h, ← ENNReal.ofReal_add (by linarith) (by linarith)]
    congr 1
    ring
  · have hset : {x ∈ Set.Ioo a b | x - a < ε ∨ b - x < ε} = Set.Ioo a b := by
      ext x
      simp only [Set.mem_Ioo]
      constructor
      · exact fun hx => hx.1
      · intro hx
        refine ⟨hx, ?_⟩
        by_contra hc
        rw [not_or, not_lt, not_lt] at hc
        linarith [hc.1, hc.2]
    rw [hset, Real.volume_Ioo, min_eq_right h.le]

end Hole

/-! ## The tube volume of a string -/

section Strings

variable {ι : Type*}

/-- [definition] **The tube volume** of a string of lengths `ℓ`: `V(ε) = Σ_j min(2ε, ℓ_j)`. -/
noncomputable def tubeVolume (ℓ : ι → ℝ) (ε : ℝ) : ℝ :=
  ∑' j, min (2 * ε) (ℓ j)

/-- [proved-standard; formal-checked] The tube series of a summable string of nonnegative lengths is summable. -/
theorem summable_tube {ℓ : ι → ℝ} (hℓ : Summable ℓ) (h0 : ∀ j, 0 ≤ ℓ j) {ε : ℝ} (hε : 0 ≤ ε) :
    Summable fun j => min (2 * ε) (ℓ j) :=
  Summable.of_nonneg_of_le (fun j => le_min (by linarith) (h0 j)) (fun j => min_le_right _ _) hℓ

/-- [proved-standard; formal-checked] A summable string has finitely many holes of length at least `2ε`. -/
theorem finite_long_holes {ℓ : ι → ℝ} (hℓ : Summable ℓ) {ε : ℝ} (hε : 0 < ε) :
    {j | 2 * ε ≤ ℓ j}.Finite := by
  have h := hℓ.tendsto_cofinite_zero.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < 2 * ε))
  simpa only [not_lt] using Filter.eventually_cofinite.1 h

/-- [proved-standard; formal-checked] **The split at the scale**: `V(ε) = 2ε·N(ε) + Σ_(ℓ_j < 2ε) ℓ_j`. -/
theorem tubeVolume_split {ℓ : ι → ℝ} (hℓ : Summable ℓ) (h0 : ∀ j, 0 ≤ ℓ j) {ε : ℝ} (hε : 0 < ε)
    (J : Finset ι) (hJ : ∀ j, j ∈ J ↔ 2 * ε ≤ ℓ j) :
    tubeVolume ℓ ε =
      2 * ε * geometricCount J ℓ (1 / (2 * ε)) + ∑' j, {j | ℓ j < 2 * ε}.indicator ℓ j := by
  classical
  have hcount : geometricCount J ℓ (1 / (2 * ε)) = J.card := by
    unfold geometricCount
    rw [Finset.filter_true_of_mem]
    intro j hj
    rw [one_div, inv_mul_eq_div, one_le_div (by positivity)]
    exact (hJ j).1 hj
  have hpt : ∀ j, min (2 * ε) (ℓ j) =
      (if j ∈ J then 2 * ε else 0) + {j | ℓ j < 2 * ε}.indicator ℓ j := by
    intro j
    by_cases h : 2 * ε ≤ ℓ j
    · simp [(hJ j).2 h, min_eq_left h, Set.indicator, not_lt.2 h]
    · have h' : ℓ j < 2 * ε := lt_of_not_ge h
      have hj : j ∉ J := fun hj => h ((hJ j).1 hj)
      simp [hj, min_eq_right h'.le, Set.indicator, h']
  have hs1 : Summable fun j => if j ∈ J then 2 * ε else 0 :=
    summable_of_ne_finset_zero (s := J) (fun j hj => by simp [hj])
  have hs2 : Summable fun j => {j | ℓ j < 2 * ε}.indicator ℓ j :=
    Summable.of_nonneg_of_le (fun j => Set.indicator_nonneg (fun j _ => h0 j) j)
      (fun j => Set.indicator_le_self' (fun j _ => h0 j) j) hℓ
  unfold tubeVolume
  rw [tsum_congr hpt, hs1.tsum_add hs2, tsum_eq_sum (s := J) (fun j hj => by simp [hj]),
    Finset.sum_ite_of_true (fun j hj => hj), Finset.sum_const, nsmul_eq_mul, hcount]
  ring

end Strings

/-! ## The Cantor string by depth with multiplicity -/

section Cantor

/-- [definition] **The Cantor hole length at depth `n`**: `3^(−(n+1))`. -/
noncomputable def cantorLength (n : ℕ) : ℝ := (1 / 3 : ℝ) ^ (n + 1)

/-- [definition] **The Cantor string** indexed by depth with multiplicity: `⟨n, i⟩ ↦ 3^(−(n+1))`, `i < 2^n`. -/
noncomputable def cantorString : (Σ n : ℕ, Fin (2 ^ n)) → ℝ := fun p => cantorLength p.1

/-- [definition] **The Cantor string's tube volume** as its depth series `Σ_n 2^n min(2ε, 3^(−(n+1)))`. -/
noncomputable def cantorTube (ε : ℝ) : ℝ := ∑' n : ℕ, (2 : ℝ) ^ n * min (2 * ε) (cantorLength n)

/-- [proved-standard; formal-checked] Every Cantor hole has positive length. -/
theorem cantorLength_pos (n : ℕ) : 0 < cantorLength n := by
  unfold cantorLength
  positivity

/-- [proved-derived; formal-checked] The depth-`n` holes of `cantorString` are the words' (`cantor_depth_gaps`). -/
theorem cantorString_depth (n : ℕ) :
    List.ofFn (fun i : Fin (2 ^ n) => cantorString ⟨n, i⟩) =
      (words n).map fun w => (cantorGap w : ℝ) := by
  have h := congrArg (List.map (fun q : ℚ => (q : ℝ))) (cantor_depth_gaps n)
  rw [List.map_map, List.map_replicate] at h
  rw [show (fun w => (cantorGap w : ℝ)) = (fun q : ℚ => (q : ℝ)) ∘ cantorGap from rfl, h]
  simp only [cantorString, cantorLength, List.ofFn_const]
  push_cast
  rfl

/-- [proved-derived; formal-checked] The words' holes at depth `n` carry the tube `2^n min(2ε, 3^(−(n+1)))`. -/
theorem cantor_depth_tube (n : ℕ) (ε : ℝ) :
    ((words n).map fun w => min (2 * ε) (cantorGap w : ℝ)).sum =
      (2 : ℝ) ^ n * min (2 * ε) (cantorLength n) := by
  have h : ((words n).map fun w => min (2 * ε) (cantorGap w : ℝ)) =
      ((words n).map fun w => (cantorGap w : ℝ)).map fun x => min (2 * ε) x := by
    rw [List.map_map]
    rfl
  rw [h, ← cantorString_depth, List.map_ofFn, List.sum_ofFn]
  simp [cantorString, Finset.sum_const, nsmul_eq_mul]

/-- [proved-standard; formal-checked] The holes at depth `n` have total length `(1/3)(2/3)^n`. -/
theorem two_pow_mul_cantorLength (n : ℕ) :
    (2 : ℝ) ^ n * cantorLength n = (1 / 3) * (2 / 3 : ℝ) ^ n := by
  unfold cantorLength
  rw [pow_succ, div_pow, div_pow, one_pow]
  field_simp

/-- [proved-standard; formal-checked] The depth masses `2^n·3^(−(n+1))` are summable. -/
theorem summable_cantor_mass : Summable fun n : ℕ => (2 : ℝ) ^ n * cantorLength n := by
  simp_rw [two_pow_mul_cantorLength]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- [proved-standard; formal-checked] **The Cantor holes refill the unit**: their total length is one. -/
theorem cantor_total_length : ∑' n : ℕ, (2 : ℝ) ^ n * cantorLength n = 1 := by
  simp_rw [two_pow_mul_cantorLength]
  rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- [proved-standard; formal-checked] The Cantor tube series is summable for `ε ≥ 0`. -/
theorem summable_cantorTube {ε : ℝ} (hε : 0 ≤ ε) :
    Summable fun n : ℕ => (2 : ℝ) ^ n * min (2 * ε) (cantorLength n) :=
  Summable.of_nonneg_of_le (fun n => mul_nonneg (by positivity) (le_min (by linarith)
    (cantorLength_pos n).le)) (fun n => mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity))
    summable_cantor_mass

/-- [proved-derived; formal-checked] A function of the length summed over one depth is `2^n` times its value. -/
theorem cantorString_fibre (n : ℕ) (g : ℝ → ℝ) :
    ∑' i : Fin (2 ^ n), g (cantorString ⟨n, i⟩) = (2 : ℝ) ^ n * g (cantorLength n) := by
  simp [tsum_fintype, cantorString, Finset.sum_const, nsmul_eq_mul]

/-- [proved-derived; formal-checked] The Cantor string is a summable family of lengths. -/
theorem summable_cantorString : Summable cantorString := by
  refine (summable_sigma_of_nonneg (fun p => (cantorLength_pos p.1).le)).2
    ⟨fun n => (hasSum_fintype _).summable, ?_⟩
  simpa [cantorString_fibre _ id] using summable_cantor_mass

/-- [proved-derived; formal-checked] **The string's tube volume is the depth series** for the Cantor string. -/
theorem tubeVolume_cantorString {ε : ℝ} (hε : 0 ≤ ε) : tubeVolume cantorString ε = cantorTube ε := by
  have hs := summable_tube summable_cantorString (fun p => (cantorLength_pos p.1).le) hε
  unfold tubeVolume cantorTube
  rw [hs.tsum_sigma]
  exact tsum_congr fun n => cantorString_fibre n fun x => min (2 * ε) x

end Cantor

/-! ## The tube on each band, and self-similarity -/

section Bands

/-- [proved-standard; formal-checked] **Band `m`**: for `3^(−(m+1)) < 2ε ≤ 3^(−m)`, `V(ε) = 2ε(2^m − 1) + (2/3)^m`. -/
theorem cantorTube_band {m : ℕ} {ε : ℝ} (h1 : (1 / 3 : ℝ) ^ (m + 1) < 2 * ε)
    (h2 : 2 * ε ≤ (1 / 3 : ℝ) ^ m) :
    cantorTube ε = 2 * ε * (2 ^ m - 1) + (2 / 3 : ℝ) ^ m := by
  have hε : 0 ≤ ε := by
    have : (0 : ℝ) < (1 / 3) ^ (m + 1) := by positivity
    linarith
  unfold cantorTube
  rw [← (summable_cantorTube hε).sum_add_tsum_nat_add m]
  have hlow : ∀ i ∈ Finset.range m, (2 : ℝ) ^ i * min (2 * ε) (cantorLength i) = 2 * ε * 2 ^ i := by
    intro i hi
    have hi' : i + 1 ≤ m := Finset.mem_range.1 hi
    have : 2 * ε ≤ cantorLength i :=
      h2.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hi')
    rw [min_eq_left this]
    ring
  have hhigh : ∀ i : ℕ, (2 : ℝ) ^ (i + m) * min (2 * ε) (cantorLength (i + m)) =
      (2 / 3 : ℝ) ^ m * ((1 / 3) * (2 / 3 : ℝ) ^ i) := by
    intro i
    have : cantorLength (i + m) ≤ 2 * ε :=
      (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)).trans h1.le
    rw [min_eq_right this, two_pow_mul_cantorLength, pow_add]
    ring
  rw [Finset.sum_congr rfl hlow, ← Finset.mul_sum, geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1),
    tsum_congr hhigh, tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- [definition] **The long holes on band `m`**: the holes of depth below `m`. -/
def cantorLongHoles (m : ℕ) : Finset (Σ n : ℕ, Fin (2 ^ n)) :=
  (Finset.range m).sigma fun _ => Finset.univ

/-- [proved-standard; formal-checked] On band `m` a hole is at least `2ε` long iff its depth is below `m`. -/
theorem mem_cantorLongHoles {m : ℕ} {ε : ℝ} (h1 : (1 / 3 : ℝ) ^ (m + 1) < 2 * ε)
    (h2 : 2 * ε ≤ (1 / 3 : ℝ) ^ m) (p : Σ n : ℕ, Fin (2 ^ n)) :
    p ∈ cantorLongHoles m ↔ 2 * ε ≤ cantorString p := by
  simp only [cantorLongHoles, Finset.mem_sigma, Finset.mem_range, Finset.mem_univ, and_true,
    cantorString, cantorLength]
  constructor
  · intro hp
    exact h2.trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) hp)
  · intro hp
    by_contra hc
    have : (1 / 3 : ℝ) ^ (p.1 + 1) ≤ (1 / 3) ^ (m + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith

/-- [proved-standard; formal-checked] **The count on band `m`**: `N(ε) = 2^m − 1` holes are at least `2ε` long. -/
theorem cantor_geometricCount_band {m : ℕ} {ε : ℝ} (h1 : (1 / 3 : ℝ) ^ (m + 1) < 2 * ε)
    (h2 : 2 * ε ≤ (1 / 3 : ℝ) ^ m) :
    (geometricCount (cantorLongHoles m) cantorString (1 / (2 * ε)) : ℝ) = 2 ^ m - 1 := by
  have hε : 0 < 2 * ε := lt_of_le_of_lt (by positivity) h1
  unfold geometricCount
  rw [Finset.filter_true_of_mem fun p hp => by
    rw [one_div, inv_mul_eq_div, one_le_div hε]
    exact (mem_cantorLongHoles h1 h2 p).1 hp]
  rw [cantorLongHoles, Finset.card_sigma]
  simp only [Finset.card_univ, Fintype.card_fin]
  push_cast
  rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
  norm_num

/-- [proved-standard; formal-checked] On band `m` the split reads `V(ε) = 2ε·N(ε) + (2/3)^m`. -/
theorem cantorTube_band_split {m : ℕ} {ε : ℝ} (h1 : (1 / 3 : ℝ) ^ (m + 1) < 2 * ε)
    (h2 : 2 * ε ≤ (1 / 3 : ℝ) ^ m) :
    cantorTube ε = 2 * ε * geometricCount (cantorLongHoles m) cantorString (1 / (2 * ε)) +
      (2 / 3 : ℝ) ^ m := by
  rw [cantor_geometricCount_band h1 h2, cantorTube_band h1 h2]

/-- [proved-standard; formal-checked] Every scale `ε ∈ (0, ½]` lies on a band `3^(−(m+1)) < 2ε ≤ 3^(−m)`. -/
theorem exists_band {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    ∃ m : ℕ, (1 / 3 : ℝ) ^ (m + 1) < 2 * ε ∧ 2 * ε ≤ (1 / 3 : ℝ) ^ m := by
  obtain ⟨m, hm1, hm2⟩ := exists_nat_pow_near (x := 1 / (2 * ε)) (y := (3 : ℝ))
    (by rw [le_div_iff₀ (by positivity)]; linarith) (by norm_num)
  refine ⟨m, ?_, ?_⟩
  · rw [div_pow, one_pow, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hm2
    linarith
  · rw [div_pow, one_pow, le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at hm1
    linarith

/-- [proved-standard; formal-checked] **Self-similarity of the tube**: `V(ε/3) = (2/3)(V(ε) + ε)` on `(0, ½]`. -/
theorem cantorTube_third {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    cantorTube (ε / 3) = (2 / 3) * (cantorTube ε + ε) := by
  unfold cantorTube
  rw [(summable_cantorTube (by positivity : (0 : ℝ) ≤ ε / 3)).tsum_eq_zero_add]
  have h0 : (2 : ℝ) ^ 0 * min (2 * (ε / 3)) (cantorLength 0) = 2 * ε / 3 := by
    rw [min_eq_left (by unfold cantorLength; norm_num; linarith)]
    ring
  have hs : ∀ n : ℕ, (2 : ℝ) ^ (n + 1) * min (2 * (ε / 3)) (cantorLength (n + 1)) =
      (2 / 3) * ((2 : ℝ) ^ n * min (2 * ε) (cantorLength n)) := by
    intro n
    have : min (2 * (ε / 3)) (cantorLength (n + 1)) = min (2 * ε) (cantorLength n) / 3 := by
      rw [← min_div_div_right (by norm_num)]
      unfold cantorLength
      congr 1 <;> ring
    rw [this]
    ring
  rw [h0, tsum_congr hs, tsum_mul_left]
  ring

end Bands

/-! ## The dimension and the normalized tube -/

section Dimension

/-- [definition] **The Cantor dimension** `D = log 2/log 3`, the Moran dimension of `cantor_moran_dimension`. -/
noncomputable def cantorDim : ℝ := Real.log 2 / Real.log 3

/-- [proved-standard; formal-checked] `3^D = 2`. -/
theorem three_rpow_cantorDim : (3 : ℝ) ^ cantorDim = 2 :=
  Real.rpow_logb (by norm_num) (by norm_num) (by norm_num)

/-- [proved-standard; formal-checked] `½ < D < 1` (`cantor_dimension_mem`). -/
theorem cantorDim_mem : 1 / 2 < cantorDim ∧ cantorDim < 1 := cantor_dimension_mem

/-- [proved-standard; formal-checked] `D > 5/8`, read from `2^8 = 256 > 243 = 3^5`. -/
theorem cantorDim_gt_five_eighths : 5 / 8 < cantorDim := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h : 5 * Real.log 3 < 8 * Real.log 2 := by
    rw [show (5 : ℝ) * Real.log 3 = Real.log ((3 : ℝ) ^ 5) by rw [Real.log_pow]; norm_num,
      show (8 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ 8) by rw [Real.log_pow]; norm_num]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  unfold cantorDim
  rw [lt_div_iff₀ hl3]
  linarith

/-- [proved-standard; formal-checked] `D < 3/4`, read from `2^4 = 16 < 27 = 3^3`. -/
theorem cantorDim_lt_three_quarters : cantorDim < 3 / 4 := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have h : 4 * Real.log 2 < 3 * Real.log 3 := by
    rw [show (4 : ℝ) * Real.log 2 = Real.log ((2 : ℝ) ^ 4) by rw [Real.log_pow]; norm_num,
      show (3 : ℝ) * Real.log 3 = Real.log ((3 : ℝ) ^ 3) by rw [Real.log_pow]; norm_num]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  unfold cantorDim
  rw [div_lt_iff₀ hl3]
  linarith

/-- [proved-standard; formal-checked] `D² + D > 1`, from `D > 5/8`. -/
theorem cantorDim_sq_add_gt_one : 1 < cantorDim ^ 2 + cantorDim := by
  nlinarith [cantorDim_gt_five_eighths]

/-- [proved-standard; formal-checked] `3^(1−D) = 3/2`. -/
theorem three_rpow_one_sub_cantorDim : (3 : ℝ) ^ (1 - cantorDim) = 3 / 2 := by
  rw [Real.rpow_sub (by norm_num), Real.rpow_one, three_rpow_cantorDim]

/-- [proved-standard; formal-checked] `(1/3)^D = 1/2`. -/
theorem third_rpow_cantorDim : (1 / 3 : ℝ) ^ cantorDim = 1 / 2 := by
  rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, three_rpow_cantorDim]

/-- [proved-standard; formal-checked] `(1/3)^(D−1) = 3/2`. -/
theorem third_rpow_cantorDim_sub_one : (1 / 3 : ℝ) ^ (cantorDim - 1) = 3 / 2 := by
  rw [Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow, Real.rpow_sub_one (by norm_num),
    three_rpow_cantorDim]
  norm_num

/-- [definition] **The normalized tube** `f(ε) = ε^(D−1)·V(ε)`, whose limit at `0⁺` would be the content. -/
noncomputable def normalizedTube (ε : ℝ) : ℝ := ε ^ (cantorDim - 1) * cantorTube ε

/-- [proved-standard; formal-checked] **Log-periodicity up to a correction**: `f(ε/3) = f(ε) + ε^D` on `(0, ½]`. -/
theorem normalizedTube_third {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    normalizedTube (ε / 3) = normalizedTube ε + ε ^ cantorDim := by
  unfold normalizedTube
  rw [cantorTube_third hε hε', div_eq_mul_one_div ε 3, Real.mul_rpow hε.le (by norm_num),
    third_rpow_cantorDim_sub_one, Real.rpow_sub_one hε.ne']
  field_simp

/-- [proved-standard; formal-checked] **Band form**: `f(c·3^(−m)/2) = ((c + 1) − c·2^(−m))(2/c)^(1−D)`, `c ∈ (⅓, 1]`. -/
theorem normalizedTube_band {m : ℕ} {c : ℝ} (hc1 : 1 / 3 < c) (hc2 : c ≤ 1) :
    normalizedTube (c * (1 / 3 : ℝ) ^ m / 2) =
      ((c + 1) - c * (1 / 2 : ℝ) ^ m) * (2 / c) ^ (1 - cantorDim) := by
  have hc : 0 < c := by linarith
  have hb := cantorTube_band (m := m) (ε := c * (1 / 3 : ℝ) ^ m / 2)
    (by rw [pow_succ]; nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 3) m])
    (by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 1 / 3) m])
  have hpow : (c * (1 / 3 : ℝ) ^ m / 2) ^ (cantorDim - 1) =
      (2 / c) ^ (1 - cantorDim) * (3 / 2 : ℝ) ^ m := by
    rw [show c * (1 / 3 : ℝ) ^ m / 2 = c / 2 * (1 / 3 : ℝ) ^ m by ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast_mul (by norm_num),
      mul_comm (m : ℝ), Real.rpow_mul_natCast (by norm_num), third_rpow_cantorDim_sub_one,
      show (2 / c : ℝ) = (c / 2)⁻¹ by rw [inv_div], Real.inv_rpow (by positivity),
      ← Real.rpow_neg (by positivity), neg_sub]
  have e1 : (3 / 2 : ℝ) ^ m * (1 / 3) ^ m = (1 / 2) ^ m := by rw [← mul_pow]; norm_num
  have e2 : (3 / 2 : ℝ) ^ m * (2 / 3) ^ m = 1 := by rw [← mul_pow]; norm_num
  have e3 : (1 / 2 : ℝ) ^ m * 2 ^ m = 1 := by rw [← mul_pow]; norm_num
  unfold normalizedTube
  rw [hb, hpow]
  linear_combination (2 / c) ^ (1 - cantorDim) *
    ((c * 2 ^ m - c) * e1 + e2 + c * e3)

/-- [proved-standard; formal-checked] Every `ε ∈ (0, ½]` is `c·3^(−m)/2`: a winding `m` and a phase `c ∈ (1/3, 1]`. -/
theorem exists_band_form {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    ∃ m : ℕ, ∃ c : ℝ, 1 / 3 < c ∧ c ≤ 1 ∧ ε = c * (1 / 3 : ℝ) ^ m / 2 := by
  obtain ⟨m, h1, h2⟩ := exists_band hε hε'
  have hp : (0 : ℝ) < (1 / 3) ^ m := by positivity
  refine ⟨m, 2 * ε / (1 / 3) ^ m, ?_, ?_, ?_⟩
  · rw [lt_div_iff₀ hp]
    rw [pow_succ] at h1
    linarith
  · rw [div_le_one hp]
    exact h2
  · field_simp

/-- [proved-standard; formal-checked] `V(ε) = ε^(1−D)·f(ε)`. -/
theorem cantorTube_eq_rpow_mul {ε : ℝ} (hε : 0 < ε) :
    cantorTube ε = ε ^ (1 - cantorDim) * normalizedTube ε := by
  unfold normalizedTube
  rw [← mul_assoc, ← Real.rpow_add hε, show 1 - cantorDim + (cantorDim - 1) = 0 by ring,
    Real.rpow_zero, one_mul]

end Dimension

/-! ## The band profile: its largest and least values -/

section Profile

/-- [definition] **The band profile** `g(c) = (1 + c)(2/c)^(1−D)`, the limit of `f(c·3^(−m)/2)` as `m → ∞`. -/
noncomputable def bandProfile (c : ℝ) : ℝ := (1 + c) * (2 / c) ^ (1 - cantorDim)

/-- [proved-standard; formal-checked] `g(c) = 2^(1−D)·(c^(D−1) + c^D)` for `c > 0`. -/
theorem bandProfile_eq {c : ℝ} (hc : 0 < c) :
    bandProfile c = 2 ^ (1 - cantorDim) * (c ^ (cantorDim - 1) + c ^ cantorDim) := by
  unfold bandProfile
  rw [Real.div_rpow (by norm_num) hc.le, div_eq_mul_inv, ← Real.rpow_neg hc.le, neg_sub,
    Real.rpow_sub_one hc.ne']
  field_simp

/-- [proved-standard; formal-checked] `g(1) = 2^(2−D)`. -/
theorem bandProfile_one : bandProfile 1 = (2 : ℝ) ^ (2 - cantorDim) := by
  unfold bandProfile
  rw [show (2 : ℝ) - cantorDim = 1 + (1 - cantorDim) by ring, Real.rpow_add (by norm_num),
    Real.rpow_one]
  norm_num

/-- [proved-standard; formal-checked] `g(1/2) = (3/2)·4^(1−D)`. -/
theorem bandProfile_half : bandProfile (1 / 2) = (3 / 2) * (4 : ℝ) ^ (1 - cantorDim) := by
  unfold bandProfile
  norm_num

/-- [proved-standard; formal-checked] **The upper bound of the profile**: `g(c) ≤ 2^(2−D)` on `[1/3, 1]`. -/
theorem bandProfile_le {c : ℝ} (hc1 : 1 / 3 ≤ c) (hc2 : c ≤ 1) :
    bandProfile c ≤ (2 : ℝ) ^ (2 - cantorDim) := by
  have hc : 0 < c := by linarith
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  set t := -Real.log c / Real.log 3 with ht
  have hlogc : Real.log c = -t * Real.log 3 := by rw [ht]; field_simp
  have ht0 : 0 ≤ t := by
    rw [ht]
    exact div_nonneg (neg_nonneg.2 (Real.log_nonpos hc.le hc2)) hl3.le
  have ht1 : t ≤ 1 := by
    rw [ht, div_le_one hl3]
    have : Real.log (1 / 3) ≤ Real.log c := Real.log_le_log (by norm_num) hc1
    rw [one_div, Real.log_inv] at this
    linarith
  have hA : c ^ (cantorDim - 1) = (1 + 1 / 2 : ℝ) ^ t := by
    rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos (by norm_num), hlogc,
      show (1 + 1 / 2 : ℝ) = 3 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num)]
    unfold cantorDim
    congr 1
    field_simp
    ring
  have hB : c ^ cantorDim = (1 + -(1 / 2) : ℝ) ^ t := by
    rw [Real.rpow_def_of_pos hc, Real.rpow_def_of_pos (by norm_num), hlogc,
      show (1 + -(1 / 2) : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
    unfold cantorDim
    congr 1
    field_simp
  have hb1 := rpow_one_add_le_one_add_mul_self (s := 1 / 2) (by norm_num) ht0 ht1
  have hb2 := rpow_one_add_le_one_add_mul_self (s := -(1 / 2)) (by norm_num) ht0 ht1
  rw [bandProfile_eq hc, hA, hB, ← bandProfile_one, bandProfile_eq one_pos, Real.one_rpow,
    Real.one_rpow]
  have h2 : (0 : ℝ) < 2 ^ (1 - cantorDim) := by positivity
  nlinarith

/-- [proved-standard; formal-checked] For `0 < D < 1`, `(1 + c)c^(D−1)` is least at `c = (1 − D)/D` (weighted AM–GM). -/
theorem profile_ge {D : ℝ} (hD0 : 0 < D) (hD1 : D < 1) {c : ℝ} (hc : 0 < c) :
    (1 + (1 - D) / D) * ((1 - D) / D) ^ (D - 1) ≤ (1 + c) * c ^ (D - 1) := by
  set a := (1 - D) / D with ha
  have ha0 : 0 < a := div_pos (by linarith) hD0
  set u := c / a with hu
  have hu0 : 0 < u := div_pos hc ha0
  have hcu : c = a * u := by rw [hu]; field_simp
  have hamgm := Real.geom_mean_le_arith_mean2_weighted (w₁ := D) (w₂ := 1 - D)
    (p₁ := u ^ (D - 1)) (p₂ := u ^ D) hD0.le (by linarith) (by positivity) (by positivity)
    (by ring)
  rw [← Real.rpow_mul hu0.le, ← Real.rpow_mul hu0.le, ← Real.rpow_add hu0,
    show (D - 1) * D + D * (1 - D) = 0 by ring, Real.rpow_zero] at hamgm
  have huD : u * u ^ (D - 1) = u ^ D := by
    rw [Real.rpow_sub_one hu0.ne']
    field_simp
  have hpow : c ^ (D - 1) = a ^ (D - 1) * u ^ (D - 1) := by
    rw [hcu, Real.mul_rpow ha0.le hu0.le]
  have haD : D * (1 + a) = 1 := by rw [ha]; field_simp; ring
  have hap : 0 < a ^ (D - 1) := Real.rpow_pos_of_pos ha0 _
  rw [hpow, hcu]
  have key : 1 + a ≤ u ^ (D - 1) + a * u ^ D := by
    have h1 : D * (u ^ (D - 1) + a * u ^ D) = D * u ^ (D - 1) + (1 - D) * u ^ D := by
      rw [ha]; field_simp
    nlinarith
  have hexp : (1 + a * u) * (a ^ (D - 1) * u ^ (D - 1)) =
      a ^ (D - 1) * (u ^ (D - 1) + a * u ^ D) := by
    rw [← huD]
    ring
  rw [hexp, mul_comm (1 + a)]
  exact mul_le_mul_of_nonneg_left key hap.le

/-- [proved-standard; formal-checked] **The lower bound of the profile**: `g((1 − D)/D) ≤ g(c)` for `c > 0`. -/
theorem bandProfile_ge {c : ℝ} (hc : 0 < c) :
    bandProfile ((1 - cantorDim) / cantorDim) ≤ bandProfile c := by
  have hD := cantorDim_mem
  have hstar : 0 < (1 - cantorDim) / cantorDim := div_pos (by linarith) (by linarith)
  have hg := profile_ge (by linarith : 0 < cantorDim) hD.2 hc
  rw [bandProfile_eq hstar, bandProfile_eq hc]
  have e : ∀ x : ℝ, 0 < x →
      x ^ (cantorDim - 1) + x ^ cantorDim = (1 + x) * x ^ (cantorDim - 1) := by
    intro x hx
    rw [Real.rpow_sub_one hx.ne']
    field_simp
  rw [e _ hstar, e _ hc]
  exact mul_le_mul_of_nonneg_left hg (by positivity)

/-- [proved-standard; formal-checked] The point `(1 − D)/D` lies in `(1/3, 1]`. -/
theorem lowerProfilePoint_mem :
    1 / 3 < (1 - cantorDim) / cantorDim ∧ (1 - cantorDim) / cantorDim ≤ 1 := by
  have hD := cantorDim_mem
  have h34 := cantorDim_lt_three_quarters
  have hD0 : 0 < cantorDim := by linarith
  constructor
  · rw [lt_div_iff₀ hD0]
    linarith
  · rw [div_le_one hD0]
    linarith

/-- [proved-standard; formal-checked] **The largest value of `g` on `[1/3, 1]` is `2^(2−D)`**, reached at `c = 1`. -/
theorem isGreatest_bandProfile :
    IsGreatest (bandProfile '' Set.Icc (1 / 3) 1) ((2 : ℝ) ^ (2 - cantorDim)) :=
  ⟨⟨1, ⟨by norm_num, le_rfl⟩, bandProfile_one⟩, by
    rintro _ ⟨c, ⟨hc1, hc2⟩, rfl⟩
    exact bandProfile_le hc1 hc2⟩

/-- [proved-standard; formal-checked] **The least value of `g` on `[1/3, 1]` is `g((1 − D)/D)`**. -/
theorem isLeast_bandProfile :
    IsLeast (bandProfile '' Set.Icc (1 / 3) 1) (bandProfile ((1 - cantorDim) / cantorDim)) :=
  ⟨⟨_, ⟨lowerProfilePoint_mem.1.le, lowerProfilePoint_mem.2⟩, rfl⟩, by
    rintro _ ⟨c, ⟨hc1, -⟩, rfl⟩
    exact bandProfile_ge (by linarith)⟩

/-- [proved-standard; formal-checked] On a band, `f(c·3^(−m)/2) ≤ g(c)`. -/
theorem normalizedTube_band_le {m : ℕ} {c : ℝ} (hc1 : 1 / 3 < c) (hc2 : c ≤ 1) :
    normalizedTube (c * (1 / 3 : ℝ) ^ m / 2) ≤ bandProfile c := by
  rw [normalizedTube_band hc1 hc2, bandProfile, add_comm 1 c]
  have hc : 0 < c := by linarith
  have : 0 ≤ c * (1 / 2 : ℝ) ^ m := by positivity
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

/-- [proved-standard; formal-checked] On a band, `g(c) − 2·2^(−m) ≤ f(c·3^(−m)/2)`. -/
theorem bandProfile_sub_le_normalizedTube_band {m : ℕ} {c : ℝ} (hc1 : 1 / 3 < c) (hc2 : c ≤ 1) :
    bandProfile c - 2 * (1 / 2 : ℝ) ^ m ≤ normalizedTube (c * (1 / 3 : ℝ) ^ m / 2) := by
  have hc : 0 < c := by linarith
  have h2c : 1 ≤ 2 / c := by rw [le_div_iff₀ hc]; linarith
  have hr2 : (2 / c) ^ (1 - cantorDim) ≤ 2 / c := by
    calc (2 / c) ^ (1 - cantorDim) ≤ (2 / c) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le h2c (by linarith [cantorDim_mem.1])
      _ = 2 / c := Real.rpow_one _
  have hh : (0 : ℝ) ≤ (1 / 2) ^ m := by positivity
  have hprod : c * (1 / 2 : ℝ) ^ m * (2 / c) ^ (1 - cantorDim) ≤ 2 * (1 / 2) ^ m := by
    calc c * (1 / 2 : ℝ) ^ m * (2 / c) ^ (1 - cantorDim) ≤ c * (1 / 2) ^ m * (2 / c) :=
          mul_le_mul_of_nonneg_left hr2 (by positivity)
      _ = 2 * (1 / 2) ^ m := by field_simp
  rw [normalizedTube_band hc1 hc2, bandProfile, add_comm 1 c]
  nlinarith

end Profile

/-! ## Minkowski dimension `log 2/log 3` -/

section MinkowskiDimension

/-- [proved-standard; formal-checked] `f(ε) ≤ 2^(2−D)` on `(0, ½]`. -/
theorem normalizedTube_le {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    normalizedTube ε ≤ (2 : ℝ) ^ (2 - cantorDim) := by
  obtain ⟨m, c, hc1, hc2, rfl⟩ := exists_band_form hε hε'
  exact (normalizedTube_band_le hc1 hc2).trans (bandProfile_le hc1.le hc2)

/-- [proved-standard; formal-checked] `1 ≤ f(ε) ≤ 2^(2−D)` on `(0, ½]`. -/
theorem normalizedTube_bounds {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    1 ≤ normalizedTube ε ∧ normalizedTube ε ≤ (2 : ℝ) ^ (2 - cantorDim) := by
  refine ⟨?_, normalizedTube_le hε hε'⟩
  obtain ⟨m, c, hc1, hc2, rfl⟩ := exists_band_form hε hε'
  rw [normalizedTube_band hc1 hc2]
  have hc : 0 < c := by linarith
  have hh : (1 / 2 : ℝ) ^ m ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2c : 1 ≤ 2 / c := by rw [le_div_iff₀ hc]; linarith
  have hr1 : 1 ≤ (2 / c) ^ (1 - cantorDim) := Real.one_le_rpow h2c (by linarith [cantorDim_mem.2])
  have hA1 : 1 ≤ (c + 1) - c * (1 / 2) ^ m := by nlinarith
  exact one_le_mul_of_one_le_of_one_le hA1 hr1

/-- [proved-standard; formal-checked] **Two-sided bounds**: `ε^(1−D) ≤ V(ε) ≤ 2^(2−D)·ε^(1−D)` on `(0, ½]`. -/
theorem cantorTube_bounds {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) :
    ε ^ (1 - cantorDim) ≤ cantorTube ε ∧
      cantorTube ε ≤ (2 : ℝ) ^ (2 - cantorDim) * ε ^ (1 - cantorDim) := by
  obtain ⟨h1, h2⟩ := normalizedTube_bounds hε hε'
  have hp : 0 < ε ^ (1 - cantorDim) := Real.rpow_pos_of_pos hε _
  rw [cantorTube_eq_rpow_mul hε]
  constructor <;> nlinarith

/-- [proved-standard; formal-checked] **Minkowski dimension `D`**: `log V(ε)/log ε → 1 − D` as `ε → 0⁺`. -/
theorem tendsto_log_cantorTube_div_log :
    Tendsto (fun ε => Real.log (cantorTube ε) / Real.log ε) (𝓝[>] 0) (𝓝 (1 - cantorDim)) := by
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ε ∈ Set.Ioo 0 (1 / 2) := Ioo_mem_nhdsGT (by norm_num)
  have heq : ∀ᶠ ε in 𝓝[>] (0 : ℝ), (1 - cantorDim) + Real.log (normalizedTube ε) / Real.log ε =
      Real.log (cantorTube ε) / Real.log ε := by
    filter_upwards [hev] with ε hε
    have hlogneg : Real.log ε < 0 := Real.log_neg hε.1 (by linarith [hε.2])
    obtain ⟨h1, -⟩ := normalizedTube_bounds hε.1 hε.2.le
    have hε0 := hε.1
    rw [cantorTube_eq_rpow_mul hε.1, Real.log_mul (by positivity) (by linarith),
      Real.log_rpow hε.1, add_div, mul_div_assoc, div_self hlogneg.ne, mul_one]
  have hlim : Tendsto (fun ε => Real.log (normalizedTube ε) / Real.log ε) (𝓝[>] 0) (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (g := fun ε => Real.log ((2 : ℝ) ^ (2 - cantorDim)) / Real.log ε)
      (h := fun _ => 0) (tendsto_const_nhds.div_atBot Real.tendsto_log_nhdsGT_zero)
      tendsto_const_nhds ?_ ?_
    · filter_upwards [hev] with ε hε
      have hlogneg : Real.log ε < 0 := Real.log_neg hε.1 (by linarith [hε.2])
      obtain ⟨h1, h2⟩ := normalizedTube_bounds hε.1 hε.2.le
      exact div_le_div_of_nonpos_of_le hlogneg.le (Real.log_le_log (by linarith) h2)
    · filter_upwards [hev] with ε hε
      have hlogneg : Real.log ε < 0 := Real.log_neg hε.1 (by linarith [hε.2])
      obtain ⟨h1, -⟩ := normalizedTube_bounds hε.1 hε.2.le
      exact div_nonpos_of_nonneg_of_nonpos (Real.log_nonneg h1) hlogneg.le
  have h := (tendsto_const_nhds (x := 1 - cantorDim)).add hlim
  rw [add_zero] at h
  exact h.congr' heq

end MinkowskiDimension

/-! ## The content oscillates -/

section Oscillation

/-- [proved-standard; formal-checked] At a fixed phase `c ∈ (1/3, 1]`, `f(c·3^(−m)/2) → g(c)` as `m → ∞`. -/
theorem tendsto_normalizedTube_band {c : ℝ} (hc1 : 1 / 3 < c) (hc2 : c ≤ 1) :
    Tendsto (fun m : ℕ => normalizedTube (c * (1 / 3 : ℝ) ^ m / 2)) atTop (𝓝 (bandProfile c)) := by
  simp_rw [normalizedTube_band hc1 hc2]
  have h : Tendsto (fun m : ℕ => (1 / 2 : ℝ) ^ m) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have h' := ((tendsto_const_nhds (x := c + 1)).sub (h.const_mul c)).mul_const
    ((2 / c) ^ (1 - cantorDim))
  rw [mul_zero, sub_zero] at h'
  unfold bandProfile
  rw [add_comm 1 c]
  exact h'

/-- [proved-standard; formal-checked] The points `c·3^(−m)/2`, `c > 0`, tend to `0` from the right. -/
theorem tendsto_band_points {c : ℝ} (hc : 0 < c) :
    Tendsto (fun m : ℕ => c * (1 / 3 : ℝ) ^ m / 2) atTop (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, Eventually.of_forall fun m => by simp only [Set.mem_Ioi]; positivity⟩
  have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 3)
    (by norm_num)).const_mul c).div_const 2
  rwa [mul_zero, zero_div] at h

/-- [proved-standard; formal-checked] Along `ε_m = 3^(−m)/2`, `f(ε_m) → 2^(2−D)`. -/
theorem tendsto_normalizedTube_half_third_pow :
    Tendsto (fun m : ℕ => normalizedTube ((1 / 3 : ℝ) ^ m / 2)) atTop
      (𝓝 ((2 : ℝ) ^ (2 - cantorDim))) := by
  have h := tendsto_normalizedTube_band (c := 1) (by norm_num) le_rfl
  simp_rw [one_mul, bandProfile_one] at h
  exact h

/-- [proved-standard; formal-checked] Along `ε′_m = 3^(−m)/4`, `f(ε′_m) → (3/2)·4^(1−D)`. -/
theorem tendsto_normalizedTube_quarter_third_pow :
    Tendsto (fun m : ℕ => normalizedTube ((1 / 3 : ℝ) ^ m / 4)) atTop
      (𝓝 ((3 / 2) * (4 : ℝ) ^ (1 - cantorDim))) := by
  have h := tendsto_normalizedTube_band (c := 1 / 2) (by norm_num) (by norm_num)
  rw [bandProfile_half] at h
  refine h.congr fun m => ?_
  congr 1
  ring

/-- [proved-standard; formal-checked] `2^(1−D) < 4/3`, which is `D² + D > 1`. -/
theorem two_rpow_one_sub_cantorDim_lt : (2 : ℝ) ^ (1 - cantorDim) < 4 / 3 := by
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl2 : Real.log 2 = cantorDim * Real.log 3 := by
    unfold cantorDim
    field_simp
  have hlog43 : Real.log (4 / 3) = 2 * Real.log 2 - Real.log 3 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4 / 3), Real.rpow_def_of_pos (by norm_num),
    Real.exp_lt_exp, hlog43, hl2]
  nlinarith [mul_pos hl3 (sub_pos.2 cantorDim_sq_add_gt_one)]

/-- [proved-standard; formal-checked] **The two limits differ**: `(3/2)·4^(1−D) < 2^(2−D)`. -/
theorem quarter_limit_lt_half_limit :
    (3 / 2) * (4 : ℝ) ^ (1 - cantorDim) < (2 : ℝ) ^ (2 - cantorDim) := by
  have hx := two_rpow_one_sub_cantorDim_lt
  have hx0 : (0 : ℝ) < 2 ^ (1 - cantorDim) := by positivity
  rw [← bandProfile_one, bandProfile, show (4 : ℝ) = 2 * 2 by norm_num,
    Real.mul_rpow (by norm_num) (by norm_num)]
  norm_num
  nlinarith

/-- [proved-standard; formal-checked] **The Cantor string is not Minkowski measurable**: `f` has no limit at `0⁺`. -/
theorem normalizedTube_not_tendsto : ¬ ∃ M, Tendsto normalizedTube (𝓝[>] 0) (𝓝 M) := by
  rintro ⟨M, hM⟩
  have h1 := hM.comp (tendsto_band_points (c := 1) one_pos)
  have h2 := hM.comp (tendsto_band_points (c := 1 / 2) (by norm_num))
  have e1 : M = (2 : ℝ) ^ (2 - cantorDim) := by
    refine tendsto_nhds_unique h1 ?_
    refine tendsto_normalizedTube_half_third_pow.congr fun m => ?_
    simp [Function.comp]
  have e2 : M = (3 / 2) * (4 : ℝ) ^ (1 - cantorDim) := by
    refine tendsto_nhds_unique h2 ?_
    refine tendsto_normalizedTube_quarter_third_pow.congr fun m => ?_
    simp only [Function.comp]
    congr 1
    ring
  have := quarter_limit_lt_half_limit
  rw [← e1, ← e2] at this
  exact lt_irrefl _ this

end Oscillation

/-! ## The upper and lower Minkowski contents -/

section Contents

/-- [proved-standard; formal-checked] For `0 < ε ≤ 3^(−M)/2`, `g((1 − D)/D) − 2·2^(−M) ≤ f(ε)`. -/
theorem lowerContent_sub_le_normalizedTube {M : ℕ} {ε : ℝ} (hε : 0 < ε)
    (hεM : ε ≤ (1 / 3 : ℝ) ^ M / 2) :
    bandProfile ((1 - cantorDim) / cantorDim) - 2 * (1 / 2 : ℝ) ^ M ≤ normalizedTube ε := by
  have hε' : ε ≤ 1 / 2 := hεM.trans (by
    have : (1 / 3 : ℝ) ^ M ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    linarith)
  obtain ⟨m, c, hc1, hc2, rfl⟩ := exists_band_form hε hε'
  have hMm : M ≤ m := by
    have hlt : (1 / 3 : ℝ) ^ (m + 1) < (1 / 3) ^ M := by
      rw [pow_succ]
      have hp : (0 : ℝ) < (1 / 3) ^ m := by positivity
      nlinarith
    have := (pow_lt_pow_iff_right_of_lt_one₀ (by norm_num : (0 : ℝ) < 1 / 3) (by norm_num)).1 hlt
    omega
  have hpow : (1 / 2 : ℝ) ^ m ≤ (1 / 2) ^ M := pow_le_pow_of_le_one (by norm_num) (by norm_num) hMm
  have := bandProfile_sub_le_normalizedTube_band (m := m) hc1 hc2
  have := bandProfile_ge (c := c) (by linarith)
  linarith

/-- [proved-standard; formal-checked] Near `0⁺`, `1 ≤ f ≤ 2^(2−D)`. -/
theorem normalizedTube_eventually_mem :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), 1 ≤ normalizedTube ε ∧ normalizedTube ε ≤ (2 : ℝ) ^ (2 - cantorDim) := by
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with ε hε
  exact normalizedTube_bounds hε.1 hε.2.le

/-- [proved-standard; formal-checked] **The upper Minkowski content** is `limsup f = 2^(2−D)`. -/
theorem limsup_normalizedTube :
    limsup normalizedTube (𝓝[>] 0) = (2 : ℝ) ^ (2 - cantorDim) := by
  have hev := normalizedTube_eventually_mem
  have hcob : IsCoboundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) normalizedTube :=
    isCoboundedUnder_le_of_eventually_le _ (hev.mono fun _ h => h.1)
  have hbdd : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) normalizedTube :=
    isBoundedUnder_of_eventually_le (hev.mono fun _ h => h.2)
  refine le_antisymm (limsup_le_of_le hcob (hev.mono fun _ h => h.2)) ?_
  have hpts := tendsto_band_points (c := 1) one_pos
  have hseq : Tendsto (normalizedTube ∘ fun m : ℕ => 1 * (1 / 3 : ℝ) ^ m / 2) atTop
      (𝓝 ((2 : ℝ) ^ (2 - cantorDim))) := by
    refine tendsto_normalizedTube_half_third_pow.congr fun m => ?_
    simp [Function.comp]
  rw [← hseq.limsup_eq, limsup_comp]
  refine limsup_le_limsup_of_le hpts ?_ hbdd
  exact isCoboundedUnder_le_of_eventually_le _ (hpts.eventually (hev.mono fun _ h => h.1))

/-- [proved-standard; formal-checked] **The lower Minkowski content** is `liminf f = g((1 − D)/D)`. -/
theorem liminf_normalizedTube :
    liminf normalizedTube (𝓝[>] 0) = bandProfile ((1 - cantorDim) / cantorDim) := by
  have hev := normalizedTube_eventually_mem
  have hcob : IsCoboundedUnder (· ≥ ·) (𝓝[>] (0 : ℝ)) normalizedTube :=
    isCoboundedUnder_ge_of_eventually_le _ (hev.mono fun _ h => h.2)
  have hbdd : IsBoundedUnder (· ≥ ·) (𝓝[>] (0 : ℝ)) normalizedTube :=
    isBoundedUnder_of_eventually_ge (hev.mono fun _ h => h.1)
  have hstar := lowerProfilePoint_mem
  refine le_antisymm ?_ ?_
  · have hpts := tendsto_band_points (c := (1 - cantorDim) / cantorDim) (by linarith [hstar.1])
    have hseq := tendsto_normalizedTube_band hstar.1 hstar.2
    rw [← hseq.liminf_eq, show (fun m : ℕ => normalizedTube ((1 - cantorDim) / cantorDim *
      (1 / 3 : ℝ) ^ m / 2)) = normalizedTube ∘ fun m : ℕ => (1 - cantorDim) / cantorDim *
      (1 / 3 : ℝ) ^ m / 2 from rfl, liminf_comp]
    refine liminf_le_liminf_of_le hpts hbdd ?_
    exact isCoboundedUnder_ge_of_eventually_le _ (hpts.eventually (hev.mono fun _ h => h.2))
  · have hlim : Tendsto (fun M : ℕ => bandProfile ((1 - cantorDim) / cantorDim) -
        2 * (1 / 2 : ℝ) ^ M) atTop (𝓝 (bandProfile ((1 - cantorDim) / cantorDim))) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num)).const_mul 2
      rw [mul_zero] at h
      simpa using (tendsto_const_nhds (x := bandProfile ((1 - cantorDim) / cantorDim))).sub h
    refine le_of_tendsto' hlim fun M => le_liminf_of_le hcob ?_
    have hM : (0 : ℝ) < (1 / 3) ^ M / 2 := by positivity
    filter_upwards [Ioo_mem_nhdsGT hM] with ε hε
    exact lowerContent_sub_le_normalizedTube hε.1 hε.2.le

end Contents

/-! ## The correction along the orbit `ε·3^(−k)` -/

section Join

/-- [proved-derived; formal-checked] **Along the orbit**: `f(ε·3^(−k)) = f(ε) + Σ_(i<k) (ε·3^(−i))^D`. -/
theorem normalizedTube_third_pow {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (k : ℕ) :
    normalizedTube (ε * (1 / 3 : ℝ) ^ k) =
      normalizedTube ε + ∑ i ∈ Finset.range k, (ε * (1 / 3 : ℝ) ^ i) ^ cantorDim := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hk : ε * (1 / 3 : ℝ) ^ k ≤ 1 / 2 := by
      have : (1 / 3 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      nlinarith
    rw [Finset.sum_range_succ, ← add_assoc, ← ih, pow_succ, ← mul_assoc, mul_one_div,
      normalizedTube_third (by positivity) hk]

/-- [proved-derived; formal-checked] The correction sums to `Σ_(i<k) (ε·3^(−i))^D = 2(1 − 2^(−k))·ε^D`. -/
theorem correction_eq {ε : ℝ} (hε : 0 < ε) (k : ℕ) :
    ∑ i ∈ Finset.range k, (ε * (1 / 3 : ℝ) ^ i) ^ cantorDim =
      2 * (1 - (1 / 2 : ℝ) ^ k) * ε ^ cantorDim := by
  have hterm : ∀ i ∈ Finset.range k, (ε * (1 / 3 : ℝ) ^ i) ^ cantorDim =
      ε ^ cantorDim * (1 / 2 : ℝ) ^ i := by
    intro i _
    rw [Real.mul_rpow hε.le (by positivity), ← Real.rpow_natCast_mul (by norm_num),
      mul_comm (i : ℝ), Real.rpow_mul_natCast (by norm_num), third_rpow_cantorDim]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, geom_sum_eq (by norm_num : (1 / 2 : ℝ) ≠ 1)]
  field_simp
  ring

/-- [proved-derived; formal-checked] **The orbit correction is bounded**: `0 ≤ f(ε·3^(−k)) − f(ε) ≤ ε^D/(1 − 2⁻¹)`. -/
theorem normalizedTube_third_pow_sub_le {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 2) (k : ℕ) :
    0 ≤ normalizedTube (ε * (1 / 3 : ℝ) ^ k) - normalizedTube ε ∧
      normalizedTube (ε * (1 / 3 : ℝ) ^ k) - normalizedTube ε ≤ ε ^ cantorDim / (1 - 2⁻¹) := by
  rw [normalizedTube_third_pow hε hε' k, add_sub_cancel_left, correction_eq hε k]
  have h0 : (0 : ℝ) < ε ^ cantorDim := Real.rpow_pos_of_pos hε _
  have h1 : (1 / 2 : ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (0 : ℝ) ≤ (1 / 2) ^ k := by positivity
  constructor
  · nlinarith
  · rw [show (1 : ℝ) - 2⁻¹ = 1 / 2 by norm_num, div_div_eq_mul_div, div_one]
    nlinarith

end Join

end Holonics.Foundation.FractalStringTube
