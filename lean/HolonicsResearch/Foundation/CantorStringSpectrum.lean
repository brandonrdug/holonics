import HolonicsResearch.Foundation.FractalStringTube
import Holonics.Objects.SourceHolon
import Mathlib.Topology.Instances.CantorSet
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The Cantor string placed and heard: its holes exhaust the complement, and its count oscillates at order `x^D`

[definition] Source: #410's box "Fractal strings: Lapidus–Pomerance (1993) and Lapidus–Maier (1995) (Minkowski
content, spectral counting, Tauberian machinery, inverse counterexample at ½); Herichi–Lapidus weighted shift;
Makarov (1985); Cantor-complement gaps of `Foundation/FractalPacking`". `HolonicsResearch/Foundation/FractalStringTube`
(#1030; the record `2026-11-19_THE_CANTOR_STRINGS_TUBE_BEATS_WITH_ITS_COMPLEX_DIMENSIONS_...`) took the Cantor
string's tube and left owed, among the rest, the spectral asymptotic and the holes placed as intervals exhausting the
Cantor complement. This module takes those two on the one string the tree holds. The owner it extends is
`Foundation/FractalString`: its two counts (`geometricCount`, `spectralCount`, joined by
`spectralCount_eq_sum_geometricCount`) and its paragraph "The Cantor string", whose holes are `FractalPacking`'s
sibling gaps (`cantorGap`, `cantor_gap_length`, `cantor_depth_gaps`). A hole's Dirichlet modes are its ring's
reflection-reversing modes, so a receiver at scale `x` counts the holes and hears, in each hole of length `ℓ`, the
windings `k ≤ x·ℓ`. The cells are `FractalPacking`'s `descend w root`, whose lower end is the Cantor reader's moment
(`Objects/SourceHolon.descend_eq_moment`). The Cantor set is Mathlib's (`preCantorSet`, `cantorSet`), which states
nothing on measure, so its nullity is proved here. The record
`2026-09-25_THE_MUSIC_IS_IN_THE_HOLES_HEARING_MULTIPLIES_BY_ZETA_AND_A_QUASICRYSTAL_IS_A_HELIX_THAT_NEVER_LOCKS`
states, as standard, that lattice ratios give persistent oscillation. Atlas rows read: `fractal.cantor-gap-zeta` and
`fractal.cantor-tube-content` (their scope lines: the exhaustion of the Cantor complement is not proved),
`fractal.string-counts`, `fractal.minkowski-spectral-asymptotic` (Lapidus–Pomerance's direct theorem, which assumes
Minkowski measurability) and `rh.inverse-spectral-fractal-string`. References: Lapidus–van Frankenhuijsen, *Fractal
Geometry, Complex Dimensions and Zeta Functions*, 2nd ed., Springer 2013; the two-term count of this string is the
example of Fleckinger–Vassiliev, *An example of a two-term asymptotics for the "counting function" of a fractal
drum*, Trans. AMS 337 (1993).

What is proved. An address is a word of hands `w : List Hand`, as in `FractalPacking`: its head is the newest, finest
restriction. Throughout `n = |w|` and `D = cantorDim = log 2/log 3`.

1. [definition] **The cells and holes placed** (`ternaryDigit`, `cellLower`, `cell`, `hole`): `c_w = S_w 0`,
   `cell(w) = [c_w, c_w + 3^(−n)]` and `hole(w) = (c_w + 3^(−(n+1)), c_w + 2·3^(−(n+1)))`, its open middle third.
   [proved-derived; formal-checked] They are the owner's: `c_w = (descend w root).lower`, the Cantor reader's moment
   (`cellLower_eq_descend`, `cellLower_eq_moment`); the cell is `descend w root` and the hole is the gap between its
   `leftChild` and `rightChild` (`cell_eq_descend`, `hole_eq_descend`). Read from its last, coarsest hand, the address
   is the ternary expansion `c_w = Σ_(i<n) d_i·3^(−(i+1))`, `d_i ∈ {0, 2}` the digit of the `i`-th hand of
   `w.reverse` (`cellLower_eq_sum`). The recursions: `wordMap_eq_add`, `cellLower_cons` (a finest hand),
   `cellLower_append` (a coarsest hand), `ratCast_wordMap`.
2. [proved-derived; formal-checked] **The pre-Cantor sets are unions of cells** (`cantorMap_image_cell`, `cell_nil`,
   `mem_preCantorSet_iff`, `preCantorSet_eq_iUnion_cell`): `S_h(cell(w)) = cell(w ++ [h])`, so Mathlib's recursion
   `P_(n+1) = P_n/3 ∪ (2 + P_n)/3`, which adds a coarsest hand, is the owner's, which adds a finest, and
   `preCantorSet n = ⋃_(|w| = n) cell(w)`.
3. [proved-standard; formal-checked] **The holes exhaust the complement** (`cell_subset_preCantorSet`,
   `cell_cons_subset`, `disjoint_cell`, `hole_subset_cell`, `disjoint_hole_cell_cons`, `hole_not_mem_preCantorSet`,
   `pairwise_disjoint_hole`, `hole_subset_unitInterval`, `disjoint_hole_cantorSet`, `unitInterval_diff_cantorSet`):
   distinct addresses of one depth have disjoint cells; a depth-`n` hole misses `P_(n+1)`, so holes of different
   depths are disjoint too; each hole lies in `[0, 1]` and misses `C`; and `[0, 1] \ C = ⋃_w hole(w)`, a point of the
   complement lying in the hole of the cell it last met. Both ends of each hole lie in `C` (`cellLower_replicate_left`,
   `cellUpper_replicate_right`, `mem_cantorSet_of_forall`, `cellLower_mem_cantorSet`, `cellUpper_mem_cantorSet`,
   `hole_ends_mem_cantorSet`).
4. [proved-standard; formal-checked] **The complement's string is `cantorString`, and `C` is null** (`wordAt`,
   `length_wordAt`, `wordAt_bijective`, `holeAt`, `volume_hole`, `cantorGap_eq_cantorLength`, `volume_holeAt`,
   `words_map_hole_length`, `pairwise_disjoint_holeAt`, `iUnion_holeAt`, `tsum_cantorString`,
   `volume_unitInterval_diff_cantorSet`, `volume_cantorSet`): the place `⟨n, i⟩` of `cantorString` names the `i`-th
   word of `words n`, a bijection onto all addresses, and the hole there has Lebesgue length
   `cantorString ⟨n, i⟩ = cantorLength n = cantorGap w`. By countable additivity and `cantor_total_length`,
   `vol([0, 1] \ C) = 1`, so `vol C = 0`.
5. [proved-standard; formal-checked] **The tube is a measure** (`infDist_cantorSet_of_mem_hole`,
   `volume_hole_innerTube`, `volume_innerTube`): in a hole `(a, b)` the distance to `C` is `min(x − a, b − x)`, so the
   inner `ε`-neighbourhood of `C` in its complement is the union of the holes' boundary layers, and
   `vol{x ∈ [0, 1] \ C : d(x, C) < ε} = V(ε)` for `ε > 0`, the string's tube `cantorTube ε` of `FractalStringTube`.
   This is the step that module's "What is not claimed" names as owed for its tube.
6. [definition] **The spectral count** (`cantorCount`): `N(x) = Σ_n 2^n ⌊x·3^(−(n+1))⌋₊`, summed over the depths
   below `⌊x⌋₊`. [proved-derived; formal-checked] It is the same finite sum over every range `m` with `x < 3^(m+1)`
   (`floor_mul_cantorLength_eq_zero`, `lt_three_pow_floor_add_one`, `sum_range_eq_of_le`, `cantorCount_eq_sum`),
   and it is the owner's `spectralCount` of the holes of depth below `m` (`cantorCount_eq_spectralCount`, on
   `FractalStringTube.cantorLongHoles`), so the owner's hearing identity reads it as the geometric count carried round
   every winding.
7. [proved-derived; formal-checked] **The count is self-similar** (`cantorCount_three_mul`): `N(3x) = 2N(x) + ⌊x⌋₊`
   for every real `x`. At scale `3x` the largest hole hears `⌊x⌋₊` harmonics, and each of the two halves hears what
   the whole string hears at `x`. Hence `N(3^k) = 3^k − 2^k` and `N(2·3^k) = 2·3^k − 2^(k+1)` (`cantorCount_eq_zero`,
   `cantorCount_three_pow`, `cantorCount_two_mul_three_pow`).
8. [proved-standard; formal-checked] **The Weyl term and the second term** (`sum_two_pow_mul_cantorLength`,
   `sub_cantorCount_eq`, `three_pow_rpow`, `cantorCount_le`, `rpow_cantorDim_le_sub_cantorCount`,
   `sub_cantorCount_lt`, `spectralRatio`, `spectralRatio_mem`, `tendsto_cantorCount_div`): for `x < 3^(m+1)`,
   `x − N(x) = x(2/3)^m + Σ_(n<m) 2^n {x·3^(−(n+1))}`, the deep holes' share and the shallow holes' fractional parts.
   So `N(x) ≤ x` for `x ≥ 0` (the Weyl term `|Ω|·x`, with `|Ω| = 1` the total length) and `N(x)/x → 1`; and for
   `x ≥ 1`, `x^D ≤ x − N(x) < 2x^D`. The second term has order `x^D` with the constants `c₁ = 1`, reached at every
   `3^k`, and `c₂ = 2`, from the band profile's bound `g(c) ≤ 2^(2−D)` of `FractalStringTube` (`bandProfile_le`,
   `bandProfile_eq`) read at `c = 3^k/x` for `3^k ≤ x < 3^(k+1)`.
9. [proved-standard; formal-checked] **The second term oscillates** (`spectralRatio_three_mul`,
   `spectralRatio_three_mul_natCast`, `spectralRatio_three_pow`, `spectralRatio_two_mul_three_pow`,
   `one_lt_two_rpow_one_sub_cantorDim`, `spectralRatio_not_tendsto`, `cantorString_counts_oscillate`): with
   `R(x) = (x − N(x))/x^D`, `R(3x) = R(x) + (x − ⌊x⌋₊)/(2x^D)` for `x ≥ 0`, so on the natural numbers `R` is invariant
   under `x ↦ 3x`; `R(3^k) = 1` and `R(2·3^k) = 2^(1−D) > 1`, so `R` has no limit at `∞`. Beside
   `normalizedTube_not_tendsto`: both counts of the Cantor string oscillate, the tube as `ε → 0⁺` and the spectrum as
   `x → ∞`.

**One period on both sides.** In the log chart `t = log x`, `spectralRatio_three_mul` reads
`R(t + log 3) = R(t) + (x − ⌊x⌋₊)/(2x^D)`, a correction that is zero on the natural numbers; on the geometric side,
with `t = −log ε`, `normalizedTube_third` reads `f(t + log 3) = f(t) + e^(−Dt)`. Both counts are periodic of period
`log 3` up to their corrections, the reciprocal spacing of the complex dimensions `D + 2πik/log 3`
(`cantor_complex_dimensions`): the real part `D` is the order of the second term, and the rotation part is what keeps
it from settling. Lapidus–Pomerance's direct theorem gives `N_ν(x) = x − c_D·M·x^D + o(x^D)` for a Minkowski
measurable string with content `M`; the Cantor string lies outside that hypothesis (`normalizedTube_not_tendsto`), and
its second term has the same order `x^D` with no constant.

What is not claimed.
- The Tauberian theorem in general, and Lapidus–Pomerance's direct theorem and criterion (a string is Minkowski
  measurable if and only if `ℓ_j ∼ L·j^(−1/D)`) for a general string. Here one string's count is computed from its
  holes, not transferred from its tube.
- The nonlattice case (the owner's golden string, `goldenStringZeta_eq`) and the lattice criterion for a general
  self-similar string.
- Lapidus–Maier's inverse spectral problem and its failure at `½` (atlas `rh.inverse-spectral-fractal-string`),
  Herichi–Lapidus's weighted shift and spectral operator, and Makarov's theorem (1985). They stay owed in the box.
- The explicit formula of the second term: `R`'s periodic profile in `log x`, its Fourier coefficients at the complex
  dimensions, and its upper and lower limits (`c₁ = 1` is reached; that `2` is the least upper bound is not proved),
  with their relation to the tube's upper and lower contents.
- An operator: no Dirichlet Laplacian on `[0, 1] \ C` is built, so that `N` counts its eigenvalues is the owner's
  reading of a hole's harmonics, not a theorem here.

**Computational object.** The helical pair interaction, read on the holes: each hole is the gap that a pair of sibling
cells leaves at the restriction producing them (`hole_eq_descend`), and a receiver at scale `x` hears that hole's
windings `k ≤ x·ℓ` (the owner's `spectralCount`). Of the winding guide's six objects: faces and placement (the holes
are placed: an address is a placement, its ternary expansion `c_w` is the face that places it, and the placed holes
exhaust the complement; `R` is a face of the count read at the receiver's scale), the helix (each hole is a ring whose
windings `⌊x·ℓ⌋₊` the count sums; in the log chart `x = t·3^k` is a whole winding `k` and a phase `t ∈ [1, 3)`, and
`R` returns to its value one winding up at the natural numbers), and the tower thread (the restriction tower of
`FractalPacking`, one hand per level: `preCantorSet n` is the union of the depth-`n` cells, and
`N(3x) = 2N(x) + ⌊x⌋₊` is one level of the thread). The pair beyond the sibling gap, the cell holonomy and the tube
stay attached; the inner neighbourhood of `volume_innerTube`, a neighbourhood of a boundary, is not the guide's tube
(a transfer between cross-section charts) and uses none of it.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Foundation.CantorStringSpectrum

open Filter Topology MeasureTheory
open Holonics.Foundation.FractalString Holonics.Foundation.FractalPacking
open Holonics.Foundation.FractalStringTube

/-! ## The cells and the holes, placed -/

section Placed

/-- [definition] The ternary digit a hand writes: `0` for the left third, `2` for the right. -/
def ternaryDigit : Hand → ℝ
  | .left => 0
  | .right => 2

/-- [definition] The lower end of the cell addressed by `w`, `S_w 0`, read in `ℝ`. -/
noncomputable def cellLower (w : List Hand) : ℝ := wordMap w 0

/-- [definition] The cell addressed by `w`: `[c_w, c_w + 3^(−|w|)]`. -/
noncomputable def cell (w : List Hand) : Set ℝ :=
  Set.Icc (cellLower w) (cellLower w + (1 / 3 : ℝ) ^ w.length)

/-- [definition] The hole of the cell addressed by `w`: its open middle third. -/
noncomputable def hole (w : List Hand) : Set ℝ :=
  Set.Ioo (cellLower w + (1 / 3 : ℝ) ^ (w.length + 1)) (cellLower w + 2 * (1 / 3 : ℝ) ^ (w.length + 1))

/-- [proved-derived; formal-checked] Every composite is affine: `S_w y = c_w + 3^(−|w|)·y`. -/
theorem wordMap_eq_add (w : List Hand) (y : ℝ) :
    wordMap w y = cellLower w + (1 / 3 : ℝ) ^ w.length * y := by
  have := wordMap_sub w y 0
  rw [cellLower]
  linarith

/-- [proved-derived; formal-checked] The empty address starts at `0`. -/
theorem cellLower_nil : cellLower [] = 0 := rfl

/-- [proved-derived; formal-checked] A new, finest hand moves the lower end by its digit: `c_(h::w) = c_w +
d_h·3^(−(|w|+1))`. -/
theorem cellLower_cons (h : Hand) (w : List Hand) :
    cellLower (h :: w) = cellLower w + ternaryDigit h * (1 / 3 : ℝ) ^ (w.length + 1) := by
  rw [cellLower, wordMap, wordMap_eq_add, pow_succ]
  cases h <;> simp only [cantorMap, ternaryDigit] <;> ring

/-- [proved-derived; formal-checked] A new, coarsest hand acts outermost: `c_(w ++ [h]) = S_h(c_w)`. -/
theorem cellLower_append (w : List Hand) (h : Hand) :
    cellLower (w ++ [h]) = cantorMap h (cellLower w) := by
  rw [cellLower, wordMap_append]
  rfl

/-- [proved-derived; formal-checked] The composites commute with the cast `ℚ → ℝ`. -/
theorem ratCast_wordMap (w : List Hand) (q : ℚ) :
    ((wordMap w q : ℚ) : ℝ) = wordMap w (q : ℝ) := by
  induction w generalizing q with
  | nil => rfl
  | cons h w ih =>
      rw [wordMap, wordMap, ih]
      congr 1
      cases h <;> simp [cantorMap]

/-- [proved-derived; formal-checked] The lower end is the owner's: `c_w = (descend w root).lower`. -/
theorem cellLower_eq_descend (w : List Hand) : ((descend w root).lower : ℝ) = cellLower w := by
  rw [descend_root_eq_wordMap, ratCast_wordMap]
  simp [cellLower]

/-- [proved-derived; formal-checked] The lower end is the Cantor reader's moment (`SourceHolon.descend_eq_moment`). -/
theorem cellLower_eq_moment (w : List Hand) :
    cellLower w = (Objects.SourceHolon.cantorReader.moment w : ℝ) := by
  rw [← cellLower_eq_descend, Objects.SourceHolon.descend_eq_moment]

/-- [proved-derived; formal-checked] The cell is the owner's addressed cell `descend w root`, read in `ℝ`. -/
theorem cell_eq_descend (w : List Hand) :
    cell w = Set.Icc ((descend w root).lower : ℝ) ((descend w root).upper : ℝ) := by
  have hw := root_descend_width w
  rw [Cell.width] at hw
  have hu : ((descend w root).upper : ℝ) = cellLower w + (1 / 3 : ℝ) ^ w.length := by
    rw [← cellLower_eq_descend, show (descend w root).upper = (descend w root).lower + (1 / 3 : ℚ) ^ w.length by
      linarith]
    push_cast
    ring
  rw [cell, hu, cellLower_eq_descend]

/-- [proved-derived; formal-checked] The hole is the owner's sibling gap, between the two children of the cell. -/
theorem hole_eq_descend (w : List Hand) :
    hole w = Set.Ioo ((leftChild (descend w root)).upper : ℝ) ((rightChild (descend w root)).lower : ℝ) := by
  have hw := root_descend_width w
  have hl : ((leftChild (descend w root)).upper : ℝ) = cellLower w + (1 / 3 : ℝ) ^ (w.length + 1) := by
    rw [← cellLower_eq_descend]
    simp only [leftChild, hw]
    push_cast
    ring
  have hr : ((rightChild (descend w root)).lower : ℝ) = cellLower w + 2 * (1 / 3 : ℝ) ^ (w.length + 1) := by
    rw [← cellLower_eq_descend]
    simp only [rightChild, hw]
    push_cast
    ring
  rw [hole, hl, hr]

/-- [proved-derived; formal-checked] `S_h` carries the cell of `w` onto the cell of `w ++ [h]`. -/
theorem cantorMap_image_cell (h : Hand) (w : List Hand) :
    cantorMap h '' cell w = cell (w ++ [h]) := by
  have hs : (0 : ℝ) < (1 / 3) ^ w.length := by positivity
  ext x
  simp only [Set.mem_image, cell, Set.mem_Icc, cellLower_append, List.length_append,
    List.length_singleton, pow_succ]
  constructor
  · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
    cases h <;> simp only [cantorMap] <;> constructor <;> linarith
  · rintro ⟨h1, h2⟩
    cases h
    · refine ⟨3 * x, ⟨?_, ?_⟩, ?_⟩ <;> simp only [cantorMap] at * <;> linarith
    · refine ⟨3 * x - 2, ⟨?_, ?_⟩, ?_⟩ <;> simp only [cantorMap] at * <;> linarith

/-- [proved-derived; formal-checked] The empty address's cell is `[0, 1]`. -/
theorem cell_nil : cell [] = Set.Icc 0 1 := by
  simp [cell, cellLower_nil]

/-- [proved-derived; formal-checked] **The pre-Cantor sets are the unions of the addressed cells**:
`x ∈ preCantorSet n` iff `x` lies in the cell of some word of `n` hands. -/
theorem mem_preCantorSet_iff {n : ℕ} {x : ℝ} :
    x ∈ preCantorSet n ↔ ∃ w : List Hand, w.length = n ∧ x ∈ cell w := by
  induction n generalizing x with
  | zero =>
      simp only [preCantorSet_zero, List.length_eq_zero_iff, exists_eq_left, cell_nil]
  | succ n ih =>
      rw [preCantorSet_succ]
      constructor
      · rintro (⟨y, hy, rfl⟩ | ⟨y, hy, rfl⟩)
        · obtain ⟨w, hw, hyw⟩ := ih.1 hy
          refine ⟨w ++ [.left], by simp [hw], ?_⟩
          rw [← cantorMap_image_cell]
          exact ⟨y, hyw, rfl⟩
        · obtain ⟨w, hw, hyw⟩ := ih.1 hy
          refine ⟨w ++ [.right], by simp [hw], ?_⟩
          rw [← cantorMap_image_cell]
          exact ⟨y, hyw, by simp only [cantorMap]; ring⟩
      · rintro ⟨v, hv, hx⟩
        obtain ⟨w, h, rfl⟩ : ∃ w h, v = w ++ [h] := by
          rcases List.eq_nil_or_concat v with h | ⟨w, h, rfl⟩
          · simp [h] at hv
          · exact ⟨w, h, List.concat_eq_append⟩
        have hw : w.length = n := by simpa using hv
        rw [← cantorMap_image_cell] at hx
        obtain ⟨y, hy, rfl⟩ := hx
        cases h
        · exact Or.inl ⟨y, ih.2 ⟨w, hw, hy⟩, rfl⟩
        · exact Or.inr ⟨y, ih.2 ⟨w, hw, hy⟩, by simp only [cantorMap]; ring⟩

/-- [proved-derived; formal-checked] `preCantorSet n = ⋃_(|w| = n) [c_w, c_w + 3^(−n)]`. -/
theorem preCantorSet_eq_iUnion_cell (n : ℕ) :
    preCantorSet n = ⋃ (w : List Hand) (_ : w.length = n), cell w := by
  ext x
  simp [mem_preCantorSet_iff]

/-- [proved-derived; formal-checked] A depth-`n` cell lies in `preCantorSet n`. -/
theorem cell_subset_preCantorSet (w : List Hand) : cell w ⊆ preCantorSet w.length :=
  fun _ hx => mem_preCantorSet_iff.2 ⟨w, rfl, hx⟩

/-- [proved-derived; formal-checked] A child's cell lies in its parent's. -/
theorem cell_cons_subset (h : Hand) (w : List Hand) : cell (h :: w) ⊆ cell w := by
  have hs : (0 : ℝ) < (1 / 3) ^ (w.length + 1) := by positivity
  have h3 : (1 / 3 : ℝ) ^ w.length = 3 * (1 / 3) ^ (w.length + 1) := by rw [pow_succ]; ring
  intro x hx
  simp only [cell, Set.mem_Icc, cellLower_cons, List.length_cons] at hx ⊢
  rw [h3]
  cases h <;> simp only [ternaryDigit] at hx <;> constructor <;> linarith [hx.1, hx.2]

/-- [proved-derived; formal-checked] **Distinct addresses of one depth have disjoint cells.** -/
theorem disjoint_cell {u v : List Hand} (hl : u.length = v.length) (huv : u ≠ v) :
    Disjoint (cell u) (cell v) := by
  induction u generalizing v with
  | nil => exact absurd (List.length_eq_zero_iff.1 hl.symm).symm huv
  | cons h u ih =>
      cases v with
      | nil => simp at hl
      | cons h' v =>
          have hl' : u.length = v.length := by simpa using hl
          by_cases he : u = v
          · subst he
            have hh : h ≠ h' := fun hh => huv (by rw [hh])
            have hs : (0 : ℝ) < (1 / 3) ^ (u.length + 1) := by positivity
            rw [Set.disjoint_left]
            intro x hx hx'
            simp only [cell, Set.mem_Icc, cellLower_cons, List.length_cons] at hx hx'
            cases h <;> cases h' <;> simp only [ternaryDigit, ne_eq, not_true_eq_false] at hh hx hx' <;>
              linarith [hx.1, hx.2, hx'.1, hx'.2]
          · exact (ih hl' he).mono (cell_cons_subset h u) (cell_cons_subset h' v)

/-- [proved-derived; formal-checked] A hole lies in its cell. -/
theorem hole_subset_cell (w : List Hand) : hole w ⊆ cell w := by
  have hs : (0 : ℝ) < (1 / 3) ^ (w.length + 1) := by positivity
  have h3 : (1 / 3 : ℝ) ^ w.length = 3 * (1 / 3) ^ (w.length + 1) := by rw [pow_succ]; ring
  intro x hx
  simp only [hole, cell, Set.mem_Ioo, Set.mem_Icc] at hx ⊢
  rw [h3]
  constructor <;> linarith [hx.1, hx.2]

/-- [proved-derived; formal-checked] A hole misses both of its children's cells. -/
theorem disjoint_hole_cell_cons (h : Hand) (w : List Hand) : Disjoint (hole w) (cell (h :: w)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [hole, cell, Set.mem_Ioo, Set.mem_Icc, cellLower_cons, List.length_cons] at hx hx'
  cases h <;> simp only [ternaryDigit] at hx' <;> linarith [hx.1, hx.2, hx'.1, hx'.2]

/-- [proved-derived; formal-checked] The hole of a depth-`n` cell misses `preCantorSet (n + 1)`. -/
theorem hole_not_mem_preCantorSet {w : List Hand} {x : ℝ} (hx : x ∈ hole w) :
    x ∉ preCantorSet (w.length + 1) := by
  rw [mem_preCantorSet_iff]
  rintro ⟨v, hv, hxv⟩
  cases v with
  | nil => simp at hv
  | cons h u =>
      have hu : u.length = w.length := by simpa using hv
      by_cases he : u = w
      · subst he
        exact Set.disjoint_left.1 (disjoint_hole_cell_cons h u) hx hxv
      · exact Set.disjoint_left.1 (disjoint_cell hu he) (cell_cons_subset h u hxv) (hole_subset_cell w hx)

/-- [proved-derived; formal-checked] **The holes are pairwise disjoint**, over every depth and address. -/
theorem pairwise_disjoint_hole : Pairwise fun u v : List Hand => Disjoint (hole u) (hole v) := by
  have key : ∀ u v : List Hand, u.length < v.length → Disjoint (hole u) (hole v) := by
    intro u v hlt
    rw [Set.disjoint_left]
    intro x hxu hxv
    exact hole_not_mem_preCantorSet hxu
      (preCantorSet_antitone (Nat.succ_le_of_lt hlt) (cell_subset_preCantorSet v (hole_subset_cell v hxv)))
  intro u v huv
  rcases lt_trichotomy u.length v.length with hlt | heq | hgt
  · exact key u v hlt
  · exact (disjoint_cell heq huv).mono (hole_subset_cell u) (hole_subset_cell v)
  · exact (key v u hgt).symm

/-- [proved-derived; formal-checked] Every hole lies in the unit cell. -/
theorem hole_subset_unitInterval (w : List Hand) : hole w ⊆ Set.Icc 0 1 :=
  (hole_subset_cell w).trans ((cell_subset_preCantorSet w).trans preCantorSet_subset_unitInterval)

/-- [proved-derived; formal-checked] Every hole misses the Cantor set. -/
theorem disjoint_hole_cantorSet (w : List Hand) : Disjoint (hole w) cantorSet := by
  rw [Set.disjoint_left]
  intro x hx hC
  exact hole_not_mem_preCantorSet hx (Set.mem_iInter.1 hC _)

/-- [proved-derived; formal-checked] **The holes exhaust the Cantor complement**:
`[0, 1] \ C = ⋃_w hole(w)`. -/
theorem unitInterval_diff_cantorSet : Set.Icc 0 1 \ cantorSet = ⋃ w : List Hand, hole w := by
  ext x
  simp only [Set.mem_sdiff, Set.mem_iUnion]
  constructor
  · rintro ⟨hx, hC⟩
    have hex : ∃ k, x ∉ preCantorSet k := by
      by_contra hall
      push Not at hall
      exact hC (Set.mem_iInter.2 hall)
    classical
    set k := Nat.find hex with hk
    have hk0 : k ≠ 0 := by
      intro h0
      have := Nat.find_spec hex
      rw [← hk, h0, preCantorSet_zero] at this
      exact this hx
    obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hk0
    have hxn : x ∈ preCantorSet n := by
      by_contra hc
      exact Nat.find_min hex (by omega : n < Nat.find hex) hc
    have hxk : x ∉ preCantorSet (n + 1) := by
      have := Nat.find_spec hex
      rwa [← hk, hn] at this
    obtain ⟨w, hw, hxw⟩ := mem_preCantorSet_iff.1 hxn
    have hl : x ∉ cell (.left :: w) := fun h =>
      hxk (by rw [← hw]; exact cell_subset_preCantorSet _ h)
    have hr : x ∉ cell (.right :: w) := fun h =>
      hxk (by rw [← hw]; exact cell_subset_preCantorSet _ h)
    have h3 : (1 / 3 : ℝ) ^ w.length = 3 * (1 / 3) ^ (w.length + 1) := by rw [pow_succ]; ring
    refine ⟨w, ?_⟩
    simp only [cell, Set.mem_Icc, cellLower_cons, List.length_cons, ternaryDigit, not_and_or,
      not_le] at hl hr hxw
    simp only [hole, Set.mem_Ioo]
    rw [h3] at hxw
    constructor
    · rcases hl with hl | hl <;> linarith [hxw.1, hxw.2]
    · rcases hr with hr | hr <;> linarith [hxw.1, hxw.2]
  · rintro ⟨w, hx⟩
    exact ⟨hole_subset_unitInterval w hx, Set.disjoint_left.1 (disjoint_hole_cantorSet w) hx⟩

/-- [proved-derived; formal-checked] Left hands below `w` keep its lower end. -/
theorem cellLower_replicate_left (k : ℕ) (w : List Hand) :
    cellLower (List.replicate k Hand.left ++ w) = cellLower w := by
  induction k with
  | zero => rfl
  | succ k ih => rw [List.replicate_succ, List.cons_append, cellLower_cons, ih, ternaryDigit, zero_mul, add_zero]

/-- [proved-derived; formal-checked] Right hands below `w` keep its upper end. -/
theorem cellUpper_replicate_right (k : ℕ) (w : List Hand) :
    cellLower (List.replicate k Hand.right ++ w) + (1 / 3 : ℝ) ^ (List.replicate k Hand.right ++ w).length =
      cellLower w + (1 / 3 : ℝ) ^ w.length := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append, cellLower_cons, List.length_cons, ← ih, ternaryDigit,
        pow_succ (1 / 3 : ℝ) (List.replicate k Hand.right ++ w).length]
      ring

/-- [proved-derived; formal-checked] A point in a cell of every depth from `|w|` on lies in the Cantor set. -/
theorem mem_cantorSet_of_forall {x : ℝ} {w : List Hand}
    (h : ∀ k : ℕ, ∃ v : List Hand, v.length = k + w.length ∧ x ∈ cell v) : x ∈ cantorSet := by
  refine Set.mem_iInter.2 fun m => ?_
  obtain ⟨v, hv, hx⟩ := h m
  exact preCantorSet_antitone (by omega : m ≤ v.length) (cell_subset_preCantorSet v hx)

/-- [proved-derived; formal-checked] Each cell's lower end lies in the Cantor set. -/
theorem cellLower_mem_cantorSet (w : List Hand) : cellLower w ∈ cantorSet := by
  refine mem_cantorSet_of_forall (w := w) fun k => ⟨List.replicate k Hand.left ++ w, by simp, ?_⟩
  rw [cell, Set.mem_Icc, cellLower_replicate_left]
  exact ⟨le_rfl, by simp only [le_add_iff_nonneg_right]; positivity⟩

/-- [proved-derived; formal-checked] Each cell's upper end lies in the Cantor set. -/
theorem cellUpper_mem_cantorSet (w : List Hand) : cellLower w + (1 / 3 : ℝ) ^ w.length ∈ cantorSet := by
  refine mem_cantorSet_of_forall (w := w) fun k => ⟨List.replicate k Hand.right ++ w, by simp, ?_⟩
  rw [cell, Set.mem_Icc, cellUpper_replicate_right]
  refine ⟨?_, le_rfl⟩
  rw [← cellUpper_replicate_right k w]
  simp only [le_add_iff_nonneg_right]
  positivity

/-- [proved-derived; formal-checked] **A hole's two ends lie in the Cantor set**: the left end is the upper end of
the left child's cell, the right end the lower end of the right child's. -/
theorem hole_ends_mem_cantorSet (w : List Hand) :
    cellLower w + (1 / 3 : ℝ) ^ (w.length + 1) ∈ cantorSet ∧
      cellLower w + 2 * (1 / 3 : ℝ) ^ (w.length + 1) ∈ cantorSet := by
  constructor
  · have := cellUpper_mem_cantorSet (.left :: w)
    rwa [cellLower_cons, ternaryDigit, zero_mul, add_zero, List.length_cons] at this
  · have := cellLower_mem_cantorSet (.right :: w)
    rwa [cellLower_cons, ternaryDigit] at this

/-- [proved-derived; formal-checked] **The address is the ternary expansion**: read from its last, coarsest hand,
`c_w = Σ_(i<|w|) d_i·3^(−(i+1))`, with `d_i ∈ {0, 2}` the digit of the `i`-th hand from the end. -/
theorem cellLower_eq_sum (w : List Hand) :
    cellLower w = ∑ i ∈ Finset.range w.length, ternaryDigit (w.reverse.getD i .left) * (1 / 3 : ℝ) ^ (i + 1) := by
  suffices h : ∀ u : List Hand,
      cellLower u.reverse = ∑ i ∈ Finset.range u.length, ternaryDigit (u.getD i .left) * (1 / 3 : ℝ) ^ (i + 1) by
    simpa using h w.reverse
  intro u
  induction u with
  | nil => rfl
  | cons h u ih =>
      rw [List.reverse_cons, cellLower_append, ih, List.length_cons, Finset.sum_range_succ']
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      have hsum : ∑ i ∈ Finset.range u.length, ternaryDigit (u.getD i .left) * (1 / 3 : ℝ) ^ (i + 1 + 1) =
          (∑ i ∈ Finset.range u.length, ternaryDigit (u.getD i .left) * (1 / 3 : ℝ) ^ (i + 1)) / 3 := by
        rw [Finset.sum_div]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [pow_succ]
        ring
      rw [hsum]
      cases h <;> simp only [cantorMap, ternaryDigit] <;> ring

end Placed

/-! ## The holes as the Cantor string, and the measure of the complement -/

section Measure

/-- [definition] The word at place `i` of depth `n` in the owner's list `words n`: the address of the hole that
`cantorString` indexes by `⟨n, i⟩`. -/
def wordAt (p : Σ n : ℕ, Fin (2 ^ n)) : List Hand :=
  (words p.1).get (Fin.cast (length_words p.1).symm p.2)

/-- [proved-derived; formal-checked] The word at `⟨n, i⟩` has `n` hands. -/
theorem length_wordAt (p : Σ n : ℕ, Fin (2 ^ n)) : (wordAt p).length = p.1 :=
  mem_words.1 (List.get_mem _ _)

/-- [proved-derived; formal-checked] Each address is listed once: `wordAt` is a bijection from the string's index
`Σ n, Fin 2^n` onto the words of hands. -/
theorem wordAt_bijective : Function.Bijective wordAt := by
  constructor
  · rintro ⟨n, i⟩ ⟨m, j⟩ h
    have hnm : n = m := by
      have := congrArg List.length h
      rwa [length_wordAt, length_wordAt] at this
    subst hnm
    have hij := (nodup_words n).get_inj_iff.1 h
    have : i = j := by
      rw [Fin.ext_iff] at hij ⊢
      simpa using hij
    rw [this]
  · intro w
    obtain ⟨i, hi⟩ := List.mem_iff_get.1 (mem_words.2 (rfl : w.length = w.length))
    refine ⟨⟨w.length, Fin.cast (length_words _) i⟩, ?_⟩
    exact hi

/-- [definition] The hole that `cantorString` indexes by `⟨n, i⟩`. -/
noncomputable def holeAt (p : Σ n : ℕ, Fin (2 ^ n)) : Set ℝ := hole (wordAt p)

/-- [proved-derived; formal-checked] The hole of a depth-`n` cell is `3^(−(n+1))` long. -/
theorem volume_hole (w : List Hand) : volume (hole w) = ENNReal.ofReal (cantorLength w.length) := by
  rw [hole, Real.volume_Ioo, cantorLength]
  congr 1
  ring

/-- [proved-derived; formal-checked] The placed hole's length is the owner's `cantorGap`. -/
theorem cantorGap_eq_cantorLength (w : List Hand) : (cantorGap w : ℝ) = cantorLength w.length := by
  rw [cantor_gap_length, cantorLength]
  push_cast
  rfl

/-- [proved-derived; formal-checked] **The string of the complement is `cantorString`**: the hole at `⟨n, i⟩`
has length `cantorString ⟨n, i⟩`. -/
theorem volume_holeAt (p : Σ n : ℕ, Fin (2 ^ n)) : volume (holeAt p) = ENNReal.ofReal (cantorString p) := by
  rw [holeAt, volume_hole, length_wordAt]
  rfl

/-- [proved-derived; formal-checked] The placed holes of depth `n`, read in the owner's order, have the lengths of
`cantorString`'s depth-`n` holes. -/
theorem words_map_hole_length (n : ℕ) :
    (words n).map (fun w => (volume (hole w)).toReal) = List.ofFn fun i : Fin (2 ^ n) => cantorString ⟨n, i⟩ := by
  rw [cantorString_depth]
  refine List.map_congr_left fun w hw => ?_
  rw [volume_hole, ENNReal.toReal_ofReal (cantorLength_pos _).le, cantorGap_eq_cantorLength]

/-- [proved-derived; formal-checked] The holes, indexed as `cantorString`, are pairwise disjoint. -/
theorem pairwise_disjoint_holeAt : Pairwise fun p q => Disjoint (holeAt p) (holeAt q) :=
  fun _ _ hpq => pairwise_disjoint_hole fun h => hpq (wordAt_bijective.1 h)

/-- [proved-derived; formal-checked] The holes, indexed as `cantorString`, are all the holes. -/
theorem iUnion_holeAt : ⋃ p, holeAt p = ⋃ w : List Hand, hole w :=
  wordAt_bijective.2.iUnion_comp hole

/-- [proved-standard; formal-checked] `Σ_j ℓ_j = 1` for the Cantor string as a family. -/
theorem tsum_cantorString : ∑' p, cantorString p = 1 := by
  rw [summable_cantorString.tsum_sigma, tsum_congr fun n => cantorString_fibre n fun x => x]
  exact cantor_total_length

/-- [proved-standard; formal-checked] **The complement has measure one**, by countable additivity over the holes. -/
theorem volume_unitInterval_diff_cantorSet : volume (Set.Icc (0 : ℝ) 1 \ cantorSet) = 1 := by
  rw [unitInterval_diff_cantorSet, ← iUnion_holeAt,
    measure_iUnion pairwise_disjoint_holeAt fun _ => measurableSet_Ioo]
  simp_rw [volume_holeAt]
  rw [← ENNReal.ofReal_tsum_of_nonneg (f := cantorString) (fun p => (cantorLength_pos _).le) summable_cantorString,
    tsum_cantorString, ENNReal.ofReal_one]

/-- [proved-standard; formal-checked] **The Cantor set is Lebesgue-null.** -/
theorem volume_cantorSet : volume cantorSet = 0 := by
  have h := measure_inter_add_sdiff (μ := volume) (Set.Icc (0 : ℝ) 1) isClosed_cantorSet.measurableSet
  rw [Set.inter_eq_right.2 cantorSet_subset_unitInterval, volume_unitInterval_diff_cantorSet, Real.volume_Icc,
    sub_zero, ENNReal.ofReal_one] at h
  exact (ENNReal.add_left_inj ENNReal.one_ne_top).1 (by rw [h, zero_add])

end Measure

/-! ## The spectral count: its Weyl term and its second term -/

section Spectrum

/-- [definition] **The Cantor string's spectral count** `N(x) = Σ_n 2^n ⌊x·3^(−(n+1))⌋₊`, summed over the depths
below `⌊x⌋₊`; every deeper term vanishes (`cantorCount_eq_sum`). -/
noncomputable def cantorCount (x : ℝ) : ℕ :=
  ∑ n ∈ Finset.range ⌊x⌋₊, 2 ^ n * ⌊x * cantorLength n⌋₊

/-- [proved-standard; formal-checked] A depth-`n` hole has no harmonic at or below `x` when `x < 3^(n+1)`. -/
theorem floor_mul_cantorLength_eq_zero {x : ℝ} {n : ℕ} (h : x < 3 ^ (n + 1)) :
    ⌊x * cantorLength n⌋₊ = 0 := by
  rw [Nat.floor_eq_zero, cantorLength, one_div_pow, mul_one_div, div_lt_one (by positivity)]
  exact h

/-- [proved-standard; formal-checked] `x < 3^(⌊x⌋₊ + 1)`: no hole of depth `⌊x⌋₊` or more is heard at `x`. -/
theorem lt_three_pow_floor_add_one (x : ℝ) : x < 3 ^ (⌊x⌋₊ + 1) := by
  have h1 := Nat.lt_floor_add_one x
  have h2 : ((⌊x⌋₊ + 1 : ℕ) : ℝ) < ((3 ^ (⌊x⌋₊ + 1) : ℕ) : ℝ) := by
    exact_mod_cast Nat.lt_pow_self (by norm_num : 1 < 3)
  push_cast at h2
  linarith

/-- [proved-standard; formal-checked] The depths from `m` on add nothing to the count when `x < 3^(m+1)`. -/
theorem sum_range_eq_of_le {x : ℝ} {m M : ℕ} (hm : x < 3 ^ (m + 1)) (hmM : m ≤ M) :
    ∑ n ∈ Finset.range M, 2 ^ n * ⌊x * cantorLength n⌋₊ =
      ∑ n ∈ Finset.range m, 2 ^ n * ⌊x * cantorLength n⌋₊ := by
  refine (Finset.sum_subset (Finset.range_subset_range.2 hmM) fun n _ hn => ?_).symm
  have hmn : m ≤ n := by simpa using hn
  rw [floor_mul_cantorLength_eq_zero (hm.trans_le (pow_le_pow_right₀ (by norm_num) (by omega))), mul_zero]

/-- [proved-derived; formal-checked] **The count is a finite sum at every depth that reaches `x`**: for any `m`
with `x < 3^(m+1)`, `N(x) = Σ_(n<m) 2^n ⌊x·3^(−(n+1))⌋₊`. -/
theorem cantorCount_eq_sum {x : ℝ} {m : ℕ} (hm : x < 3 ^ (m + 1)) :
    cantorCount x = ∑ n ∈ Finset.range m, 2 ^ n * ⌊x * cantorLength n⌋₊ := by
  rw [cantorCount, ← sum_range_eq_of_le (lt_three_pow_floor_add_one x) (le_max_left _ m),
    sum_range_eq_of_le hm (le_max_right ⌊x⌋₊ m)]

/-- [proved-derived; formal-checked] **The count is the owner's `spectralCount`** of the holes of depth below `m`,
for any `m` with `x < 3^(m+1)`. -/
theorem cantorCount_eq_spectralCount {x : ℝ} {m : ℕ} (hm : x < 3 ^ (m + 1)) :
    cantorCount x = spectralCount (cantorLongHoles m) cantorString x := by
  rw [cantorCount_eq_sum hm, spectralCount, cantorLongHoles, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp [cantorString, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-- [proved-derived; formal-checked] **The count is self-similar**: `N(3x) = 2N(x) + ⌊x⌋₊`. -/
theorem cantorCount_three_mul (x : ℝ) : cantorCount (3 * x) = 2 * cantorCount x + ⌊x⌋₊ := by
  have hm := lt_three_pow_floor_add_one x
  have hm3 : 3 * x < 3 ^ (⌊x⌋₊ + 1 + 1) := by
    rw [pow_succ]
    linarith
  rw [cantorCount_eq_sum hm3, cantorCount_eq_sum hm, Finset.sum_range_succ', Finset.mul_sum]
  have h0 : 3 * x * cantorLength 0 = x := by
    simp only [cantorLength]
    ring
  have hs : ∀ n, 3 * x * cantorLength (n + 1) = x * cantorLength n := by
    intro n
    simp only [cantorLength]
    ring
  simp only [hs, h0, pow_zero, one_mul]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- [proved-standard; formal-checked] The holes of depth below `k` have total length `1 − (2/3)^k`. -/
theorem sum_two_pow_mul_cantorLength (k : ℕ) :
    ∑ n ∈ Finset.range k, (2 : ℝ) ^ n * cantorLength n = 1 - (2 / 3) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih, two_pow_mul_cantorLength, pow_succ]
      ring

/-- [proved-derived; formal-checked] **The second term by depth**: for `x < 3^(m+1)`,
`x − N(x) = x(2/3)^m + Σ_(n<m) 2^n·{x·3^(−(n+1))}`, the deep holes' share plus the fractional parts. -/
theorem sub_cantorCount_eq {x : ℝ} {m : ℕ} (hm : x < 3 ^ (m + 1)) :
    x - cantorCount x = x * (2 / 3) ^ m +
      ∑ n ∈ Finset.range m, (2 : ℝ) ^ n * (x * cantorLength n - ⌊x * cantorLength n⌋₊) := by
  rw [cantorCount_eq_sum hm]
  push_cast
  simp only [mul_sub, Finset.sum_sub_distrib]
  have h : ∑ n ∈ Finset.range m, (2 : ℝ) ^ n * (x * cantorLength n) = x * (1 - (2 / 3) ^ m) := by
    rw [← sum_two_pow_mul_cantorLength, Finset.mul_sum]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [h]
  ring

/-- [proved-standard; formal-checked] `(3^k)^z = (3^z)^k`. -/
theorem three_pow_rpow (k : ℕ) (z : ℝ) : ((3 : ℝ) ^ k) ^ z = ((3 : ℝ) ^ z) ^ k := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm, Real.rpow_mul (by norm_num),
    Real.rpow_natCast]

/-- [proved-standard; formal-checked] **The Weyl term bounds the count**: `N(x) ≤ x` for `x ≥ 0`, the total
length being one. -/
theorem cantorCount_le {x : ℝ} (hx : 0 ≤ x) : (cantorCount x : ℝ) ≤ x := by
  have h := sub_cantorCount_eq (lt_three_pow_floor_add_one x)
  have hfr : 0 ≤ ∑ n ∈ Finset.range ⌊x⌋₊, (2 : ℝ) ^ n * (x * cantorLength n - ⌊x * cantorLength n⌋₊) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity)
      (sub_nonneg.2 (Nat.floor_le (mul_nonneg hx (cantorLength_pos n).le)))
  have : 0 ≤ x * (2 / 3 : ℝ) ^ ⌊x⌋₊ := by positivity
  linarith

/-- [proved-standard; formal-checked] **The second term from below**: `x^D ≤ x − N(x)` for `x ≥ 1`. -/
theorem rpow_cantorDim_le_sub_cantorCount {x : ℝ} (hx : 1 ≤ x) : x ^ cantorDim ≤ x - cantorCount x := by
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 3)
  have hx0 : 0 < x := by linarith
  rw [sub_cantorCount_eq hk2]
  have hfr : 0 ≤ ∑ n ∈ Finset.range k, (2 : ℝ) ^ n * (x * cantorLength n - ⌊x * cantorLength n⌋₊) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (by positivity)
      (sub_nonneg.2 (Nat.floor_le (mul_nonneg hx0.le (cantorLength_pos n).le)))
  have h1 : x ^ (cantorDim - 1) ≤ ((3 : ℝ) ^ k) ^ (cantorDim - 1) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hk1 (by linarith [cantorDim_mem.2])
  have h2 : ((3 : ℝ) ^ k) ^ (cantorDim - 1) = (2 / 3) ^ k := by
    rw [three_pow_rpow, Real.rpow_sub_one (by norm_num), three_rpow_cantorDim]
  have h3 : x ^ cantorDim = x * x ^ (cantorDim - 1) := by
    rw [Real.rpow_sub_one hx0.ne']
    field_simp
  rw [h2] at h1
  have := mul_le_mul_of_nonneg_left h1 hx0.le
  linarith

/-- [proved-standard; formal-checked] **The second term from above**: `x − N(x) < 2x^D` for `x ≥ 1`, from the band
profile's bound `g(c) ≤ 2^(2−D)` (`bandProfile_le`) at `c = 3^k/x`. -/
theorem sub_cantorCount_lt {x : ℝ} (hx : 1 ≤ x) : x - cantorCount x < 2 * x ^ cantorDim := by
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near hx (by norm_num : (1 : ℝ) < 3)
  have hx0 : 0 < x := by linarith
  rw [sub_cantorCount_eq hk2]
  have hfr : ∑ n ∈ Finset.range k, (2 : ℝ) ^ n * (x * cantorLength n - ⌊x * cantorLength n⌋₊) < 2 ^ k := by
    calc _ ≤ ∑ n ∈ Finset.range k, (2 : ℝ) ^ n := Finset.sum_le_sum fun n _ => by
            have h := Nat.lt_floor_add_one (x * cantorLength n)
            have h2 : (0 : ℝ) < 2 ^ n := by positivity
            nlinarith
      _ < 2 ^ k := by
            rw [geom_sum_eq (by norm_num : (2 : ℝ) ≠ 1)]
            norm_num
  obtain ⟨c, hc⟩ : ∃ c, c = (3 : ℝ) ^ k / x := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : 1 / 3 ≤ c := by
    rw [hc, le_div_iff₀ hx0]
    rw [pow_succ] at hk2
    linarith
  have hc2 : c ≤ 1 := by
    rw [hc, div_le_one hx0]
    exact hk1
  have hprof : c ^ (cantorDim - 1) + c ^ cantorDim ≤ 2 := by
    have h := bandProfile_le hc1 hc2
    rw [bandProfile_eq hc0, show (2 : ℝ) - cantorDim = 1 + (1 - cantorDim) by ring,
      Real.rpow_add (by norm_num), Real.rpow_one] at h
    have h2 : (0 : ℝ) < 2 ^ (1 - cantorDim) := by positivity
    nlinarith
  have hxD : 0 < x ^ cantorDim := Real.rpow_pos_of_pos hx0 _
  have hcD : c ^ cantorDim = 2 ^ k / x ^ cantorDim := by
    rw [hc, Real.div_rpow (by positivity) hx0.le, three_pow_rpow, three_rpow_cantorDim]
  have hcD1 : c ^ (cantorDim - 1) = c ^ cantorDim / c := Real.rpow_sub_one hc0.ne' _
  have hx0' : x ≠ 0 := hx0.ne'
  have hxD' : x ^ cantorDim ≠ 0 := hxD.ne'
  have hid : x * (2 / 3) ^ k + 2 ^ k = x ^ cantorDim * (c ^ (cantorDim - 1) + c ^ cantorDim) := by
    rw [hcD1, hcD, hc, div_pow]
    field_simp
  have := mul_le_mul_of_nonneg_left hprof hxD.le
  linarith

/-- [definition] **The normalized second term** `R(x) = (x − N(x))/x^D`. -/
noncomputable def spectralRatio (x : ℝ) : ℝ := (x - cantorCount x) / x ^ cantorDim

/-- [proved-standard; formal-checked] **The second term is of order `x^D`**: `1 ≤ R(x) < 2` for `x ≥ 1`. -/
theorem spectralRatio_mem {x : ℝ} (hx : 1 ≤ x) : 1 ≤ spectralRatio x ∧ spectralRatio x < 2 := by
  have hxD : 0 < x ^ cantorDim := Real.rpow_pos_of_pos (by linarith) _
  rw [spectralRatio, le_div_iff₀ hxD, div_lt_iff₀ hxD, one_mul]
  exact ⟨rpow_cantorDim_le_sub_cantorCount hx, sub_cantorCount_lt hx⟩

/-- [proved-standard; formal-checked] **The Weyl law**: `N(x)/x → 1` as `x → ∞`. -/
theorem tendsto_cantorCount_div : Tendsto (fun x => (cantorCount x : ℝ) / x) atTop (𝓝 1) := by
  have h0 : Tendsto (fun x : ℝ => x ^ (cantorDim - 1)) atTop (𝓝 0) := by
    have := tendsto_rpow_neg_atTop (by linarith [cantorDim_mem.2] : 0 < 1 - cantorDim)
    rwa [neg_sub] at this
  have hlim : Tendsto (fun x : ℝ => 1 - 2 * x ^ (cantorDim - 1)) atTop (𝓝 1) := by
    simpa using (h0.const_mul 2).const_sub 1
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlim tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    have h := sub_cantorCount_lt hx
    have h3 : x ^ cantorDim = x * x ^ (cantorDim - 1) := by
      rw [Real.rpow_sub_one hx0.ne']
      field_simp
    have h4 : (1 - 2 * x ^ (cantorDim - 1)) * x = x - 2 * (x * x ^ (cantorDim - 1)) := by ring
    rw [le_div_iff₀ hx0, h4]
    linarith
  · filter_upwards [eventually_ge_atTop 1] with x hx
    have hx0 : 0 < x := by linarith
    rw [div_le_one hx0]
    exact cantorCount_le hx0.le

/-- [proved-derived; formal-checked] **One winding up the scale**: `R(3x) = R(x) + (x − ⌊x⌋₊)/(2x^D)` for
`x ≥ 0`. -/
theorem spectralRatio_three_mul {x : ℝ} (hx : 0 ≤ x) :
    spectralRatio (3 * x) = spectralRatio x + (x - ⌊x⌋₊) / (2 * x ^ cantorDim) := by
  rw [spectralRatio, spectralRatio, cantorCount_three_mul, Real.mul_rpow (by norm_num) hx,
    three_rpow_cantorDim]
  push_cast
  rw [show 3 * x - (2 * (cantorCount x : ℝ) + ⌊x⌋₊) = 2 * (x - cantorCount x) + (x - ⌊x⌋₊) by ring,
    add_div, mul_div_mul_left _ _ two_ne_zero]

/-- [proved-derived; formal-checked] **On the natural numbers the ratio is invariant under `x ↦ 3x`**. -/
theorem spectralRatio_three_mul_natCast (n : ℕ) : spectralRatio (3 * n) = spectralRatio n := by
  rw [spectralRatio_three_mul (Nat.cast_nonneg n), Nat.floor_natCast, sub_self, zero_div, add_zero]

/-- [proved-derived; formal-checked] `N(x) = 0` for `x < 3`: the largest hole, `1/3` long, first sounds at `3`. -/
theorem cantorCount_eq_zero {x : ℝ} (hx : x < 3) : cantorCount x = 0 := by
  rw [cantorCount_eq_sum (m := 0) (by simpa using hx)]
  rfl

/-- [proved-derived; formal-checked] `N(3^k) = 3^k − 2^k`, by the scaling law from `N(1) = 0`. -/
theorem cantorCount_three_pow (k : ℕ) : (cantorCount ((3 : ℝ) ^ k) : ℝ) = 3 ^ k - 2 ^ k := by
  induction k with
  | zero =>
      rw [pow_zero, cantorCount_eq_zero (by norm_num)]
      norm_num
  | succ k ih =>
      have hf : ⌊(3 : ℝ) ^ k⌋₊ = 3 ^ k := by
        rw [show (3 : ℝ) ^ k = ((3 ^ k : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]
      rw [pow_succ', cantorCount_three_mul, hf]
      push_cast
      rw [ih]
      ring

/-- [proved-derived; formal-checked] `N(2·3^k) = 2·3^k − 2^(k+1)`, by the scaling law from `N(2) = 0`. -/
theorem cantorCount_two_mul_three_pow (k : ℕ) :
    (cantorCount (2 * (3 : ℝ) ^ k) : ℝ) = 2 * 3 ^ k - 2 ^ (k + 1) := by
  induction k with
  | zero =>
      rw [pow_zero, mul_one, cantorCount_eq_zero (by norm_num)]
      norm_num
  | succ k ih =>
      have hf : ⌊2 * (3 : ℝ) ^ k⌋₊ = 2 * 3 ^ k := by
        rw [show 2 * (3 : ℝ) ^ k = ((2 * 3 ^ k : ℕ) : ℝ) by push_cast; rfl, Nat.floor_natCast]
      rw [pow_succ', show (2 : ℝ) * (3 * 3 ^ k) = 3 * (2 * 3 ^ k) by ring, cantorCount_three_mul, hf]
      push_cast
      rw [ih]
      ring

/-- [proved-derived; formal-checked] `R(3^k) = 1`: `N(3^k) = 3^k − 2^k`. -/
theorem spectralRatio_three_pow (k : ℕ) : spectralRatio ((3 : ℝ) ^ k) = 1 := by
  induction k with
  | zero =>
      rw [pow_zero, spectralRatio, cantorCount_eq_zero (by norm_num), Real.one_rpow]
      norm_num
  | succ k ih =>
      have h := spectralRatio_three_mul_natCast (3 ^ k)
      push_cast at h
      rw [pow_succ', h, ih]

/-- [proved-derived; formal-checked] `R(2·3^k) = 2^(1−D)`: `N(2·3^k) = 2·3^k − 2^(k+1)`. -/
theorem spectralRatio_two_mul_three_pow (k : ℕ) :
    spectralRatio (2 * (3 : ℝ) ^ k) = 2 ^ (1 - cantorDim) := by
  induction k with
  | zero =>
      rw [pow_zero, mul_one, spectralRatio, cantorCount_eq_zero (by norm_num), Real.rpow_sub (by norm_num),
        Real.rpow_one]
      simp
  | succ k ih =>
      have h := spectralRatio_three_mul_natCast (2 * 3 ^ k)
      push_cast at h
      rw [pow_succ', show (2 : ℝ) * (3 * 3 ^ k) = 3 * (2 * 3 ^ k) by ring, h, ih]

/-- [proved-standard; formal-checked] `2^(1−D) > 1`, so the two values differ. -/
theorem one_lt_two_rpow_one_sub_cantorDim : 1 < (2 : ℝ) ^ (1 - cantorDim) :=
  Real.one_lt_rpow (by norm_num) (by linarith [cantorDim_mem.2])

/-- [proved-standard; formal-checked] **The second term oscillates**: `R(x)` has no limit as `x → ∞`. -/
theorem spectralRatio_not_tendsto : ¬ ∃ L, Tendsto spectralRatio atTop (𝓝 L) := by
  rintro ⟨L, hL⟩
  have h3 : Tendsto (fun k : ℕ => (3 : ℝ) ^ k) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have e1 : L = 1 := by
    refine tendsto_nhds_unique (hL.comp h3) ?_
    simp only [Function.comp_def, spectralRatio_three_pow]
    exact tendsto_const_nhds
  have e2 : L = 2 ^ (1 - cantorDim) := by
    refine tendsto_nhds_unique (hL.comp (h3.const_mul_atTop (by norm_num : (0 : ℝ) < 2))) ?_
    simp only [Function.comp_def, spectralRatio_two_mul_three_pow]
    exact tendsto_const_nhds
  have h := one_lt_two_rpow_one_sub_cantorDim
  rw [← e2, e1] at h
  exact lt_irrefl _ h

/-- [proved-standard; formal-checked] **Both counts of the Cantor string oscillate**: the normalized tube has no
limit at `0⁺` (`normalizedTube_not_tendsto`), and the normalized second term of the spectral count has none at `∞`. -/
theorem cantorString_counts_oscillate :
    (¬ ∃ M, Tendsto normalizedTube (𝓝[>] 0) (𝓝 M)) ∧ ¬ ∃ L, Tendsto spectralRatio atTop (𝓝 L) :=
  ⟨normalizedTube_not_tendsto, spectralRatio_not_tendsto⟩

end Spectrum

/-! ## The tube as a Lebesgue measure -/

section InnerTube

/-- [proved-derived; formal-checked] **In a hole the distance to the Cantor set is the distance to the nearer
end**: for `x ∈ (a, b) = hole(w)`, `infDist x C = min(x − a, b − x)`, both ends lying in `C`. -/
theorem infDist_cantorSet_of_mem_hole {w : List Hand} {x : ℝ} (hx : x ∈ hole w) :
    Metric.infDist x cantorSet = min (x - (cellLower w + (1 / 3 : ℝ) ^ (w.length + 1)))
      (cellLower w + 2 * (1 / 3 : ℝ) ^ (w.length + 1) - x) := by
  obtain ⟨ha, hb⟩ := hole_ends_mem_cantorSet w
  have hx' := hx
  simp only [hole, Set.mem_Ioo] at hx'
  apply le_antisymm
  · refine le_min ?_ ?_
    · have h := Metric.infDist_le_dist_of_mem (x := x) ha
      rwa [Real.dist_eq, abs_of_pos (sub_pos.2 hx'.1)] at h
    · have h := Metric.infDist_le_dist_of_mem (x := x) hb
      rwa [Real.dist_eq, abs_of_neg (sub_neg.2 hx'.2), neg_sub] at h
  · rw [Metric.le_infDist ⟨_, ha⟩]
    intro y hy
    have hy' : y ∉ hole w := fun h => Set.disjoint_left.1 (disjoint_hole_cantorSet w) h hy
    simp only [hole, Set.mem_Ioo, not_and_or, not_lt] at hy'
    rw [Real.dist_eq]
    rcases hy' with h | h
    · exact (min_le_left _ _).trans ((by linarith : x - (cellLower w + (1 / 3 : ℝ) ^ (w.length + 1)) ≤ x - y).trans
        (le_abs_self _))
    · refine (min_le_right _ _).trans ((by linarith : cellLower w + 2 * (1 / 3 : ℝ) ^ (w.length + 1) - x ≤ y - x).trans
        ?_)
      rw [abs_sub_comm]
      exact le_abs_self _

/-- [proved-derived; formal-checked] One hole's inner tube is its two boundary layers: `min(2ε, 3^(−(n+1)))`. -/
theorem volume_hole_innerTube (w : List Hand) {ε : ℝ} (hε : 0 < ε) :
    volume {x ∈ hole w | Metric.infDist x cantorSet < ε} =
      ENNReal.ofReal (min (2 * ε) (cantorLength w.length)) := by
  have hset : {x ∈ hole w | Metric.infDist x cantorSet < ε} =
      {x ∈ Set.Ioo (cellLower w + (1 / 3 : ℝ) ^ (w.length + 1)) (cellLower w + 2 * (1 / 3 : ℝ) ^ (w.length + 1)) |
        x - (cellLower w + (1 / 3 : ℝ) ^ (w.length + 1)) < ε ∨
          cellLower w + 2 * (1 / 3 : ℝ) ^ (w.length + 1) - x < ε} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hx, hd⟩
      rw [infDist_cantorSet_of_mem_hole hx, min_lt_iff] at hd
      exact ⟨hx, hd⟩
    · rintro ⟨hx, hd⟩
      refine ⟨hx, ?_⟩
      rw [infDist_cantorSet_of_mem_hole hx, min_lt_iff]
      exact hd
  rw [hset, volume_hole_tube hε, cantorLength]
  congr 2
  ring

/-- [proved-standard; formal-checked] **The string's tube is the measure of the inner `ε`-neighbourhood**: for
`ε > 0`, `vol{x ∈ [0, 1] \ C : infDist(x, C) < ε} = V(ε) = Σ_n 2^n min(2ε, 3^(−(n+1)))`. -/
theorem volume_innerTube {ε : ℝ} (hε : 0 < ε) :
    volume {x ∈ Set.Icc 0 1 \ cantorSet | Metric.infDist x cantorSet < ε} = ENNReal.ofReal (cantorTube ε) := by
  have hU : {x ∈ Set.Icc 0 1 \ cantorSet | Metric.infDist x cantorSet < ε} =
      ⋃ p, {x ∈ hole (wordAt p) | Metric.infDist x cantorSet < ε} := by
    rw [wordAt_bijective.2.iUnion_comp (fun w => {x ∈ hole w | Metric.infDist x cantorSet < ε}),
      unitInterval_diff_cantorSet]
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, exists_and_right]
  have hp : ∀ p : Σ n : ℕ, Fin (2 ^ n), volume {x ∈ hole (wordAt p) | Metric.infDist x cantorSet < ε} =
      ENNReal.ofReal (min (2 * ε) (cantorString p)) := fun p => by
    rw [volume_hole_innerTube _ hε, length_wordAt]
    rfl
  rw [hU, measure_iUnion (f := fun p => {x ∈ hole (wordAt p) | Metric.infDist x cantorSet < ε})
      (fun p q hpq => (pairwise_disjoint_holeAt hpq).mono (Set.sep_subset _ _) (Set.sep_subset _ _))
      fun p => measurableSet_Ioo.inter (isOpen_lt (Metric.continuous_infDist_pt _) continuous_const).measurableSet,
    tsum_congr hp, ← ENNReal.ofReal_tsum_of_nonneg (f := fun p => min (2 * ε) (cantorString p))
      (fun p => le_min (by linarith) (cantorLength_pos _).le)
      (summable_tube summable_cantorString (fun p => (cantorLength_pos _).le) hε.le),
    ← tubeVolume_cantorString hε.le]
  rfl

end InnerTube

end Holonics.Foundation.CantorStringSpectrum
