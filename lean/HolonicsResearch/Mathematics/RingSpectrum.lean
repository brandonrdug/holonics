import HolonicsResearch.Mathematics.OnePlaneRing
import HolonicsResearch.Mathematics.OrbitEnergy
import Mathlib.LinearAlgebra.Charpoly.ToMatrix
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# The ring's spectrum is its Galois orbits

The record `research/records/2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md`
(§3 and owed (k)) couples the cells of the ring `ℤ/m` to their neighbours and reads the cycle
Laplacian's spectrum one Galois orbit of colours at a time. This file proves it.

[proved-standard; formal-checked] What is proved.

1. **The colours diagonalize the ring** (`dft_cycleLaplacian`, `charpoly_cycleLaplacian`). The
   cycle Laplacian `(L v)(x) = 2v(x) − v(x + 1) − v(x − 1)` is carried by the discrete Fourier
   transform to multiplication by the squared gaps `|1 − ψ(k)|² = 2 − ψ(k) − ψ(−k)`, so
   `det(x − L_m) = ∏_k (x − (2 − ψ(k) − ψ(−k)))`. For `m = 1` the one cell carries a loop and for
   `m = 2` the two cells carry two edges; the statements hold for every `m ≥ 1`.
2. **One factor per orbit** (`prod_colours`, `orbit_factor`, `charpoly_cycleLaplacian_orbits`). The
   colours of order `d ∣ m` are the primitive `d`-th roots of unity. For `d ≥ 3` none is real, the
   mirror `ζ ↦ ζ⁻¹ = ζ̄` exchanges the upper and the lower half, and the orbit's factor is the square
   of `ψ_d(x) = ∏_(Im ζ > 0) ((2 − ζ − ζ⁻¹) − x)`:
   `det(x − L_m) = x · (x − 4)^[2 ∣ m] · ∏_(d ∣ m, d ≥ 3) ψ_d(x)²`.
3. **The orbit's polynomial** (`orbitPoly_eq`, `natDegree_orbitMinpoly`, `orbitPoly_eval_zero`,
   `orbitMinpoly_eq_minpoly`). `ψ_d = (−1)^(φ(d)/2) · ψ̃_d` with `ψ̃_d` monic of degree `φ(d)/2`;
   `ψ_d(0) = Φ_d(1)`, so an orbit's squared gaps multiply to its prime or to `1`
   (`OrbitEnergy.cyclotomic_eval_one`); and `ψ̃_d` is the minimal polynomial over `ℚ` of
   `2 − ζ − ζ⁻¹` for every colour `ζ` of order `d`. The proof embeds `ℚ[X]/Φ_d` into `ℂ` once per
   colour, so all the colours' squared gaps share one minimal polynomial, and bounds its degree by
   the tower `ℚ ⊆ ℚ(2 − θ − θ⁻¹) ⊊ ℚ(θ)`: the middle field is real under every embedding, and
   `θ` is not.
4. **The nonzero eigenvalues multiply to `m²`** (`prod_gapSq_ne_zero`): the gaps off colour `0`
   multiply to `m` (`OrbitEnergy.orbit_energies_multiply_to_ring`), and the mirror pairs each with
   its conjugate.

Not proved here: Kirchhoff's matrix-tree theorem, which reads `m² / m = m` as the ring's number of
spanning trees, is not in Mathlib; the count `m` itself is the cycle minus one of its `m` edges. The
worked cases `ψ_7 = −x³ + 7x² − 14x + 7` and `ψ_9 = −x³ + 6x² − 9x + 3` stay checked, not formal.

Consumers: the atlas row `colour.ring-spectrum-orbits`.
-/

open Polynomial ZMod Complex
open scoped ComplexConjugate Nat

namespace Holonics.Mathematics.RingSpectrum

open Holonics.Mathematics.OnePlaneRing Holonics.Mathematics.OrbitEnergy

/-- [definition] The cycle Laplacian of the ring `ℤ/m`: each cell coupled to its two neighbours,
`(L v)(x) = 2v(x) − v(x + 1) − v(x − 1)`. -/
def cycleLaplacian (m : ℕ) : Matrix (ZMod m) (ZMod m) ℤ := fun i j =>
  (if j = i then 2 else 0) - (if j = i + 1 then 1 else 0) - (if j = i - 1 then 1 else 0)

variable {m : ℕ} [NeZero m]

/-- [definition] The squared gap of colour `k`, `|1 − ψ(k)|² = 2 − ψ(k) − ψ(−k)`. -/
noncomputable def gapSq (k : ZMod m) : ℂ := 2 - stdAddChar k - stdAddChar (-k)

theorem mulVec_cycleLaplacian (v : ZMod m → ℂ) (i : ZMod m) :
    ((cycleLaplacian m).map (Int.castRingHom ℂ)).mulVec v i = 2 * v i - v (i + 1) - v (i - 1) := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, cycleLaplacian, eq_intCast, Int.cast_sub,
    Int.cast_ite, Int.cast_ofNat, Int.cast_one, Int.cast_zero, sub_mul, ite_mul, zero_mul,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul]

/-- [proved-standard; formal-checked] **The colours diagonalize the ring**: the Fourier transform
carries `L` to multiplication by the squared gaps. -/
theorem dft_cycleLaplacian (v : ZMod m → ℂ) (k : ZMod m) :
    𝓕 (((cycleLaplacian m).map (Int.castRingHom ℂ)).mulVec v) k = gapSq k * 𝓕 v k := by
  have hv : ((cycleLaplacian m).map (Int.castRingHom ℂ)).mulVec v =
      (2 : ℂ) • v - (fun x => v (x + 1)) - (fun x => v (x + -1)) := by
    funext i
    rw [mulVec_cycleLaplacian]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [← sub_eq_add_neg]
  rw [hv, map_sub, map_sub, _root_.map_smul, Pi.sub_apply, Pi.sub_apply, Pi.smul_apply, dft_comp_add,
    dft_comp_add, one_mul, neg_one_mul, gapSq, smul_eq_mul, smul_eq_mul, smul_eq_mul]
  ring

/-- [proved-standard; formal-checked] **The ring's characteristic polynomial**:
`det(x − L_m) = ∏_k (x − (2 − ψ(k) − ψ(−k)))`. -/
theorem charpoly_cycleLaplacian :
    (cycleLaplacian m).charpoly.map (Int.castRingHom ℂ) = ∏ k : ZMod m, (X - C (gapSq k)) := by
  rw [← Matrix.charpoly_map, ← Matrix.charpoly_diagonal, ← Matrix.charpoly_toLin',
    ← Matrix.charpoly_toLin' (Matrix.diagonal gapSq),
    ← LinearEquiv.charpoly_conj (dft (N := m) (E := ℂ))]
  congr 1
  refine LinearMap.ext fun w => ?_
  funext k
  rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, Matrix.toLin'_apply,
    Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  change 𝓕 (((cycleLaplacian m).map (Int.castRingHom ℂ)).mulVec (dft.symm w)) k = _
  rw [dft_cycleLaplacian, LinearEquiv.apply_symm_apply]

/-- [proved-standard; formal-checked] **The colours are the roots of unity, orbit by orbit**: the
colours `ψ(k)`, `k ∈ ℤ/m`, are the `m`-th roots of unity, which are the primitive `d`-th roots for
`d ∣ m`. -/
theorem prod_colours {M : Type*} [CommMonoid M] (f : ℂ → M) :
    ∏ k : ZMod m, f (stdAddChar k) = ∏ d ∈ m.divisors, ∏ ζ ∈ primitiveRoots d ℂ, f ζ := by
  classical
  have hm : 0 < m := NeZero.pos m
  rw [← Finset.prod_biUnion (fun i _ j _ hij => IsPrimitiveRoot.disjoint hij),
    ← IsPrimitiveRoot.nthRoots_one_eq_biUnion_primitiveRoots]
  have himg : Finset.univ.image (fun k : ZMod m => (stdAddChar k : ℂ)) =
      Polynomial.nthRootsFinset m (1 : ℂ) := by
    refine Finset.eq_of_subset_of_card_le (fun z hz => ?_) ?_
    · obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
      rw [Polynomial.mem_nthRootsFinset hm, ← AddChar.map_nsmul_eq_pow, nsmul_eq_mul,
        ZMod.natCast_self, zero_mul, AddChar.map_zero_eq_one]
    · rw [(Complex.isPrimitiveRoot_exp m (NeZero.ne m)).card_nthRootsFinset,
        Finset.card_image_of_injective _ injective_stdAddChar, Finset.card_univ, ZMod.card]
  rw [← himg, Finset.prod_image (fun a _ b _ h => injective_stdAddChar h)]

section Orbit

/-- [definition] The colours of order `d` in the upper half plane. -/
noncomputable def upper (d : ℕ) : Finset ℂ := (primitiveRoots d ℂ).filter (fun ζ => 0 < ζ.im)

theorem inv_eq_conj_of_mem {d : ℕ} (hd : 0 < d) {ζ : ℂ} (hζ : ζ ∈ primitiveRoots d ℂ) :
    ζ⁻¹ = conj ζ :=
  Complex.inv_eq_conj (((mem_primitiveRoots hd).mp hζ).norm'_eq_one hd.ne')

/-- [proved-standard; formal-checked] No colour of order `d ≥ 3` is real. -/
theorem im_ne_zero {d : ℕ} (hd : 3 ≤ d) {ζ : ℂ} (hζ : ζ ∈ primitiveRoots d ℂ) : ζ.im ≠ 0 := by
  intro h
  have hd0 : 0 < d := by omega
  have hp := (mem_primitiveRoots hd0).mp hζ
  have hc : conj ζ = ζ := Complex.conj_eq_iff_im.mpr h
  have hne : ζ ≠ 0 := hp.ne_zero hd0.ne'
  have h2 : ζ ^ 2 = 1 := by
    have : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hne
    rw [inv_eq_conj_of_mem hd0 hζ, hc] at this
    rw [sq, this]
  have := Nat.le_of_dvd two_pos (hp.dvd_of_pow_eq_one 2 h2)
  omega

theorem inv_mem_lower {d : ℕ} (hd : 0 < d) {ζ : ℂ} (hζ : ζ ∈ upper d) :
    ζ⁻¹ ∈ (primitiveRoots d ℂ).filter (fun ζ => ¬ 0 < ζ.im) := by
  rw [upper, Finset.mem_filter] at hζ
  have hinv := ((mem_primitiveRoots hd).mp hζ.1).inv
  rw [Finset.mem_filter, mem_primitiveRoots hd]
  refine ⟨hinv, ?_⟩
  rw [inv_eq_conj_of_mem hd hζ.1, Complex.conj_im]
  linarith [hζ.2]


theorem inv_mem_upper {d : ℕ} (hd : 3 ≤ d) {ζ : ℂ}
    (hζ : ζ ∈ (primitiveRoots d ℂ).filter (fun ζ => ¬ 0 < ζ.im)) : ζ⁻¹ ∈ upper d := by
  have hd0 : 0 < d := by omega
  rw [Finset.mem_filter] at hζ
  have hinv := ((mem_primitiveRoots hd0).mp hζ.1).inv
  rw [upper, Finset.mem_filter, mem_primitiveRoots hd0]
  refine ⟨hinv, ?_⟩
  rw [inv_eq_conj_of_mem hd0 hζ.1, Complex.conj_im]
  have h1 := im_ne_zero hd hζ.1
  have h2 : ζ.im < 0 := lt_of_le_of_ne (not_lt.mp hζ.2) h1
  linarith

/-- [proved-standard; formal-checked] **The mirror pairs the halves**: for `d ≥ 3`, a product over
the colours of order `d` is the product over the upper half of `f(ζ)` and of `f(ζ⁻¹)`. -/
theorem prod_split {M : Type*} [CommMonoid M] {d : ℕ} (hd : 3 ≤ d) (f : ℂ → M) :
    ∏ ζ ∈ primitiveRoots d ℂ, f ζ = (∏ ζ ∈ upper d, f ζ) * ∏ ζ ∈ upper d, f ζ⁻¹ := by
  have hd0 : 0 < d := by omega
  rw [← Finset.prod_filter_mul_prod_filter_not (primitiveRoots d ℂ) (fun ζ => 0 < ζ.im)]
  congr 1
  symm
  exact Finset.prod_nbij' (fun ζ => ζ⁻¹) (fun ζ => ζ⁻¹) (fun ζ hζ => inv_mem_lower hd0 hζ)
    (fun ζ hζ => inv_mem_upper hd hζ) (fun ζ _ => inv_inv ζ) (fun ζ _ => inv_inv ζ)
    (fun ζ _ => rfl)

/-- [proved-standard; formal-checked] Half the colours of order `d ≥ 3` lie in the upper half. -/
theorem card_upper {d : ℕ} (hd : 3 ≤ d) : 2 * (upper d).card = φ d := by
  have hd0 : 0 < d := by omega
  have hlow : ((primitiveRoots d ℂ).filter (fun ζ => ¬ 0 < ζ.im)).card = (upper d).card := by
    symm
    exact Finset.card_nbij' (fun ζ => ζ⁻¹) (fun ζ => ζ⁻¹) (fun ζ hζ => inv_mem_lower hd0 hζ)
      (fun ζ hζ => inv_mem_upper hd hζ) (fun ζ _ => inv_inv ζ) (fun ζ _ => inv_inv ζ)
  have hsplit := Finset.card_filter_add_card_filter_not (s := primitiveRoots d ℂ)
    (fun ζ : ℂ => 0 < ζ.im)
  rw [hlow, Complex.card_primitiveRoots d] at hsplit
  unfold upper at hsplit ⊢
  omega

/-- [definition] The record's `ψ_d(x) = ∏_(Im ζ > 0) ((2 − ζ − ζ⁻¹) − x)`, signed so that
`ψ_d(0) = Φ_d(1)`. -/
noncomputable def orbitPoly (d : ℕ) : ℂ[X] := ∏ ζ ∈ upper d, (C (2 - ζ - ζ⁻¹) - X)

/-- [definition] Its monic form `ψ̃_d(x) = ∏_(Im ζ > 0) (x − (2 − ζ − ζ⁻¹))`. -/
noncomputable def orbitMinpoly (d : ℕ) : ℂ[X] := ∏ ζ ∈ upper d, (X - C (2 - ζ - ζ⁻¹))

theorem monic_orbitMinpoly (d : ℕ) : (orbitMinpoly d).Monic :=
  monic_prod_of_monic _ _ fun _ _ => monic_X_sub_C _

/-- [proved-standard; formal-checked] `ψ̃_d` has degree `φ(d)/2`. -/
theorem natDegree_orbitMinpoly {d : ℕ} (hd : 3 ≤ d) : (orbitMinpoly d).natDegree = φ d / 2 := by
  rw [orbitMinpoly, natDegree_prod_of_monic _ _ fun ζ _ => monic_X_sub_C _]
  simp only [natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
  have := card_upper hd
  omega

/-- [proved-standard; formal-checked] `ψ_d = (−1)^(φ(d)/2) · ψ̃_d`. -/
theorem orbitPoly_eq {d : ℕ} (hd : 3 ≤ d) : orbitPoly d = (-1) ^ (φ d / 2) * orbitMinpoly d := by
  have hc : φ d / 2 = (upper d).card := by have := card_upper hd; omega
  rw [orbitPoly, orbitMinpoly, hc, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun ζ _ => by ring

/-- [proved-standard; formal-checked] **One orbit, one squared factor**: for `d ≥ 3`,
`∏_(ζ of order d) (x − (2 − ζ − ζ⁻¹)) = ψ_d(x)²`. -/
theorem orbit_factor {d : ℕ} (hd : 3 ≤ d) :
    ∏ ζ ∈ primitiveRoots d ℂ, (X - C (2 - ζ - ζ⁻¹)) = orbitPoly d ^ 2 := by
  rw [prod_split hd, orbitPoly, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ζ _ => ?_
  rw [inv_inv, show (2 - ζ⁻¹ - ζ : ℂ) = 2 - ζ - ζ⁻¹ by ring]
  ring

/-- [proved-standard; formal-checked] **`ψ_d(0) = Φ_d(1)`**: an orbit's squared gaps multiply to
the product of its gaps, its prime or `1`. -/
theorem orbitPoly_eval_zero {d : ℕ} (hd : 3 ≤ d) :
    (orbitPoly d).eval 0 = (cyclotomic d ℂ).eval 1 := by
  have hd0 : 0 < d := by omega
  rw [← orbit_gap_product hd0, prod_split hd, orbitPoly, eval_prod, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun ζ hζ => ?_
  have hne : ζ ≠ 0 :=
    ((mem_primitiveRoots hd0).mp (Finset.mem_filter.mp hζ).1).ne_zero hd0.ne'
  have h := mul_inv_cancel₀ hne
  rw [eval_sub, eval_C, eval_X, sub_zero]
  linear_combination -h

theorem primitiveRoots_two : primitiveRoots 2 ℂ = {-1} := by
  have h := IsPrimitiveRoot.neg_one (R := ℂ) 0 (by norm_num)
  have hmem : (-1 : ℂ) ∈ primitiveRoots 2 ℂ := (mem_primitiveRoots two_pos).mpr h
  obtain ⟨a, ha⟩ := Finset.card_eq_one.mp
    ((Complex.card_primitiveRoots 2).trans Nat.totient_two)
  rw [ha, Finset.mem_singleton] at hmem
  rw [ha, hmem]

end Orbit

/-- [proved-standard; formal-checked] **The ring's spectrum is its Galois orbits**:
`det(x − L_m) = x · (x − 4)^[2 ∣ m] · ∏_(d ∣ m, d ≥ 3) ψ_d(x)²`. -/
theorem charpoly_cycleLaplacian_orbits :
    (cycleLaplacian m).charpoly.map (Int.castRingHom ℂ) =
      X * (X - C 4) ^ (if 2 ∣ m then 1 else 0) *
        ∏ d ∈ m.divisors.filter (3 ≤ ·), orbitPoly d ^ 2 := by
  classical
  have hg : ∀ k : ZMod m, gapSq k = 2 - stdAddChar k - (stdAddChar k)⁻¹ := fun k => by
    rw [gapSq, AddChar.map_neg_eq_inv]
  simp_rw [charpoly_cycleLaplacian, hg]
  rw [prod_colours (fun ζ => X - C (2 - ζ - ζ⁻¹)),
    ← Finset.prod_filter_mul_prod_filter_not m.divisors (fun d => 3 ≤ d), mul_comm]
  congr 1
  · have hm0 : m ≠ 0 := NeZero.ne m
    have hlow : m.divisors.filter (fun d => ¬ 3 ≤ d) = if 2 ∣ m then {1, 2} else {1} := by
      ext d
      simp only [Finset.mem_filter, Nat.mem_divisors, not_le]
      split_ifs with h2
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hdm, -⟩, hd3⟩
          interval_cases d
          · simp at hdm; exact absurd hdm hm0
          · left; rfl
          · right; rfl
        · rintro (rfl | rfl)
          · exact ⟨⟨one_dvd m, hm0⟩, by norm_num⟩
          · exact ⟨⟨h2, hm0⟩, by norm_num⟩
      · simp only [Finset.mem_singleton]
        constructor
        · rintro ⟨⟨hdm, -⟩, hd3⟩
          interval_cases d
          · simp at hdm; exact absurd hdm hm0
          · rfl
          · exact absurd hdm h2
        · rintro rfl
          exact ⟨⟨one_dvd m, hm0⟩, by norm_num⟩
    have h1 : ∏ ζ ∈ primitiveRoots 1 ℂ, (X - C (2 - ζ - ζ⁻¹)) = (X : ℂ[X]) := by
      rw [IsPrimitiveRoot.primitiveRoots_one, Finset.prod_singleton]
      norm_num
    have h2' : ∏ ζ ∈ primitiveRoots 2 ℂ, (X - C (2 - ζ - ζ⁻¹)) = (X - C 4 : ℂ[X]) := by
      rw [primitiveRoots_two, Finset.prod_singleton]
      norm_num
    rw [hlow]
    split_ifs with h2
    · rw [Finset.prod_insert (by norm_num), Finset.prod_singleton, h1, h2', pow_one]
    · rw [Finset.prod_singleton, h1, pow_zero, mul_one]
  · exact Finset.prod_congr rfl fun d hd => orbit_factor (Finset.mem_filter.mp hd).2

/-- [proved-standard; formal-checked] The gaps off colour `0` multiply to the ring's size:
`∏_(k ≠ 0) (1 − ψ(k)) = m`. -/
theorem prod_one_sub_colour :
    ∏ k ∈ Finset.univ.erase (0 : ZMod m), (1 - (stdAddChar k : ℂ)) = (m : ℂ) := by
  classical
  have hm : 0 < m := NeZero.pos m
  let f : ℂ → ℂ := fun ζ => if ζ = 1 then 1 else 1 - ζ
  have h1 : ∏ k : ZMod m, f (stdAddChar k) =
      ∏ k ∈ Finset.univ.erase (0 : ZMod m), (1 - (stdAddChar k : ℂ)) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (0 : ZMod m))]
    simp only [f, AddChar.map_zero_eq_one, if_true, one_mul]
    refine Finset.prod_congr rfl fun k hk => ?_
    have : (stdAddChar k : ℂ) ≠ 1 := by
      intro h
      apply (Finset.mem_erase.mp hk).1
      exact injective_stdAddChar (h.trans (AddChar.map_zero_eq_one _).symm)
    simp only [this, if_false]
  have hf1 : ∏ ζ ∈ primitiveRoots 1 ℂ, f ζ = 1 := by
    rw [IsPrimitiveRoot.primitiveRoots_one, Finset.prod_singleton]
    simp [f]
  rw [← h1, prod_colours f, ← Finset.prod_erase m.divisors hf1,
    ← orbit_energies_multiply_to_ring ℂ hm]
  refine Finset.prod_congr rfl fun d hd => ?_
  have hd1 : d ≠ 1 := (Finset.mem_erase.mp hd).1
  have hd0 : 0 < d := Nat.pos_of_mem_divisors (Finset.mem_erase.mp hd).2
  rw [← orbit_gap_product hd0]
  refine Finset.prod_congr rfl fun ζ hζ => ?_
  have : ζ ≠ 1 := by
    rintro rfl
    exact hd1 (IsPrimitiveRoot.one_left_iff.mp ((mem_primitiveRoots hd0).mp hζ))
  simp only [f, this, if_false]

/-- [proved-standard; formal-checked] **The nonzero eigenvalues multiply to `m²`**:
`∏_(k ≠ 0) (2 − ψ(k) − ψ(−k)) = m²`. -/
theorem prod_gapSq_ne_zero : ∏ k ∈ Finset.univ.erase (0 : ZMod m), gapSq k = (m : ℂ) ^ 2 := by
  have hfac : ∀ k : ZMod m, gapSq k = (1 - stdAddChar k) * (1 - stdAddChar (-k)) := fun k => by
    have h : (stdAddChar k : ℂ) * stdAddChar (-k) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    rw [gapSq]
    linear_combination -h
  simp_rw [hfac]
  rw [Finset.prod_mul_distrib, prod_one_sub_colour, sq]
  congr 1
  rw [← prod_one_sub_colour]
  exact Finset.prod_nbij' (fun k => -k) (fun k => -k)
    (fun k hk => Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (Finset.mem_erase.mp hk).1,
      Finset.mem_univ _⟩)
    (fun k hk => Finset.mem_erase.mpr ⟨neg_ne_zero.mpr (Finset.mem_erase.mp hk).1,
      Finset.mem_univ _⟩)
    (fun k _ => neg_neg k) (fun k _ => neg_neg k) (fun k _ => rfl)

section Minpoly

/-- [proved-standard; formal-checked] A colour's squared gap is real: `2 − ζ − ζ⁻¹ = 2 − 2 Re ζ`. -/
theorem gap_eq_ofReal {d : ℕ} (hd : 0 < d) {ζ : ℂ} (hζ : ζ ∈ primitiveRoots d ℂ) :
    (2 - ζ - ζ⁻¹ : ℂ) = ((2 - 2 * ζ.re : ℝ) : ℂ) := by
  rw [inv_eq_conj_of_mem hd hζ]
  apply Complex.ext <;> simp; ring

/-- [proved-standard; formal-checked] The colours of the upper half have distinct squared gaps. -/
theorem gap_injOn {d : ℕ} (hd : 0 < d) :
    Set.InjOn (fun ζ : ℂ => 2 - ζ - ζ⁻¹) (upper d : Set ℂ) := by
  intro ζ hζ ξ hξ h
  rw [Finset.mem_coe, upper, Finset.mem_filter] at hζ hξ
  simp only at h
  rw [gap_eq_ofReal hd hζ.1, gap_eq_ofReal hd hξ.1, Complex.ofReal_inj] at h
  have hre : ζ.re = ξ.re := by linarith
  have hn : ∀ z ∈ primitiveRoots d ℂ, z.re * z.re + z.im * z.im = 1 := fun z hz => by
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq,
      ((mem_primitiveRoots hd).mp hz).norm'_eq_one hd.ne', one_pow]
  have him : ζ.im * ζ.im = ξ.im * ξ.im := by
    have h1 := hn ζ hζ.1
    have h2 := hn ξ hξ.1
    rw [hre] at h1
    linarith
  exact Complex.ext hre ((mul_self_inj hζ.2.le hξ.2.le).mp him)

/-- [proved-standard; formal-checked] **`ψ̃_d` is the minimal polynomial** over `ℚ` of the squared
gap `2 − ζ − ζ⁻¹` of every colour `ζ` of order `d ≥ 3`. -/
theorem orbitMinpoly_eq_minpoly {d : ℕ} (hd : 3 ≤ d) {ζ : ℂ} (hζ : ζ ∈ primitiveRoots d ℂ) :
    orbitMinpoly d = (minpoly ℚ (2 - ζ - ζ⁻¹)).map (algebraMap ℚ ℂ) := by
  classical
  have hd0 : 0 < d := by omega
  have hirr : Irreducible (cyclotomic d ℚ) := cyclotomic.irreducible_rat hd0
  have : Fact (Irreducible (cyclotomic d ℚ)) := ⟨hirr⟩
  have hf0 : cyclotomic d ℚ ≠ 0 := hirr.ne_zero
  have : Module.Finite ℚ (AdjoinRoot (cyclotomic d ℚ)) := (AdjoinRoot.powerBasis hf0).finite
  let θ : AdjoinRoot (cyclotomic d ℚ) := AdjoinRoot.root (cyclotomic d ℚ)
  let lK : AdjoinRoot (cyclotomic d ℚ) := 2 - θ - θ⁻¹
  -- one embedding of `ℚ[X]/Φ_d` per colour
  have hroot : ∀ ξ ∈ primitiveRoots d ℂ,
      (cyclotomic d ℚ).eval₂ (Algebra.ofId ℚ ℂ : ℚ →+* ℂ) ξ = 0 := fun ξ hξ => by
    rw [show (Algebra.ofId ℚ ℂ : ℚ →+* ℂ) = algebraMap ℚ ℂ from rfl, ← eval_map,
      map_cyclotomic]
    exact ((mem_primitiveRoots hd0).mp hξ).isRoot_cyclotomic hd0
  let emb : ∀ ξ ∈ primitiveRoots d ℂ, AdjoinRoot (cyclotomic d ℚ) →ₐ[ℚ] ℂ := fun ξ hξ =>
    AdjoinRoot.liftAlgHom (cyclotomic d ℚ) (Algebra.ofId ℚ ℂ) ξ (hroot ξ hξ)
  have hθ : ∀ ξ (hξ : ξ ∈ primitiveRoots d ℂ), emb ξ hξ θ = ξ := fun ξ hξ =>
    AdjoinRoot.liftAlgHom_root _ _ _ _
  have hl : ∀ ξ (hξ : ξ ∈ primitiveRoots d ℂ), emb ξ hξ lK = 2 - ξ - ξ⁻¹ := fun ξ hξ => by
    simp only [lK, map_sub, map_inv₀, map_ofNat, hθ]
  -- every colour's squared gap has the minimal polynomial of `2 − θ − θ⁻¹`
  have key : ∀ ξ ∈ primitiveRoots d ℂ, minpoly ℚ (2 - ξ - ξ⁻¹) = minpoly ℚ lK := fun ξ hξ => by
    rw [← hl ξ hξ]
    exact minpoly.algHom_eq (emb ξ hξ) (emb ξ hξ : AdjoinRoot (cyclotomic d ℚ) →+* ℂ).injective lK
  rw [key ζ hζ]
  have hint : IsIntegral ℚ lK := Algebra.IsIntegral.isIntegral lK
  -- `ψ̃_d` divides the minimal polynomial: its roots are distinct roots of it
  have hdvd : orbitMinpoly d ∣ (minpoly ℚ lK).map (algebraMap ℚ ℂ) := by
    refine Finset.prod_dvd_of_coprime (fun ξ hξ η hη hne => ?_) (fun ξ hξ => ?_)
    · apply isCoprime_X_sub_C_of_isUnit_sub
      exact (sub_ne_zero.mpr fun h => hne (gap_injOn hd0 hξ hη h)).isUnit
    · rw [dvd_iff_isRoot, IsRoot, eval_map, ← aeval_def]
      have hξ' := (Finset.mem_filter.mp hξ).1
      rw [← key ξ hξ']
      exact minpoly.aeval ℚ _
  -- the degree is at most `φ(d)/2`: `ℚ(2 − θ − θ⁻¹)` is real under every embedding, `θ` is not
  have hdeg : 2 * (minpoly ℚ lK).natDegree ≤ φ d := by
    let F : IntermediateField ℚ (AdjoinRoot (cyclotomic d ℚ)) := IntermediateField.adjoin ℚ {lK}
    have hF : Module.finrank ℚ F = (minpoly ℚ lK).natDegree := IntermediateField.adjoin.finrank hint
    have hK : Module.finrank ℚ (AdjoinRoot (cyclotomic d ℚ)) = φ d := by
      rw [show Module.finrank ℚ (AdjoinRoot (cyclotomic d ℚ)) = (cyclotomic d ℚ).natDegree from
        finrank_quotient_span_eq_natDegree, natDegree_cyclotomic]
    have htower := Module.finrank_mul_finrank ℚ F (AdjoinRoot (cyclotomic d ℚ))
    have hne1 : Module.finrank F (AdjoinRoot (cyclotomic d ℚ)) ≠ 1 := by
      intro h1
      have htop := IntermediateField.finrank_eq_one_iff_eq_top.mp h1
      have hmem : θ ∈ F := htop ▸ IntermediateField.mem_top
      obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ θ).mp hmem
      have h := congrArg (emb ζ hζ) hrs
      rw [map_div₀, ← aeval_algHom_apply, ← aeval_algHom_apply, hl ζ hζ, hθ ζ hζ,
        gap_eq_ofReal hd0 hζ,
        show ((2 - 2 * ζ.re : ℝ) : ℂ) = algebraMap ℝ ℂ (2 - 2 * ζ.re) from rfl,
        aeval_algebraMap_apply, aeval_algebraMap_apply, ← map_div₀] at h
      apply im_ne_zero hd hζ
      rw [h]
      exact Complex.ofReal_im _
    have hpos : 0 < Module.finrank F (AdjoinRoot (cyclotomic d ℚ)) := Module.finrank_pos
    rw [hF, hK] at htower
    have h2 : 2 ≤ Module.finrank F (AdjoinRoot (cyclotomic d ℚ)) := by omega
    calc 2 * (minpoly ℚ lK).natDegree
        ≤ Module.finrank F (AdjoinRoot (cyclotomic d ℚ)) * (minpoly ℚ lK).natDegree :=
          Nat.mul_le_mul_right _ h2
      _ = φ d := by rw [mul_comm]; exact htower
  have hdeg' : ((minpoly ℚ lK).map (algebraMap ℚ ℂ)).natDegree ≤ (orbitMinpoly d).natDegree := by
    rw [natDegree_map, natDegree_orbitMinpoly hd]
    omega
  exact (eq_of_monic_of_dvd_of_natDegree_le (monic_orbitMinpoly d)
    ((minpoly.monic hint).map _) hdvd hdeg').symm

end Minpoly

end Holonics.Mathematics.RingSpectrum
