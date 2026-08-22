import Mathlib.NumberTheory.LSeries.HurwitzZetaEven
import Mathlib.NumberTheory.LSeries.HurwitzZetaOdd
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

/-!
# FiveTheta: the sign-minus-one theta function of the congruent-number curve at five

**The analytic deed of the rank-one campaign.**  The L-function of `y² = x³ − 25x` is
the quadratic twist by five of the Hecke L-series at one, and its theta function is the
`χ₅`-weighted Gaussian class sum

```text
θ₅(x)  =  Σ_{a ≡ 1 (4), t ∈ ℤ}  a·(−1)^t·χ₅(a² + 4t²)·exp(−π(a² + 4t²)·√2·x/20),
```

conductor `800 = 32·5²`.  This file constructs `θ₅` as a finite combination of fifty
shifted mathlib Hurwitz-kernel products and proves the twisted transformation law

* **`theFiveDuplicationIdentity`** — the level-five duplication: the fifty
  `sinKernel`–`cosKernel` products at scale `y` equal `−800` times the fifty
  `oddKernel`–`evenKernel` products at scale `800y`.  The engine is finite: the fifty
  phases collapse through the quadratic Gauss sum mod five (`theGaussEigenIdentity`,
  `Σ_{r,s} χ₅(r²−s²)·ζ^{ξr+ηs} = 5·χ₅(ξ²−η²)` — the twist character is a finite
  Fourier eigenfunction), and the lattice then folds through
  `(p,q) ↦ (p+q+1, p−q)` exactly as at one; **the sign of the functional equation is
  `χ₅(2) = −1`**, deposited by the fold `n² + m² = 2(a² + b²)`.
* **`theFiveThetaFunctionalEquation`** — `θ₅(1/x) = −x²·θ₅(x)`: weight two,
  **sign `−1`**, level 800.
* **`theCompletedLFunctionAtFiveIsEntire`**, **`theCompletedLFunctionalEquationAtFive`**
  — the strong FE-pair with `ε = −1` returns `Λ₅` entire with `Λ₅(2−s) = −Λ₅(s)`.
* **`theOddHandForcesTheCentralVanishingAtFive`** — `Λ₅(1) = 0`: the odd hand kills
  the fixed point of the reflection.  Analytic rank at least one, kernel-checked.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

noncomputable section

namespace Soma.Holonics.Millennium.FiveTheta

open Real HurwitzZeta Complex

/-! ## 1. The quadratic character mod five -/

/-- The quadratic character mod five on the integers: `+1` on residues `1, 4`,
`−1` on residues `2, 3`, `0` on multiples of five. -/
def chi5 (m : ℤ) : ℤ :=
  if m % 5 = 0 then 0 else if m % 5 = 1 ∨ m % 5 = 4 then 1 else -1

lemma chi5_congr {a b : ℤ} (h : a % 5 = b % 5) : chi5 a = chi5 b := by
  unfold chi5; rw [h]

lemma chi5_mul (a b : ℤ) : chi5 (a * b) = chi5 a * chi5 b := by
  have ha : a % 5 = 0 ∨ a % 5 = 1 ∨ a % 5 = 2 ∨ a % 5 = 3 ∨ a % 5 = 4 := by omega
  have hb : b % 5 = 0 ∨ b % 5 = 1 ∨ b % 5 = 2 ∨ b % 5 = 3 ∨ b % 5 = 4 := by omega
  have hab : (a * b) % 5 = (a % 5 * (b % 5)) % 5 := by
    conv_lhs => rw [Int.mul_emod]
  rcases ha with h1 | h1 | h1 | h1 | h1 <;> rcases hb with h2 | h2 | h2 | h2 | h2 <;>
    simp [chi5, hab, h1, h2]

lemma chi5_sq_mul (t w : ℤ) : chi5 (t ^ 2 * w) = chi5 t ^ 2 * chi5 w := by
  rw [show t ^ 2 * w = t * (t * w) from by ring, chi5_mul, chi5_mul]
  ring

lemma chi5_neg (a : ℤ) : chi5 (-a) = chi5 a := by
  have h4 : chi5 (-1 : ℤ) = 1 := by decide
  calc chi5 (-a) = chi5 ((-1) * a) := by ring_nf
    _ = chi5 (-1) * chi5 a := chi5_mul _ _
    _ = chi5 a := by rw [h4]; ring

lemma chi5_abs_le (a : ℤ) : |chi5 a| ≤ 1 := by
  unfold chi5; split_ifs <;> simp

/-! ## 2. The fifth root of unity and its two relations -/

/-- The primitive fifth root of unity. -/
def zeta5 : ℂ := cexp (2 * π * I / 5)

lemma zeta5_ne_zero : zeta5 ≠ 0 := Complex.exp_ne_zero _

lemma zeta5_pow_five : zeta5 ^ (5 : ℕ) = 1 := by
  rw [zeta5, ← Complex.exp_nat_mul]
  rw [show (5 : ℕ) * (2 * ↑π * I / 5) = 2 * π * I from by push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma zeta5_ne_one : zeta5 ≠ 1 := by
  intro h
  rw [zeta5, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hπ : (π : ℂ) ≠ 0 := by
    exact_mod_cast Real.pi_ne_zero
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  field_simp at hn
  have : (1 : ℤ) = 5 * n := by exact_mod_cast hn
  omega

/-- The vanishing cyclotomic sum: `1 + ζ + ζ² + ζ³ + ζ⁴ = 0`. -/
lemma zeta5_phi : 1 + zeta5 + zeta5 ^ 2 + zeta5 ^ 3 + zeta5 ^ 4 = 0 := by
  have h : (zeta5 - 1) * (1 + zeta5 + zeta5 ^ 2 + zeta5 ^ 3 + zeta5 ^ 4)
      = zeta5 ^ (5 : ℕ) - 1 := by ring
  rw [zeta5_pow_five, sub_self] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd (by linear_combination h1) zeta5_ne_one
  · exact h1

/-- Integer-exponent powers of `ζ` through `cexp`. -/
lemma zeta5_zpow_exp (K : ℤ) : cexp (2 * π * I * K / 5) = zeta5 ^ K := by
  rw [show (2 * (π : ℂ) * I * K / 5) = (K : ℂ) * (2 * π * I / 5) from by ring]
  rw [zeta5, ← Complex.exp_int_mul]

/-- Powers of `ζ` reduce mod five. -/
lemma zeta5_zpow_emod (K : ℤ) : zeta5 ^ K = zeta5 ^ (K % 5) := by
  conv_lhs => rw [show K = 5 * (K / 5) + K % 5 from by omega]
  rw [zpow_add₀ zeta5_ne_zero, zpow_mul]
  rw [show (zeta5 ^ (5 : ℤ)) = 1 from by
    rw [show (5 : ℤ) = ((5 : ℕ) : ℤ) from rfl, zpow_natCast, zeta5_pow_five]]
  rw [one_zpow, one_mul]

lemma zeta5_zpow_congr {a b : ℤ} (h : a % 5 = b % 5) : zeta5 ^ a = zeta5 ^ b := by
  rw [zeta5_zpow_emod a, zeta5_zpow_emod b, h]

/-- Small nonnegative powers via natural exponents. -/
lemma zeta5_zpow_ofNat (k : ℕ) : zeta5 ^ (k : ℤ) = zeta5 ^ k := zpow_natCast _ _

/-! ## 3. The Gauss sum mod five and the eigen-identity -/

/-- The linear Gauss sum `g(t) = Σ_{r<5} χ₅(r)·ζ^{tr}`. -/
def gSum (t : ℤ) : ℂ := ∑ r ∈ Finset.range 5, (chi5 (r : ℤ) : ℂ) * zeta5 ^ (t * (r : ℤ))

private lemma chi5_zero : chi5 0 = 0 := by decide
private lemma chi5_one : chi5 1 = 1 := by decide
private lemma chi5_two : chi5 2 = -1 := by decide
private lemma chi5_three : chi5 3 = -1 := by decide
private lemma chi5_four : chi5 4 = 1 := by decide

private lemma gSum_expand (t : ℤ) :
    gSum t = zeta5 ^ (t * 1) - zeta5 ^ (t * 2) - zeta5 ^ (t * 3) + zeta5 ^ (t * 4) := by
  unfold gSum
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  rw [show ((0 : ℕ) : ℤ) = 0 from rfl, show ((1 : ℕ) : ℤ) = 1 from rfl,
    show ((2 : ℕ) : ℤ) = 2 from rfl, show ((3 : ℕ) : ℤ) = 3 from rfl,
    show ((4 : ℕ) : ℤ) = 4 from rfl,
    chi5_zero, chi5_one, chi5_two, chi5_three, chi5_four]
  push_cast
  ring

private lemma zeta5_red (a b : ℤ) (h : a % 5 = b) : zeta5 ^ a = zeta5 ^ b := by
  rw [zeta5_zpow_emod a, h]

/-- The multiplicative shift law: `g(t) = χ₅(t)·g(1)`. -/
lemma gSum_shift (t : ℤ) : gSum t = (chi5 t : ℂ) * gSum 1 := by
  have ht : t % 5 = 0 ∨ t % 5 = 1 ∨ t % 5 = 2 ∨ t % 5 = 3 ∨ t % 5 = 4 := by omega
  have hchi : chi5 t = chi5 (t % 5) := chi5_congr (by omega)
  rcases ht with h | h | h | h | h
  · rw [gSum_expand, gSum_expand, hchi, h, chi5_zero,
      zeta5_red (t*1) 0 (by omega), zeta5_red (t*2) 0 (by omega),
      zeta5_red (t*3) 0 (by omega), zeta5_red (t*4) 0 (by omega)]
    push_cast
    ring
  · rw [gSum_expand, gSum_expand, hchi, h, chi5_one,
      zeta5_red (t*1) 1 (by omega), zeta5_red (t*2) 2 (by omega),
      zeta5_red (t*3) 3 (by omega), zeta5_red (t*4) 4 (by omega)]
    push_cast
    ring
  · rw [gSum_expand, gSum_expand, hchi, h, chi5_two,
      zeta5_red (t*1) 2 (by omega), zeta5_red (t*2) 4 (by omega),
      zeta5_red (t*3) 1 (by omega), zeta5_red (t*4) 3 (by omega)]
    push_cast
    ring
  · rw [gSum_expand, gSum_expand, hchi, h, chi5_three,
      zeta5_red (t*1) 3 (by omega), zeta5_red (t*2) 1 (by omega),
      zeta5_red (t*3) 4 (by omega), zeta5_red (t*4) 2 (by omega)]
    push_cast
    ring
  · rw [gSum_expand, gSum_expand, hchi, h, chi5_four,
      zeta5_red (t*1) 4 (by omega), zeta5_red (t*2) 3 (by omega),
      zeta5_red (t*3) 2 (by omega), zeta5_red (t*4) 1 (by omega)]
    push_cast
    ring

/-- The square of the Gauss sum is five: `g(1)² = 5`. -/
lemma gSum_one_sq : gSum 1 * gSum 1 = 5 := by
  have h5 : zeta5 ^ (5 : ℕ) = 1 := zeta5_pow_five
  have h6 : zeta5 ^ (6 : ℕ) = zeta5 ^ (1 : ℕ) := by
    rw [show (6 : ℕ) = 5 + 1 from rfl, pow_add, zeta5_pow_five, one_mul]
  have h7 : zeta5 ^ (7 : ℕ) = zeta5 ^ (2 : ℕ) := by
    rw [show (7 : ℕ) = 5 + 2 from rfl, pow_add, zeta5_pow_five, one_mul]
  have h8 : zeta5 ^ (8 : ℕ) = zeta5 ^ (3 : ℕ) := by
    rw [show (8 : ℕ) = 5 + 3 from rfl, pow_add, zeta5_pow_five, one_mul]
  have hA2 : (zeta5 + zeta5 ^ 4) ^ 2 = (zeta5 ^ 2 + zeta5 ^ 3) + 2 := by
    calc (zeta5 + zeta5 ^ 4) ^ 2 = zeta5 ^ 2 + 2 * zeta5 ^ 5 + zeta5 ^ 8 := by ring
      _ = (zeta5 ^ 2 + zeta5 ^ 3) + 2 := by rw [h8, h5]; ring
  have hB2 : (zeta5 ^ 2 + zeta5 ^ 3) ^ 2 = (zeta5 + zeta5 ^ 4) + 2 := by
    calc (zeta5 ^ 2 + zeta5 ^ 3) ^ 2 = zeta5 ^ 4 + 2 * zeta5 ^ 5 + zeta5 ^ 6 := by ring
      _ = (zeta5 + zeta5 ^ 4) + 2 := by rw [h6, h5]; ring
  have hAB : (zeta5 + zeta5 ^ 4) * (zeta5 ^ 2 + zeta5 ^ 3) = -1 := by
    calc (zeta5 + zeta5 ^ 4) * (zeta5 ^ 2 + zeta5 ^ 3)
        = zeta5 ^ 3 + zeta5 ^ 4 + zeta5 ^ 6 + zeta5 ^ 7 := by ring
      _ = zeta5 ^ 3 + zeta5 ^ 4 + zeta5 ^ 1 + zeta5 ^ 2 := by rw [h6, h7]
      _ = -1 := by linear_combination zeta5_phi
  have hApB : (zeta5 + zeta5 ^ 4) + (zeta5 ^ 2 + zeta5 ^ 3) = -1 := by
    linear_combination zeta5_phi
  have hg : gSum 1 = (zeta5 + zeta5 ^ 4) - (zeta5 ^ 2 + zeta5 ^ 3) := by
    rw [gSum_expand]
    rw [zeta5_red (1*1) 1 (by omega), zeta5_red (1*2) 2 (by omega),
      zeta5_red (1*3) 3 (by omega), zeta5_red (1*4) 4 (by omega)]
    rw [show (1 : ℤ) = ((1 : ℕ) : ℤ) from rfl, show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl,
      show (3 : ℤ) = ((3 : ℕ) : ℤ) from rfl, show (4 : ℤ) = ((4 : ℕ) : ℤ) from rfl,
      zpow_natCast, zpow_natCast, zpow_natCast, zpow_natCast]
    ring
  rw [hg]
  linear_combination hA2 + hB2 - 2 * hAB + hApB

/-- **The eigen-identity**: the twist character is a finite Fourier eigenfunction —
`Σ_{r,s<5} χ₅(r²−s²)·ζ^{ξr+ηs} = 5·χ₅(ξ²−η²)` for every integer frequency pair. -/
theorem theGaussEigenIdentity (ξ η : ℤ) :
    ∑ r ∈ Finset.range 5, ∑ s ∈ Finset.range 5,
        (chi5 ((r : ℤ) ^ 2 - (s : ℤ) ^ 2) : ℂ) * zeta5 ^ (ξ * (r : ℤ) + η * (s : ℤ))
      = 5 * (chi5 (ξ ^ 2 - η ^ 2) : ℂ) := by
  -- rotate to the split chart `(u, v) = (r+s, r−s)`
  have hrot : ∑ r ∈ Finset.range 5, ∑ s ∈ Finset.range 5,
        (chi5 ((r : ℤ) ^ 2 - (s : ℤ) ^ 2) : ℂ) * zeta5 ^ (ξ * (r : ℤ) + η * (s : ℤ))
      = ∑ u ∈ Finset.range 5, ∑ v ∈ Finset.range 5,
        (chi5 ((u : ℤ) * (v : ℤ)) : ℂ) * zeta5 ^ ((3*(ξ+η)) * (u : ℤ) + (3*(ξ-η)) * (v : ℤ)) := by
    rw [← Finset.sum_product', ← Finset.sum_product']
    refine Finset.sum_nbij' (fun p => ((p.1 + p.2) % 5, (p.1 + 5 - p.2) % 5))
      (fun q => ((3 * (q.1 + q.2)) % 5, (3 * (q.1 + 5 - q.2)) % 5)) ?_ ?_ ?_ ?_ ?_
    · rintro ⟨r, s⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp ⊢
      omega
    · rintro ⟨u, v⟩ hq
      simp only [Finset.mem_product, Finset.mem_range] at hq ⊢
      omega
    · rintro ⟨r, s⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      simp only [Prod.mk.injEq]
      constructor <;> omega
    · rintro ⟨u, v⟩ hq
      simp only [Finset.mem_product, Finset.mem_range] at hq
      simp only [Prod.mk.injEq]
      constructor <;> omega
    · rintro ⟨r, s⟩ hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      have hchi : chi5 ((((r + s) % 5 : ℕ) : ℤ) * (((r + 5 - s) % 5 : ℕ) : ℤ))
          = chi5 ((r : ℤ) ^ 2 - (s : ℤ) ^ 2) := by
        apply chi5_congr
        have h1 : (((r + s) % 5 : ℕ) : ℤ) % 5 = ((r : ℤ) + s) % 5 := by
          push_cast; omega
        have h2 : (((r + 5 - s) % 5 : ℕ) : ℤ) % 5 = ((r : ℤ) - s) % 5 := by
          push_cast; omega
        calc (((r + s) % 5 : ℕ) : ℤ) * (((r + 5 - s) % 5 : ℕ) : ℤ) % 5
            = ((((r + s) % 5 : ℕ) : ℤ) % 5) * ((((r + 5 - s) % 5 : ℕ) : ℤ) % 5) % 5 := by
              conv_lhs => rw [Int.mul_emod]
          _ = (((r : ℤ) + s) % 5) * (((r : ℤ) - s) % 5) % 5 := by rw [h1, h2]
          _ = (((r : ℤ) + s) * ((r : ℤ) - s)) % 5 := by rw [← Int.mul_emod]
          _ = ((r : ℤ) ^ 2 - (s : ℤ) ^ 2) % 5 := by ring_nf
      have hzet : zeta5 ^ ((3*(ξ+η)) * ((((r + s) % 5 : ℕ)) : ℤ)
            + (3*(ξ-η)) * ((((r + 5 - s) % 5 : ℕ)) : ℤ))
          = zeta5 ^ (ξ * (r : ℤ) + η * (s : ℤ)) := by
        apply zeta5_zpow_congr
        have hU : ((((r + s) % 5 : ℕ)) : ℤ) ≡ (r : ℤ) + s [ZMOD 5] := by
          show ((((r + s) % 5 : ℕ)) : ℤ) % 5 = ((r : ℤ) + s) % 5
          push_cast
          omega
        have hV : ((((r + 5 - s) % 5 : ℕ)) : ℤ) ≡ (r : ℤ) - s [ZMOD 5] := by
          show ((((r + 5 - s) % 5 : ℕ)) : ℤ) % 5 = ((r : ℤ) - s) % 5
          push_cast
          omega
        have h1 : (3*(ξ+η)) * ((((r + s) % 5 : ℕ)) : ℤ)
              + (3*(ξ-η)) * ((((r + 5 - s) % 5 : ℕ)) : ℤ)
            ≡ (3*(ξ+η)) * ((r : ℤ) + s) + (3*(ξ-η)) * ((r : ℤ) - s) [ZMOD 5] :=
          (hU.mul_left _).add (hV.mul_left _)
        have h2 : (3*(ξ+η)) * ((r : ℤ) + s) + (3*(ξ-η)) * ((r : ℤ) - s)
            ≡ ξ * (r : ℤ) + η * (s : ℤ) [ZMOD 5] := by
          rw [Int.modEq_iff_dvd]
          exact ⟨-(ξ * (r : ℤ) + η * (s : ℤ)), by ring⟩
        exact h1.trans h2
      rw [hchi, hzet]
  rw [hrot]
  -- factor the double sum through the two linear Gauss sums
  have hfac : ∑ u ∈ Finset.range 5, ∑ v ∈ Finset.range 5,
        (chi5 ((u : ℤ) * (v : ℤ)) : ℂ) * zeta5 ^ ((3*(ξ+η)) * (u : ℤ) + (3*(ξ-η)) * (v : ℤ))
      = gSum (3*(ξ+η)) * gSum (3*(ξ-η)) := by
    unfold gSum
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ => ?_
    rw [chi5_mul, zpow_add₀ zeta5_ne_zero]
    push_cast
    ring
  rw [hfac, gSum_shift (3*(ξ+η)), gSum_shift (3*(ξ-η))]
  have hchi9 : chi5 (3*(ξ+η)) * chi5 (3*(ξ-η)) = chi5 (ξ ^ 2 - η ^ 2) := by
    rw [← chi5_mul]
    calc chi5 (3*(ξ+η) * (3*(ξ-η))) = chi5 (9 * (ξ^2 - η^2)) := by ring_nf
      _ = chi5 (3 ^ 2) * chi5 (ξ^2 - η^2) := by
          rw [show (9 : ℤ) * (ξ^2 - η^2) = 3^2 * (ξ^2 - η^2) from by ring, chi5_mul]
      _ = chi5 (ξ^2 - η^2) := by norm_num [chi5]
  calc (chi5 (3*(ξ+η)) : ℂ) * gSum 1 * ((chi5 (3*(ξ-η)) : ℂ) * gSum 1)
      = ((chi5 (3*(ξ+η)) * chi5 (3*(ξ-η)) : ℤ) : ℂ) * (gSum 1 * gSum 1) := by
        push_cast; ring
    _ = ((chi5 (ξ^2 - η^2) : ℤ) : ℂ) * 5 := by rw [hchi9, gSum_one_sq]
    _ = 5 * (chi5 (ξ ^ 2 - η ^ 2) : ℂ) := by ring

/-! ## 4. The phase decompositions at level twenty and ten -/

/-- The odd indicator, as a complex weight. -/
def oddInd (m : ℤ) : ℂ := if m % 2 = 0 then 0 else 1

/-- Integer powers of `−1` through `cexp`. -/
lemma neg_one_zpow_exp (k : ℤ) : cexp (π * I * k) = (-1 : ℂ) ^ k := by
  rw [show (π : ℂ) * I * k = (k : ℂ) * (π * I) from by ring, Complex.exp_int_mul,
    Complex.exp_pi_mul_I]

/-- The level-twenty phase splits into the quarter-turn and the mod-five phase. -/
lemma phaseA (e n : ℤ) :
    cexp (2 * π * I * ((4 * e + 1) * n) / 20)
      = cexp (π * I * n / 2) * zeta5 ^ (-((4 * e + 1) * n)) := by
  rw [show 2 * (π : ℂ) * I * ((4 * e + 1) * n) / 20
      = (e * n : ℤ) * (2 * π * I)
        + (π * I * n / 2 + 2 * π * I * ((-((4 * e + 1) * n) : ℤ) : ℂ) / 5) from by
    push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_add,
    zeta5_zpow_exp]

/-- The level-ten phase splits into the half-turn and the mod-five phase. -/
lemma phaseB (d m : ℤ) :
    cexp (2 * π * I * (d * m) / 10)
      = (-1 : ℂ) ^ (d * m) * zeta5 ^ (-(2 * d * m)) := by
  rw [show 2 * (π : ℂ) * I * (d * m) / 10
      = π * I * ((d * m : ℤ) : ℂ) + 2 * π * I * ((-(2 * d * m) : ℤ) : ℂ) / 5 from by
    push_cast; ring]
  rw [Complex.exp_add, zeta5_zpow_exp, neg_one_zpow_exp]

/-! ## 5. The phase collapse: fifty phases return the eigen-identity -/

/-- One dual-side phase coefficient. -/
private def phaseTerm (n m : ℤ) (e d : ℕ) : ℂ :=
  (chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) : ℂ) * (-1 : ℂ) ^ (d : ℕ) *
    cexp (2 * π * I * ((4 * (e : ℤ) + 1) * n) / 20) * cexp (2 * π * I * ((d : ℤ) * m) / 10)

/-- **The phase collapse.**  The fifty dual-side phases collapse through the Gauss
eigen-identity: the whole `(e, d)` sum is `10·i^n·[m odd]·χ₅(n²+m²)`. -/
theorem thePhaseCollapse (n m : ℤ) :
    ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10, phaseTerm n m e d
      = 10 * cexp (π * I * n / 2) * oddInd m * (chi5 (n ^ 2 + m ^ 2) : ℂ) := by
  have hneg : (-1 : ℂ) ≠ 0 := by norm_num
  -- pair `d` against `d + 5`: the ten-fold `d`-sum folds to the five-fold one
  have hpair : ∀ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10, phaseTerm n m e d
      = (1 - (-1 : ℂ) ^ m) * ∑ d ∈ Finset.range 5, phaseTerm n m e d := by
    intro e _
    have hsplit : ∑ d ∈ Finset.range 10, phaseTerm n m e d
        = ∑ d ∈ Finset.range 5, phaseTerm n m e d
          + ∑ d ∈ Finset.range 5, phaseTerm n m e (5 + d) := by
      rw [show (10 : ℕ) = 5 + 5 from rfl, Finset.sum_range_add]
    have hshift : ∀ d : ℕ, phaseTerm n m e (5 + d) = -((-1 : ℂ) ^ m) * phaseTerm n m e d := by
      intro d
      unfold phaseTerm
      have hc : ((5 + d : ℕ) : ℤ) = (d : ℤ) + 5 := by push_cast; ring
      rw [hc]
      have hchi : chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * ((d : ℤ) + 5) ^ 2)
          = chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) := by
        apply chi5_congr
        have h : (4 * (e : ℤ) + 1) ^ 2 + 4 * ((d : ℤ) + 5) ^ 2
            = ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) + 5 * (8 * (d : ℤ) + 20) := by ring
        omega
      have hsign : (-1 : ℂ) ^ ((5 + d : ℕ)) = -(-1 : ℂ) ^ (d : ℕ) := by
        rw [pow_add]
        norm_num
      have hph : cexp (2 * π * I * (((d : ℤ) + 5) * m) / 10)
          = (-1 : ℂ) ^ m * cexp (2 * π * I * ((d : ℤ) * m) / 10) := by
        rw [show 2 * (π : ℂ) * I * (((d : ℤ) + 5) * m) / 10
            = π * I * ((m : ℤ) : ℂ) + 2 * π * I * ((d : ℤ) * m) / 10 from by push_cast; ring]
        rw [Complex.exp_add, neg_one_zpow_exp]
      rw [hchi, hsign]
      push_cast at hph ⊢
      rw [hph]
      ring
    rw [hsplit, Finset.sum_congr rfl fun d _ => hshift d, ← Finset.mul_sum]
    ring
  rw [Finset.sum_congr rfl hpair, ← Finset.mul_sum]
  rcases Int.even_or_odd m with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- even hand: both sides vanish
    have h1 : (-1 : ℂ) ^ m = 1 := by
      rw [hk, show k + k = 2 * k from by ring, zpow_mul]
      norm_num
    have h0 : oddInd m = 0 := by
      unfold oddInd
      rw [if_pos (by omega)]
    rw [h1, h0]
    ring
  · -- odd hand: the eigen-identity carries the sum
    have hm1 : (-1 : ℂ) ^ m = -1 := by
      rw [hk, zpow_add₀ hneg, zpow_mul]
      norm_num
    have h1 : oddInd m = 1 := by
      unfold oddInd
      rw [if_neg (by omega)]
    -- the sign pair `(−1)^d·(−1)^{dm}` is trivial on the odd hand
    have htriv : ∀ d : ℕ, (-1 : ℂ) ^ (d : ℕ) * (-1 : ℂ) ^ ((d : ℤ) * m) = 1 := by
      intro d
      rw [← zpow_natCast (-1 : ℂ) d, ← zpow_add₀ hneg,
        show (d : ℤ) + (d : ℤ) * m = (d : ℤ) * (1 + m) from by ring, hk,
        show (d : ℤ) * (1 + (2 * k + 1)) = 2 * ((d : ℤ) * (k + 1)) from by ring, zpow_mul]
      norm_num
    -- collapse each term through the two phase decompositions
    have hterm : ∀ e ∈ Finset.range 5, ∀ d ∈ Finset.range 5, phaseTerm n m e d
        = cexp (π * I * n / 2) *
            ((chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) : ℂ) *
              (zeta5 ^ (-((4 * (e : ℤ) + 1) * n)) * zeta5 ^ (-(2 * (d : ℤ) * m)))) := by
      intro e _ d _
      unfold phaseTerm
      rw [phaseA, phaseB]
      calc (chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) : ℂ) * (-1 : ℂ) ^ (d : ℕ) *
            (cexp (π * I * n / 2) * zeta5 ^ (-((4 * (e : ℤ) + 1) * n))) *
            ((-1 : ℂ) ^ ((d : ℤ) * m) * zeta5 ^ (-(2 * (d : ℤ) * m)))
          = ((-1 : ℂ) ^ (d : ℕ) * (-1 : ℂ) ^ ((d : ℤ) * m)) *
            ((chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) : ℂ) *
              (cexp (π * I * n / 2) * (zeta5 ^ (-((4 * (e : ℤ) + 1) * n)) *
                zeta5 ^ (-(2 * (d : ℤ) * m))))) := by ring
        _ = _ := by rw [htriv d]; ring
    have hsum2 : ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 5, phaseTerm n m e d
        = cexp (π * I * n / 2) *
            ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 5,
              (chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) : ℂ) *
                (zeta5 ^ (-((4 * (e : ℤ) + 1) * n)) * zeta5 ^ (-(2 * (d : ℤ) * m))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e he => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun d hd => hterm e he d hd
    -- reindex `e ↦ r = (4e+1) % 5` and land on the eigen-identity
    have hre : ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 5,
          (chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) : ℂ) *
            (zeta5 ^ (-((4 * (e : ℤ) + 1) * n)) * zeta5 ^ (-(2 * (d : ℤ) * m)))
        = ∑ r ∈ Finset.range 5, ∑ s ∈ Finset.range 5,
            (chi5 ((r : ℤ) ^ 2 - (s : ℤ) ^ 2) : ℂ) *
              zeta5 ^ ((-n) * (r : ℤ) + (-(2 * m)) * (s : ℤ)) := by
      refine Finset.sum_nbij' (fun e => (4 * e + 1) % 5) (fun r => (4 * r + 1) % 5)
        ?_ ?_ ?_ ?_ ?_
      · intro e he
        simp only [Finset.mem_range] at he ⊢
        omega
      · intro r hr
        simp only [Finset.mem_range] at hr ⊢
        omega
      · intro e he
        simp only [Finset.mem_range] at he
        show (4 * ((4 * e + 1) % 5) + 1) % 5 = e
        omega
      · intro r hr
        simp only [Finset.mem_range] at hr
        show (4 * ((4 * r + 1) % 5) + 1) % 5 = r
        omega
      · intro e he
        simp only [Finset.mem_range] at he
        refine Finset.sum_congr rfl fun s hs => ?_
        simp only [Finset.mem_range] at hs
        have hchi : chi5 ((((4 * e + 1) % 5 : ℕ) : ℤ) ^ 2 - (s : ℤ) ^ 2)
            = chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (s : ℤ) ^ 2) := by
          apply chi5_congr
          have hcast : (((4 * e + 1) % 5 : ℕ) : ℤ) = (4 * (e : ℤ) + 1) % 5 := by
            push_cast
            omega
          rw [hcast]
          have hb : ((4 * (e : ℤ) + 1) % 5) ≡ 4 * (e : ℤ) + 1 [ZMOD 5] :=
            Int.emod_emod_of_dvd _ (by norm_num)
          have h1 : ((4 * (e : ℤ) + 1) % 5) ^ 2 - (s : ℤ) ^ 2
              ≡ (4 * (e : ℤ) + 1) ^ 2 - (s : ℤ) ^ 2 [ZMOD 5] :=
            (hb.pow 2).sub (Int.ModEq.refl _)
          have h2 : (4 * (e : ℤ) + 1) ^ 2 - (s : ℤ) ^ 2
              ≡ (4 * (e : ℤ) + 1) ^ 2 + 4 * (s : ℤ) ^ 2 [ZMOD 5] := by
            rw [Int.modEq_iff_dvd]
            exact ⟨(s : ℤ) ^ 2, by ring⟩
          exact h1.trans h2
        have hzet : zeta5 ^ ((-n) * ((((4 * e + 1) % 5 : ℕ)) : ℤ) + (-(2 * m)) * (s : ℤ))
            = zeta5 ^ (-((4 * (e : ℤ) + 1) * n)) * zeta5 ^ (-(2 * (s : ℤ) * m)) := by
          rw [← zpow_add₀ zeta5_ne_zero]
          apply zeta5_zpow_congr
          have hcast : (((4 * e + 1) % 5 : ℕ) : ℤ) = (4 * (e : ℤ) + 1) % 5 := by
            push_cast
            omega
          rw [hcast]
          have hU : (-n) * ((4 * (e : ℤ) + 1) % 5) ≡ (-n) * (4 * (e : ℤ) + 1) [ZMOD 5] :=
            Int.ModEq.mul_left _ (Int.emod_emod_of_dvd _ (by norm_num))
          have h2 : (-n) * (4 * (e : ℤ) + 1) + (-(2 * m)) * (s : ℤ)
              = -((4 * (e : ℤ) + 1) * n) + -(2 * (s : ℤ) * m) := by ring
          calc ((-n) * ((4 * (e : ℤ) + 1) % 5) + (-(2 * m)) * (s : ℤ)) % 5
              = ((-n) * (4 * (e : ℤ) + 1) + (-(2 * m)) * (s : ℤ)) % 5 :=
                (hU.add (Int.ModEq.refl _))
            _ = (-((4 * (e : ℤ) + 1) * n) + -(2 * (s : ℤ) * m)) % 5 := by rw [h2]
        rw [hchi, hzet]
    rw [hsum2, hre, theGaussEigenIdentity (-n) (-(2 * m))]
    have hfin : chi5 ((-n) ^ 2 - (-(2 * m)) ^ 2) = chi5 (n ^ 2 + m ^ 2) := by
      apply chi5_congr
      have : (-n) ^ 2 - (-(2 * m)) ^ 2 = n ^ 2 + m ^ 2 - 5 * m ^ 2 := by ring
      omega
    rw [hfin, hm1, h1]
    ring

/-! ## 6. The theta function at five, as fifty kernel products -/

/-- The coefficient of the `(e, d)` kernel product: `χ₅((4e+1)² + 4d²)·(−1)^d`. -/
def w5 (e d : ℕ) : ℤ := chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) * (-1) ^ d

/-- **The theta function of the congruent-number curve at five**: the `χ₅`-weighted
Gaussian class sum, presented as twenty times the fifty products of shifted Hurwitz
kernels at argument `20√2·x` — conductor `800`, weight two. -/
def theta5 (x : ℝ) : ℝ :=
  20 * ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
    (w5 e d : ℝ) *
      (oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x) *
       evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x))

/-! ## 7. Summability spine -/

private lemma sqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

private lemma summable_gauss_weight (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℤ => |(n : ℝ)| * rexp (-π * c * n ^ 2) := by
  have h := (HurwitzZeta.hasSum_int_oddKernel 0 hc).summable.norm
  have h0 : Summable fun n : ℤ => |(n : ℝ) + 0| * rexp (-π * ((n : ℝ) + 0) ^ 2 * c) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)] using h
  refine h0.congr fun n => ?_
  rw [add_zero]
  ring_nf

private lemma summable_gauss (c : ℝ) (hc : 0 < c) :
    Summable fun n : ℤ => rexp (-π * c * n ^ 2) := by
  have h := (HurwitzZeta.hasSum_int_evenKernel 0 hc).summable
  refine h.congr fun n => ?_
  rw [add_zero]
  ring_nf

set_option maxHeartbeats 1000000 in
private lemma summable_master {c : ℝ} (hc : 0 < c) :
    Summable fun p : ℤ × ℤ =>
      (|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * rexp (-π * c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
  have hw := summable_gauss_weight c hc
  have hg := summable_gauss c hc
  have h1 : Summable fun p : ℤ × ℤ =>
      (|(p.1 : ℝ)| * rexp (-π * c * (p.1 : ℝ) ^ 2)) * rexp (-π * c * (p.2 : ℝ) ^ 2) :=
    hw.mul_of_nonneg hg (Pi.le_def.mpr fun n => by positivity)
      (Pi.le_def.mpr fun n => Real.exp_nonneg _)
  have h2 : Summable fun p : ℤ × ℤ =>
      rexp (-π * c * (p.1 : ℝ) ^ 2) * (|(p.2 : ℝ)| * rexp (-π * c * (p.2 : ℝ) ^ 2)) :=
    hg.mul_of_nonneg hw (Pi.le_def.mpr fun n => Real.exp_nonneg _)
      (Pi.le_def.mpr fun n => by positivity)
  have h3 : Summable fun p : ℤ × ℤ =>
      rexp (-π * c * (p.1 : ℝ) ^ 2) * rexp (-π * c * (p.2 : ℝ) ^ 2) :=
    hg.mul_of_nonneg hg (Pi.le_def.mpr fun n => Real.exp_nonneg _)
      (Pi.le_def.mpr fun n => Real.exp_nonneg _)
  refine ((h1.add h2).add h3).congr fun p => ?_
  rw [show -π * c * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)
      = -π * c * (p.1 : ℝ) ^ 2 + -π * c * (p.2 : ℝ) ^ 2 from by ring, Real.exp_add]
  ring

/-- The pre-fold Gaussian envelope. -/
private def envP (y : ℝ) (u v : ℤ) : ℝ := rexp (-π * y * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2))

/-- The post-fold Gaussian envelope. -/
private def envF (y : ℝ) (u v : ℤ) : ℝ := rexp (-2 * π * y * ((u : ℝ) ^ 2 + (v : ℝ) ^ 2))

private lemma envP_nonneg (y : ℝ) (u v : ℤ) : 0 ≤ envP y u v := Real.exp_nonneg _
private lemma envF_nonneg (y : ℝ) (u v : ℤ) : 0 ≤ envF y u v := Real.exp_nonneg _

private lemma summable_envP {y : ℝ} (hy : 0 < y) :
    Summable fun p : ℤ × ℤ => (|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * envP y p.1 p.2 :=
  (summable_master hy).congr fun p => rfl

private lemma summable_envF {y : ℝ} (hy : 0 < y) :
    Summable fun p : ℤ × ℤ => (|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * envF y p.1 p.2 := by
  refine (summable_master (show (0 : ℝ) < 2 * y by positivity)).congr fun p => ?_
  unfold envF
  congr 2
  ring

private lemma summable_of_le_envP {y : ℝ} (hy : 0 < y) {f : ℤ × ℤ → ℂ}
    (hb : ∀ p : ℤ × ℤ, ‖f p‖ ≤ 10 * ((|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * envP y p.1 p.2)) :
    Summable f :=
  Summable.of_norm_bounded ((summable_envP hy).mul_left 10) hb

private lemma summable_of_le_envF {y : ℝ} (hy : 0 < y) {f : ℤ × ℤ → ℂ}
    (hb : ∀ p : ℤ × ℤ, ‖f p‖ ≤ 40 * ((|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * envF y p.1 p.2)) :
    Summable f :=
  Summable.of_norm_bounded ((summable_envF hy).mul_left 40) hb

/-! ## 8. The dual side: fifty kernel products collapse onto one lattice family -/

/-- The `sinKernel` summand at shift `(4e+1)/20`. -/
private def sinT (y : ℝ) (e : ℕ) (n : ℤ) : ℂ :=
  -I * n * cexp (2 * π * I * (((4 * (e : ℝ) + 1) / 20 : ℝ) : ℂ) * n) * rexp (-π * n ^ 2 * y)

/-- The `cosKernel` summand at shift `d/10`. -/
private def cosT (y : ℝ) (d : ℕ) (m : ℤ) : ℂ :=
  cexp (2 * π * I * (((d : ℝ) / 10 : ℝ) : ℂ) * m) * rexp (-π * m ^ 2 * y)

/-- The collapsed dual family: weight `n`, quarter-turn phase, odd indicator in `m`,
the twist character, and the pre-fold envelope. -/
private def dual5 (y : ℝ) (p : ℤ × ℤ) : ℂ :=
  -I * p.1 * (10 * cexp (π * I * p.1 / 2) * oddInd p.2 * (chi5 (p.1 ^ 2 + p.2 ^ 2) : ℂ)) *
    (envP y p.1 p.2 : ℝ)

private lemma norm_chi5_le (N : ℤ) : ‖((chi5 N : ℤ) : ℂ)‖ ≤ 1 := by
  have h := chi5_abs_le N
  rw [show ((chi5 N : ℤ) : ℂ) = ((chi5 N : ℝ) : ℂ) from by push_cast; rfl,
    Complex.norm_real, Real.norm_eq_abs]
  exact_mod_cast h

private lemma norm_oddInd_le (m : ℤ) : ‖oddInd m‖ ≤ 1 := by
  unfold oddInd
  split_ifs <;> simp

private lemma norm_quarter_phase (n : ℤ) : ‖cexp (π * I * n / 2)‖ = 1 := by
  rw [show (π : ℂ) * I * n / 2 = ((π * n / 2 : ℝ) : ℂ) * I from by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

private lemma norm_dual5_le (y : ℝ) (p : ℤ × ℤ) :
    ‖dual5 y p‖ ≤ 10 * ((|(p.1 : ℝ)| + |(p.2 : ℝ)| + 1) * envP y p.1 p.2) := by
  obtain ⟨n, m⟩ := p
  unfold dual5
  simp only [norm_mul]
  have h1 : ‖(-I : ℂ)‖ = 1 := by simp
  have h2 : ‖((n : ℤ) : ℂ)‖ = |(n : ℝ)| := by
    rw [show ((n : ℤ) : ℂ) = ((n : ℝ) : ℂ) from by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs]
  have h3 : ‖((envP y n m : ℝ) : ℂ)‖ = envP y n m := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (envP_nonneg y n m)]
  have h4 : ‖(10 : ℂ)‖ = 10 := by norm_num
  rw [h1, h2, h3, h4, norm_quarter_phase]
  have hb : |(n : ℝ)| ≤ |(n : ℝ)| + |(m : ℝ)| + 1 := by
    have := abs_nonneg (m : ℝ); linarith
  have hoi := norm_oddInd_le m
  have hch := norm_chi5_le (n ^ 2 + m ^ 2)
  have he := envP_nonneg y n m
  have hn := abs_nonneg (n : ℝ)
  have h5 : 10 * 1 * ‖oddInd m‖ * ‖((chi5 (n ^ 2 + m ^ 2) : ℤ) : ℂ)‖ ≤ 10 := by
    have hoi0 := norm_nonneg (oddInd m)
    have hch0 := norm_nonneg ((chi5 (n ^ 2 + m ^ 2) : ℤ) : ℂ)
    nlinarith
  have h50 : 0 ≤ 10 * 1 * ‖oddInd m‖ * ‖((chi5 (n ^ 2 + m ^ 2) : ℤ) : ℂ)‖ := by
    have hoi0 := norm_nonneg (oddInd m)
    have hch0 := norm_nonneg ((chi5 (n ^ 2 + m ^ 2) : ℤ) : ℂ)
    positivity
  calc 1 * |(n : ℝ)| * (10 * 1 * ‖oddInd m‖ * ‖((chi5 (n ^ 2 + m ^ 2) : ℤ) : ℂ)‖) *
        envP y n m
      = |(n : ℝ)| * envP y n m *
          (10 * 1 * ‖oddInd m‖ * ‖((chi5 (n ^ 2 + m ^ 2) : ℤ) : ℂ)‖) := by ring
    _ ≤ |(n : ℝ)| * envP y n m * 10 :=
        mul_le_mul_of_nonneg_left h5 (mul_nonneg hn he)
    _ = 10 * (|(n : ℝ)| * envP y n m) := by ring
    _ ≤ 10 * ((|(n : ℝ)| + |(m : ℝ)| + 1) * envP y n m) := by
        have := mul_le_mul_of_nonneg_right hb he
        linarith

private lemma summable_dual5 {y : ℝ} (hy : 0 < y) : Summable (dual5 y) :=
  summable_of_le_envP hy (norm_dual5_le y)

private lemma summable_sinT {y : ℝ} (hy : 0 < y) (e : ℕ) : Summable (sinT y e) :=
  (HurwitzZeta.hasSum_int_sinKernel ((4 * (e : ℝ) + 1) / 20) hy).summable

private lemma summable_cosT {y : ℝ} (hy : 0 < y) (d : ℕ) : Summable (cosT y d) :=
  (HurwitzZeta.hasSum_int_cosKernel ((d : ℝ) / 10) hy).summable

private lemma summable_sinT_cosT {y : ℝ} (hy : 0 < y) (e d : ℕ) :
    Summable fun p : ℤ × ℤ => sinT y e p.1 * cosT y d p.2 :=
  summable_norm_iff.mp
    ((summable_norm_iff.mpr (summable_sinT hy e)).mul_norm
      (summable_norm_iff.mpr (summable_cosT hy d)))

/-- One kernel product expands to the lattice double sum. -/
private lemma kernel_product_eq (y : ℝ) (hy : 0 < y) (e d : ℕ) :
    ((sinKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) y : ℝ) : ℂ) *
        ((cosKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) y : ℝ) : ℂ)
      = ∑' p : ℤ × ℤ, sinT y e p.1 * cosT y d p.2 :=
  (HurwitzZeta.hasSum_int_sinKernel ((4 * (e : ℝ) + 1) / 20) hy).mul_eq
    (HurwitzZeta.hasSum_int_cosKernel ((d : ℝ) / 10) hy)
    (summable_sinT_cosT hy e d).hasSum

/-- The pointwise collapse: the fifty weighted lattice terms at one `(n, m)` return the
single `dual5` term. -/
private lemma pointwise_collapse (y : ℝ) (p : ℤ × ℤ) :
    ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
        ((w5 e d : ℤ) : ℂ) * (sinT y e p.1 * cosT y d p.2)
      = dual5 y p := by
  obtain ⟨n, m⟩ := p
  have hphase : ∀ e d : ℕ, ((w5 e d : ℤ) : ℂ) * (sinT y e n * cosT y d m)
      = (-I * n * (rexp (-π * n ^ 2 * y) : ℝ) * (rexp (-π * m ^ 2 * y) : ℝ)) *
          phaseTerm n m e d := by
    intro e d
    unfold w5 sinT cosT phaseTerm
    have hA : cexp (2 * π * I * (((4 * (e : ℝ) + 1) / 20 : ℝ) : ℂ) * n)
        = cexp (2 * π * I * ((4 * (e : ℤ) + 1) * n) / 20) := by
      congr 1
      push_cast
      ring
    have hB : cexp (2 * π * I * (((d : ℝ) / 10 : ℝ) : ℂ) * m)
        = cexp (2 * π * I * ((d : ℤ) * m) / 10) := by
      congr 1
      push_cast
      ring
    rw [hA, hB]
    push_cast
    ring
  rw [Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => hphase e d]
  have hsum : ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
      (-I * (n : ℂ) * ((rexp (-π * n ^ 2 * y) : ℝ) : ℂ) *
        ((rexp (-π * m ^ 2 * y) : ℝ) : ℂ)) * phaseTerm n m e d
      = (-I * (n : ℂ) * ((rexp (-π * n ^ 2 * y) : ℝ) : ℂ) *
        ((rexp (-π * m ^ 2 * y) : ℝ) : ℂ)) *
          ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10, phaseTerm n m e d := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
  rw [hsum, thePhaseCollapse n m]
  show _ = dual5 y (n, m)
  unfold dual5
  have henv : ((rexp (-π * n ^ 2 * y) : ℝ) : ℂ) * ((rexp (-π * m ^ 2 * y) : ℝ) : ℂ)
      = ((envP y n m : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    unfold envP
    norm_cast
    congr 1
    push_cast
    ring
  linear_combination (-I * (n : ℂ) * (10 * cexp (π * I * n / 2) * oddInd m *
    (chi5 (n ^ 2 + m ^ 2) : ℂ))) * henv

/-- The dual side of the duplication: the fifty weighted `sinKernel`–`cosKernel`
products equal the sum of the collapsed lattice family. -/
private lemma dual_side_eq {y : ℝ} (hy : 0 < y) :
    ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
        ((w5 e d : ℤ) : ℂ) *
          (((sinKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) y : ℝ) : ℂ) *
           ((cosKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) y : ℝ) : ℂ))
      = ∑' p : ℤ × ℤ, dual5 y p := by
  have hstep : ∀ e ∈ Finset.range 5, ∀ d ∈ Finset.range 10,
      ((w5 e d : ℤ) : ℂ) *
          (((sinKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) y : ℝ) : ℂ) *
           ((cosKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) y : ℝ) : ℂ))
        = ∑' p : ℤ × ℤ, ((w5 e d : ℤ) : ℂ) * (sinT y e p.1 * cosT y d p.2) := by
    intro e _ d _
    rw [kernel_product_eq y hy e d, ← tsum_mul_left]
  rw [Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun d hd => hstep e he d hd]
  have hswap : ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
      ∑' p : ℤ × ℤ, ((w5 e d : ℤ) : ℂ) * (sinT y e p.1 * cosT y d p.2)
      = ∑' p : ℤ × ℤ, ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
          ((w5 e d : ℤ) : ℂ) * (sinT y e p.1 * cosT y d p.2) := by
    rw [Summable.tsum_finsetSum fun e _ => summable_sum fun d _ =>
      ((summable_sinT_cosT hy e d).mul_left _)]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Summable.tsum_finsetSum fun d _ => (summable_sinT_cosT hy e d).mul_left _]
  rw [hswap]
  exact tsum_congr fun p => pointwise_collapse y p

/-! ## 9. The ladder: from the collapsed dual family to the folded classes -/

/-- The quartic sign. -/
private def sgn4 (w : ℤ) : ℂ := if w % 4 = 1 then 1 else if w % 4 = 3 then -1 else 0

/-- The doubled cosine sign. -/
private def cs4 (v : ℤ) : ℂ := if v % 4 = 0 then 1 else if v % 4 = 2 then -1 else 0

private lemma norm_sgn4_le (w : ℤ) : ‖sgn4 w‖ ≤ 1 := by
  unfold sgn4; split_ifs <;> simp

private lemma norm_cs4_le (v : ℤ) : ‖cs4 v‖ ≤ 1 := by
  unfold cs4; split_ifs <;> simp

private def dual5Even (y : ℝ) (p : ℤ × ℤ) : ℂ := if p.1 % 2 = 0 then dual5 y p else 0

private def dual5Odd (y : ℝ) (p : ℤ × ℤ) : ℂ := if p.1 % 2 = 0 then 0 else dual5 y p

/-- After the fold: weight `u+v`, quartic sign, twist character at `2(u²+v²)`. -/
private def gLadder5 (y : ℝ) (p : ℤ × ℤ) : ℂ :=
  10 * ((p.1 + p.2 : ℤ) : ℂ) * sgn4 (p.1 + p.2) *
    ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ) * ((envF y p.1 p.2 : ℝ) : ℂ)

private def gEven5 (y : ℝ) (p : ℤ × ℤ) : ℂ := if p.2 % 2 = 0 then gLadder5 y p else 0

private def gOddV5 (y : ℝ) (p : ℤ × ℤ) : ℂ := if p.2 % 2 = 0 then 0 else gLadder5 y p

private def hHalf5 (y : ℝ) (p : ℤ × ℤ) : ℂ :=
  if p.2 % 2 = 0 then
    10 * (p.1 : ℂ) * sgn4 (p.1 + p.2) * ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ) *
      ((envF y p.1 p.2 : ℝ) : ℂ)
  else 0

private def hPlus5 (y : ℝ) (p : ℤ × ℤ) : ℂ :=
  if (p.1 + p.2) % 4 = 1 ∧ p.2 % 2 = 0 then
    10 * (p.1 : ℂ) * ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ) * ((envF y p.1 p.2 : ℝ) : ℂ)
  else 0

private def hMinus5 (y : ℝ) (p : ℤ × ℤ) : ℂ :=
  if (p.1 + p.2) % 4 = 3 ∧ p.2 % 2 = 0 then
    10 * (p.1 : ℂ) * ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ) * ((envF y p.1 p.2 : ℝ) : ℂ)
  else 0

private def hFinal5 (y : ℝ) (p : ℤ × ℤ) : ℂ :=
  if p.1 % 4 = 1 then
    40 * (p.1 : ℂ) * cs4 p.2 * ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ) *
      ((envF y p.1 p.2 : ℝ) : ℂ)
  else 0

private def aPiece5 (y : ℝ) (p : ℤ × ℤ) : ℂ :=
  if p.1 % 4 = 1 ∧ p.2 % 4 = 0 then
    10 * (p.1 : ℂ) * ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ) * ((envF y p.1 p.2 : ℝ) : ℂ)
  else 0

private def bPiece5 (y : ℝ) (p : ℤ × ℤ) : ℂ :=
  if p.1 % 4 = 3 ∧ p.2 % 4 = 2 then
    10 * (p.1 : ℂ) * ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ) * ((envF y p.1 p.2 : ℝ) : ℂ)
  else 0

private def bMirror5 (y : ℝ) (p : ℤ × ℤ) : ℂ :=
  if p.1 % 4 = 1 ∧ p.2 % 4 = 2 then
    10 * (p.1 : ℂ) * ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ) * ((envF y p.1 p.2 : ℝ) : ℂ)
  else 0

/-! ## 10. Index maps -/

private def bothOddEmb (q : ℤ × ℤ) : ℤ × ℤ := (2 * q.1 + 1, 2 * q.2 + 1)

private def foldMap (q : ℤ × ℤ) : ℤ × ℤ := (q.1 + q.2 + 1, q.1 - q.2)

private def gridEmb (q : ℤ × ℤ) : ℤ × ℤ := (4 * q.1 + 1, 2 * q.2)

private lemma bothOddEmb_injective : Function.Injective bothOddEmb := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [bothOddEmb, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

private lemma foldMap_injective : Function.Injective foldMap := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [foldMap, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

private lemma gridEmb_injective : Function.Injective gridEmb := by
  rintro ⟨a, b⟩ ⟨c, e⟩ h
  simp only [gridEmb, Prod.mk.injEq] at h
  exact Prod.ext_iff.mpr ⟨by omega, by omega⟩

/-! ## 11. Summability along the ladder -/

private lemma norm_weight_le (y : ℝ) (u v w : ℤ) (c : ℝ) (s : ℂ) (hs : ‖s‖ ≤ 1)
    (hc : 0 ≤ c) (hw : c * |(w : ℝ)| ≤ 40 * (|(u : ℝ)| + |(v : ℝ)| + 1)) :
    ‖(c : ℂ) * ((w : ℤ) : ℂ) * s * ((envF y u v : ℝ) : ℂ)‖
      ≤ 40 * ((|(u : ℝ)| + |(v : ℝ)| + 1) * envF y u v) := by
  rw [norm_mul, norm_mul, norm_mul]
  have h1 : ‖((w : ℤ) : ℂ)‖ = |(w : ℝ)| := by
    rw [show ((w : ℤ) : ℂ) = ((w : ℝ) : ℂ) from by push_cast; rfl, Complex.norm_real,
      Real.norm_eq_abs]
  have h2 : ‖((envF y u v : ℝ) : ℂ)‖ = envF y u v := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (envF_nonneg y u v)]
  have h3 : ‖(c : ℂ)‖ = c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc]
  rw [h1, h2, h3]
  have he := envF_nonneg y u v
  have hwn := abs_nonneg (w : ℝ)
  have hsn := norm_nonneg s
  calc c * |(w : ℝ)| * ‖s‖ * envF y u v
      ≤ c * |(w : ℝ)| * 1 * envF y u v := by
        apply mul_le_mul_of_nonneg_right _ he
        exact mul_le_mul_of_nonneg_left hs (by positivity)
    _ = c * |(w : ℝ)| * envF y u v := by ring
    _ ≤ 40 * (|(u : ℝ)| + |(v : ℝ)| + 1) * envF y u v :=
        mul_le_mul_of_nonneg_right hw he
    _ = 40 * ((|(u : ℝ)| + |(v : ℝ)| + 1) * envF y u v) := by ring

private lemma norm_sgn_chi_le (a N : ℤ) : ‖sgn4 a * ((chi5 N : ℤ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have h1 := norm_sgn4_le a
  have h2 := norm_chi5_le N
  have h3 := norm_nonneg (sgn4 a)
  have h4 := norm_nonneg ((chi5 N : ℤ) : ℂ)
  nlinarith

private lemma norm_cs_chi_le (a N : ℤ) : ‖cs4 a * ((chi5 N : ℤ) : ℂ)‖ ≤ 1 := by
  rw [norm_mul]
  have h1 := norm_cs4_le a
  have h2 := norm_chi5_le N
  have h3 := norm_nonneg (cs4 a)
  have h4 := norm_nonneg ((chi5 N : ℤ) : ℂ)
  nlinarith

private lemma weight_sum_le (u v : ℤ) :
    (10 : ℝ) * |((u + v : ℤ) : ℝ)| ≤ 40 * (|(u : ℝ)| + |(v : ℝ)| + 1) := by
  have h : |((u + v : ℤ) : ℝ)| ≤ |(u : ℝ)| + |(v : ℝ)| := by
    push_cast
    exact abs_add_le _ _
  have h1 := abs_nonneg (u : ℝ)
  have h2 := abs_nonneg (v : ℝ)
  linarith

private lemma weight_fst_le (u v : ℤ) (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 40) :
    c * |(u : ℝ)| ≤ 40 * (|(u : ℝ)| + |(v : ℝ)| + 1) := by
  have h1 := abs_nonneg (u : ℝ)
  have h2 := abs_nonneg (v : ℝ)
  nlinarith

private lemma summable_gLadder5 {y : ℝ} (hy : 0 < y) : Summable (gLadder5 y) := by
  refine summable_of_le_envF hy fun p => ?_
  obtain ⟨u, v⟩ := p
  show ‖10 * ((u + v : ℤ) : ℂ) * sgn4 (u + v) * ((chi5 (2 * (u ^ 2 + v ^ 2)) : ℤ) : ℂ) *
      ((envF y u v : ℝ) : ℂ)‖ ≤ _
  rw [show (10 : ℂ) * ((u + v : ℤ) : ℂ) * sgn4 (u + v) *
        ((chi5 (2 * (u ^ 2 + v ^ 2)) : ℤ) : ℂ) * ((envF y u v : ℝ) : ℂ)
      = ((10 : ℝ) : ℂ) * ((u + v : ℤ) : ℂ) *
        (sgn4 (u + v) * ((chi5 (2 * (u ^ 2 + v ^ 2)) : ℤ) : ℂ)) *
        ((envF y u v : ℝ) : ℂ) from by push_cast; ring]
  exact norm_weight_le y u v (u + v) 10 _ (norm_sgn_chi_le _ _) (by norm_num)
    (weight_sum_le u v)

private lemma summable_piece {y : ℝ} (hy : 0 < y) (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 40)
    (P : ℤ × ℤ → Prop) [DecidablePred P] (S : ℤ × ℤ → ℂ) (hS : ∀ p, ‖S p‖ ≤ 1) :
    Summable fun p : ℤ × ℤ =>
      if P p then (c : ℂ) * (p.1 : ℂ) * S p * ((envF y p.1 p.2 : ℝ) : ℂ) else 0 := by
  refine summable_of_le_envF hy fun p => ?_
  obtain ⟨u, v⟩ := p
  split_ifs
  · exact norm_weight_le y u v u c _ (hS _) hc (weight_fst_le u v c hc hc')
  · simp only [norm_zero]
    exact mul_nonneg (by norm_num)
      (mul_nonneg (by positivity) (envF_nonneg y u v))

private lemma summable_hHalf5 {y : ℝ} (hy : 0 < y) : Summable (hHalf5 y) := by
  have h := summable_piece hy 10 (by norm_num) (by norm_num)
    (fun p : ℤ × ℤ => p.2 % 2 = 0)
    (fun p => sgn4 (p.1 + p.2) * ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ))
    (fun p => norm_sgn_chi_le _ _)
  refine h.congr fun p => ?_
  unfold hHalf5
  split_ifs <;> push_cast <;> ring

private lemma summable_gEven5 {y : ℝ} (hy : 0 < y) : Summable (gEven5 y) := by
  refine Summable.of_norm_bounded (summable_gLadder5 hy).norm fun p => ?_
  unfold gEven5
  split_ifs
  · exact le_rfl
  · simp

private lemma summable_gOddV5 {y : ℝ} (hy : 0 < y) : Summable (gOddV5 y) := by
  refine Summable.of_norm_bounded (summable_gLadder5 hy).norm fun p => ?_
  unfold gOddV5
  split_ifs
  · simp
  · exact le_rfl

private lemma summable_hPlus5 {y : ℝ} (hy : 0 < y) : Summable (hPlus5 y) := by
  have h := summable_piece hy 10 (by norm_num) (by norm_num)
    (fun p : ℤ × ℤ => (p.1 + p.2) % 4 = 1 ∧ p.2 % 2 = 0)
    (fun p => ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ))
    (fun p => norm_chi5_le _)
  refine h.congr fun p => ?_
  unfold hPlus5
  split_ifs <;> push_cast <;> ring

private lemma summable_hMinus5 {y : ℝ} (hy : 0 < y) : Summable (hMinus5 y) := by
  have h := summable_piece hy 10 (by norm_num) (by norm_num)
    (fun p : ℤ × ℤ => (p.1 + p.2) % 4 = 3 ∧ p.2 % 2 = 0)
    (fun p => ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ))
    (fun p => norm_chi5_le _)
  refine h.congr fun p => ?_
  unfold hMinus5
  split_ifs <;> push_cast <;> ring

private lemma summable_aPiece5 {y : ℝ} (hy : 0 < y) : Summable (aPiece5 y) := by
  have h := summable_piece hy 10 (by norm_num) (by norm_num)
    (fun p : ℤ × ℤ => p.1 % 4 = 1 ∧ p.2 % 4 = 0)
    (fun p => ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ))
    (fun p => norm_chi5_le _)
  refine h.congr fun p => ?_
  unfold aPiece5
  split_ifs <;> push_cast <;> ring

private lemma summable_bPiece5 {y : ℝ} (hy : 0 < y) : Summable (bPiece5 y) := by
  have h := summable_piece hy 10 (by norm_num) (by norm_num)
    (fun p : ℤ × ℤ => p.1 % 4 = 3 ∧ p.2 % 4 = 2)
    (fun p => ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ))
    (fun p => norm_chi5_le _)
  refine h.congr fun p => ?_
  unfold bPiece5
  split_ifs <;> push_cast <;> ring

private lemma summable_bMirror5 {y : ℝ} (hy : 0 < y) : Summable (bMirror5 y) := by
  have h := summable_piece hy 10 (by norm_num) (by norm_num)
    (fun p : ℤ × ℤ => p.1 % 4 = 1 ∧ p.2 % 4 = 2)
    (fun p => ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ))
    (fun p => norm_chi5_le _)
  refine h.congr fun p => ?_
  unfold bMirror5
  split_ifs <;> push_cast <;> ring

private lemma summable_dual5Even {y : ℝ} (hy : 0 < y) : Summable (dual5Even y) := by
  refine Summable.of_norm_bounded (summable_dual5 hy).norm fun p => ?_
  unfold dual5Even
  split_ifs
  · exact le_rfl
  · simp

private lemma summable_dual5Odd {y : ℝ} (hy : 0 < y) : Summable (dual5Odd y) := by
  refine Summable.of_norm_bounded (summable_dual5 hy).norm fun p => ?_
  unfold dual5Odd
  split_ifs
  · simp
  · exact le_rfl

/-! ## 12. Pointwise identities along the ladder -/

private lemma envF_neg_snd (y : ℝ) (u v : ℤ) : envF y u (-v) = envF y u v := by
  unfold envF; congr 1; push_cast; ring

private lemma envF_neg_both (y : ℝ) (u v : ℤ) : envF y (-u) (-v) = envF y u v := by
  unfold envF; congr 1; push_cast; ring

private lemma envF_swap (y : ℝ) (u v : ℤ) : envF y v u = envF y u v := by
  unfold envF; congr 1; push_cast; ring

private lemma quarter_phase_odd (p : ℤ) :
    -I * cexp (π * I * ((2 * p + 1 : ℤ) : ℂ) / 2) = sgn4 (2 * p + 1) := by
  rcases Int.even_or_odd p with ⟨t, rfl⟩ | ⟨t, rfl⟩
  · have h1 : sgn4 (2 * (t + t) + 1) = 1 := by
      unfold sgn4; rw [if_pos (by omega)]
    have h2 : cexp (π * I * ((2 * (t + t) + 1 : ℤ) : ℂ) / 2) = I := by
      rw [show (π : ℂ) * I * ((2 * (t + t) + 1 : ℤ) : ℂ) / 2
            = (t : ℤ) * (2 * π * I) + π / 2 * I from by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul,
        Complex.exp_pi_div_two_mul_I]
    rw [h1, h2]
    linear_combination -Complex.I_mul_I
  · have h1 : sgn4 (2 * (2 * t + 1) + 1) = -1 := by
      unfold sgn4; rw [if_neg (by omega), if_pos (by omega)]
    have h2 : cexp (π * I * ((2 * (2 * t + 1) + 1 : ℤ) : ℂ) / 2) = -I := by
      rw [show (π : ℂ) * I * ((2 * (2 * t + 1) + 1 : ℤ) : ℂ) / 2
            = (t : ℤ) * (2 * π * I) + (π * I + π / 2 * I) from by push_cast; ring,
        Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, one_mul, Complex.exp_add,
        Complex.exp_pi_mul_I, Complex.exp_pi_div_two_mul_I]
      ring
    rw [h1, h2]
    linear_combination Complex.I_mul_I

private lemma quarter_phase_neg_even {n : ℤ} (hn : n % 2 = 0) :
    cexp (π * I * ((-n : ℤ) : ℂ) / 2) = cexp (π * I * (n : ℂ) / 2) := by
  obtain ⟨r, rfl⟩ : ∃ r, n = 2 * r := ⟨n / 2, by omega⟩
  rw [show (π : ℂ) * I * ((-(2 * r) : ℤ) : ℂ) / 2
        = π * I * ((2 * r : ℤ) : ℂ) / 2 + (-r : ℤ) * (2 * π * I) from by push_cast; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- The even part of the dual family dies under the involution `n ↦ −n`. -/
private lemma tsum_dual5Even_eq_zero (y : ℝ) : ∑' p : ℤ × ℤ, dual5Even y p = 0 := by
  have h1 : ∑' p : ℤ × ℤ, dual5Even y (((Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)) p)
      = ∑' p : ℤ × ℤ, dual5Even y p :=
    ((Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)).tsum_eq (dual5Even y)
  have h2 : ∀ p : ℤ × ℤ, dual5Even y (((Equiv.neg ℤ).prodCongr (Equiv.refl ℤ)) p)
      = -dual5Even y p := by
    rintro ⟨n, m⟩
    show dual5Even y (-n, m) = -dual5Even y (n, m)
    by_cases hn : n % 2 = 0
    · simp only [dual5Even]
      rw [if_pos (show (-n) % 2 = 0 by omega), if_pos hn]
      show dual5 y (-n, m) = -dual5 y (n, m)
      unfold dual5
      show -I * ((-n : ℤ) : ℂ) * (10 * cexp (π * I * ((-n : ℤ) : ℂ) / 2) * oddInd m *
          (chi5 ((-n) ^ 2 + m ^ 2) : ℂ)) * ((envP y (-n) m : ℝ) : ℂ) = _
      rw [quarter_phase_neg_even hn,
        show ((-n : ℤ) : ℂ) = -((n : ℤ) : ℂ) from by push_cast; ring,
        show chi5 ((-n) ^ 2 + m ^ 2) = chi5 (n ^ 2 + m ^ 2) from by ring_nf,
        show envP y (-n) m = envP y n m from by unfold envP; congr 1; push_cast; ring]
      ring
    · simp only [dual5Even]
      rw [if_neg (show ¬((-n) % 2 = 0) by omega), if_neg hn, neg_zero]
  have h3 : ∑' p : ℤ × ℤ, dual5Even y p = -∑' p : ℤ × ℤ, dual5Even y p := by
    conv_lhs => rw [← h1, tsum_congr h2]
    exact tsum_neg
  linear_combination h3 / 2

/-- The odd part transports through `(p, q) ↦ (2p+1, 2q+1)` and the fold. -/
private lemma dual5Odd_comp_bothOdd (y : ℝ) (q : ℤ × ℤ) :
    dual5Odd y (bothOddEmb q) = gLadder5 y (foldMap q) := by
  obtain ⟨p, t⟩ := q
  show dual5Odd y (2 * p + 1, 2 * t + 1) = gLadder5 y (p + t + 1, p - t)
  simp only [dual5Odd]
  rw [if_neg (show ¬((2 * p + 1) % 2 = 0) by omega)]
  show dual5 y (2 * p + 1, 2 * t + 1) = _
  unfold dual5 gLadder5
  show -I * ((2 * p + 1 : ℤ) : ℂ) * (10 * cexp (π * I * ((2 * p + 1 : ℤ) : ℂ) / 2) *
      oddInd (2 * t + 1) * (chi5 ((2 * p + 1) ^ 2 + (2 * t + 1) ^ 2) : ℂ)) *
      ((envP y (2 * p + 1) (2 * t + 1) : ℝ) : ℂ) = _
  have hoi : oddInd (2 * t + 1) = 1 := by
    unfold oddInd
    rw [if_neg (by omega)]
  have hchi : chi5 ((2 * p + 1) ^ 2 + (2 * t + 1) ^ 2)
      = chi5 (2 * ((p + t + 1) ^ 2 + (p - t) ^ 2)) := by
    rw [show (2 * p + 1) ^ 2 + (2 * t + 1) ^ 2 = 2 * ((p + t + 1) ^ 2 + (p - t) ^ 2) from
      by ring]
  have henv : envP y (2 * p + 1) (2 * t + 1) = envF y (p + t + 1) (p - t) := by
    unfold envP envF
    congr 1
    push_cast
    ring
  rw [hoi, hchi, henv, show (p + t + 1) + (p - t) = 2 * p + 1 from by ring]
  have hq := quarter_phase_odd p
  linear_combination (10 * ((2 * p + 1 : ℤ) : ℂ) * (chi5 (2 * ((p + t + 1) ^ 2 +
    (p - t) ^ 2)) : ℂ) * ((envF y (p + t + 1) (p - t) : ℝ) : ℂ)) * hq

private lemma tsum_dual5Odd_eq_gLadder5 (y : ℝ) :
    ∑' p : ℤ × ℤ, dual5Odd y p = ∑' p : ℤ × ℤ, gLadder5 y p := by
  have h1 : ∑' q : ℤ × ℤ, dual5Odd y (bothOddEmb q) = ∑' p : ℤ × ℤ, dual5Odd y p := by
    refine bothOddEmb_injective.tsum_eq ?_
    rw [Function.support_subset_iff]
    rintro ⟨n, m⟩ hne
    have hn : ¬(n % 2 = 0) := by
      intro h
      apply hne
      simp only [dual5Odd]
      rw [if_pos h]
    have hm : ¬(m % 2 = 0) := by
      intro h
      apply hne
      simp only [dual5Odd]
      rw [if_neg hn]
      unfold dual5
      show -I * (n : ℂ) * (10 * cexp (π * I * (n : ℂ) / 2) * oddInd m *
          (chi5 (n ^ 2 + m ^ 2) : ℂ)) * ((envP y n m : ℝ) : ℂ) = 0
      rw [show oddInd m = 0 from by unfold oddInd; rw [if_pos h]]
      ring
    exact ⟨((n - 1) / 2, (m - 1) / 2), by
      simp only [bothOddEmb, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩⟩
  have h2 : ∑' q : ℤ × ℤ, gLadder5 y (foldMap q) = ∑' p : ℤ × ℤ, gLadder5 y p := by
    refine foldMap_injective.tsum_eq ?_
    rw [Function.support_subset_iff]
    rintro ⟨u, v⟩ hne
    have hodd : (u + v) % 4 = 1 ∨ (u + v) % 4 = 3 := by
      by_contra hc
      push_neg at hc
      apply hne
      show 10 * ((u + v : ℤ) : ℂ) * sgn4 (u + v) * _ * _ = 0
      rw [show sgn4 (u + v) = 0 from by unfold sgn4; rw [if_neg hc.1, if_neg hc.2]]
      ring
    exact ⟨((u + v - 1) / 2, (u - v - 1) / 2), by
      simp only [foldMap, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩⟩
  rw [← h1, ← h2]
  exact tsum_congr fun q => dual5Odd_comp_bothOdd y q

/-- The swap fold. -/
private lemma gOddV5_comp_swap (y : ℝ) (p : ℤ × ℤ) :
    gOddV5 y ((Equiv.prodComm ℤ ℤ) p) = gEven5 y p := by
  obtain ⟨u, v⟩ := p
  show gOddV5 y (v, u) = gEven5 y (u, v)
  have hswap : gLadder5 y (v, u) = gLadder5 y (u, v) := by
    unfold gLadder5
    rw [show v + u = u + v from by ring, envF_swap,
      show v ^ 2 + u ^ 2 = u ^ 2 + v ^ 2 from by ring]
  have hzero : ∀ a b : ℤ, (a + b) % 2 = 0 → gLadder5 y (a, b) = 0 := by
    intro a b h
    show 10 * ((a + b : ℤ) : ℂ) * sgn4 (a + b) * _ * _ = 0
    rw [show sgn4 (a + b) = 0 from by unfold sgn4; rw [if_neg (by omega), if_neg (by omega)]]
    ring
  simp only [gOddV5, gEven5]
  by_cases hu : u % 2 = 0
  · rw [if_pos hu]
    by_cases hv : v % 2 = 0
    · rw [if_pos hv, hzero u v (by omega)]
    · rw [if_neg hv]
  · rw [if_neg hu]
    by_cases hv : v % 2 = 0
    · rw [if_pos hv, hswap]
    · rw [if_neg hv, hzero v u (by omega)]

private lemma tsum_gLadder5_eq_two_gEven5 {y : ℝ} (hy : 0 < y) :
    ∑' p : ℤ × ℤ, gLadder5 y p = 2 * ∑' p : ℤ × ℤ, gEven5 y p := by
  have hpt : ∀ p : ℤ × ℤ, gLadder5 y p = gEven5 y p + gOddV5 y p := by
    intro p
    simp only [gEven5, gOddV5]
    split_ifs <;> ring
  have hswap : ∑' p : ℤ × ℤ, gOddV5 y p = ∑' p : ℤ × ℤ, gEven5 y p := by
    rw [← (Equiv.prodComm ℤ ℤ).tsum_eq (gOddV5 y)]
    exact tsum_congr fun p => gOddV5_comp_swap y p
  rw [tsum_congr hpt, (summable_gEven5 hy).tsum_add (summable_gOddV5 hy), hswap]
  ring

/-- The `v ↦ −v` fold replaces the weight `u+v` by `u`. -/
private lemma gEven5_add_negSnd (y : ℝ) (p : ℤ × ℤ) :
    gEven5 y p + gEven5 y (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)) p)
      = 2 * hHalf5 y p := by
  obtain ⟨u, v⟩ := p
  show gEven5 y (u, v) + gEven5 y (u, -v) = 2 * hHalf5 y (u, v)
  simp only [gEven5, hHalf5]
  by_cases hv : v % 2 = 0
  · rw [if_pos hv, if_pos (show (-v) % 2 = 0 by omega), if_pos hv]
    unfold gLadder5
    show 10 * ((u + v : ℤ) : ℂ) * sgn4 (u + v) * ((chi5 (2 * (u ^ 2 + v ^ 2)) : ℤ) : ℂ) *
        ((envF y u v : ℝ) : ℂ) +
        10 * ((u + -v : ℤ) : ℂ) * sgn4 (u + -v) *
          ((chi5 (2 * (u ^ 2 + (-v) ^ 2)) : ℤ) : ℂ) * ((envF y u (-v) : ℝ) : ℂ) = _
    rw [show u + -v = u - v from by ring,
      show sgn4 (u - v) = sgn4 (u + v) from by
        unfold sgn4; rw [show (u - v) % 4 = (u + v) % 4 from by omega],
      envF_neg_snd, show 2 * (u ^ 2 + (-v) ^ 2) = 2 * (u ^ 2 + v ^ 2) from by ring]
    push_cast
    ring
  · rw [if_neg hv, if_neg (show ¬((-v) % 2 = 0) by omega), if_neg hv]
    ring

private lemma tsum_gEven5_eq_hHalf5 {y : ℝ} (hy : 0 < y) :
    ∑' p : ℤ × ℤ, gEven5 y p = ∑' p : ℤ × ℤ, hHalf5 y p := by
  have hcomp : Summable (gEven5 y ∘ ((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ))) :=
    (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)).summable_iff).mpr (summable_gEven5 hy)
  have h2 : (2 : ℂ) * ∑' p : ℤ × ℤ, gEven5 y p = 2 * ∑' p : ℤ × ℤ, hHalf5 y p := by
    calc (2 : ℂ) * ∑' p : ℤ × ℤ, gEven5 y p
        = ∑' p : ℤ × ℤ, gEven5 y p
            + ∑' p : ℤ × ℤ, gEven5 y (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)) p) := by
          rw [((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)).tsum_eq (gEven5 y)]
          ring
      _ = ∑' p : ℤ × ℤ, (gEven5 y p
            + gEven5 y (((Equiv.refl ℤ).prodCongr (Equiv.neg ℤ)) p)) :=
          ((summable_gEven5 hy).tsum_add hcomp).symm
      _ = ∑' p : ℤ × ℤ, (2 : ℂ) * hHalf5 y p := tsum_congr fun p => gEven5_add_negSnd y p
      _ = 2 * ∑' p : ℤ × ℤ, hHalf5 y p := tsum_mul_left
  exact mul_left_cancel₀ two_ne_zero h2

/-- The class fold. -/
private lemma tsum_hHalf5_eq_two_hPlus5 {y : ℝ} (hy : 0 < y) :
    ∑' p : ℤ × ℤ, hHalf5 y p = 2 * ∑' p : ℤ × ℤ, hPlus5 y p := by
  have hpt : ∀ p : ℤ × ℤ, hHalf5 y p = hPlus5 y p - hMinus5 y p := by
    rintro ⟨u, v⟩
    simp only [hHalf5, hPlus5, hMinus5, sgn4]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have hneg : ∑' p : ℤ × ℤ, hMinus5 y p = -∑' p : ℤ × ℤ, hPlus5 y p := by
    have h1 : ∑' p : ℤ × ℤ, hMinus5 y (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) p)
        = ∑' p : ℤ × ℤ, hMinus5 y p :=
      ((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)).tsum_eq (hMinus5 y)
    have h2 : ∀ p : ℤ × ℤ, hMinus5 y (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) p)
        = -hPlus5 y p := by
      rintro ⟨u, v⟩
      show hMinus5 y (-u, -v) = -hPlus5 y (u, v)
      simp only [hMinus5, hPlus5]
      by_cases h : (u + v) % 4 = 1 ∧ v % 2 = 0
      · rw [if_pos (show (-u + -v) % 4 = 3 ∧ (-v) % 2 = 0 by omega), if_pos h,
          envF_neg_both, show 2 * ((-u) ^ 2 + (-v) ^ 2) = 2 * (u ^ 2 + v ^ 2) from by ring]
        push_cast
        ring
      · rw [if_neg (show ¬((-u + -v) % 4 = 3 ∧ (-v) % 2 = 0) by omega), if_neg h, neg_zero]
    rw [← h1, tsum_congr h2]
    exact tsum_neg
  rw [tsum_congr hpt, (summable_hPlus5 hy).tsum_sub (summable_hMinus5 hy), hneg]
  ring

/-- The gather onto the cosine-signed target. -/
private lemma tsum_hFinal5_eq_four_hPlus5 {y : ℝ} (hy : 0 < y) :
    ∑' p : ℤ × ℤ, hFinal5 y p = 4 * ∑' p : ℤ × ℤ, hPlus5 y p := by
  have hsplit : ∀ p : ℤ × ℤ, hPlus5 y p = aPiece5 y p + bPiece5 y p := by
    rintro ⟨u, v⟩
    simp only [hPlus5, aPiece5, bPiece5]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have hfin : ∀ p : ℤ × ℤ, hFinal5 y p = 4 * aPiece5 y p - 4 * bMirror5 y p := by
    rintro ⟨u, v⟩
    simp only [hFinal5, aPiece5, bMirror5, cs4]
    split_ifs <;> first | ring1 | (exfalso; omega)
  have hbm : ∑' p : ℤ × ℤ, bPiece5 y p = -∑' p : ℤ × ℤ, bMirror5 y p := by
    have h1 : ∑' p : ℤ × ℤ, bPiece5 y (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) p)
        = ∑' p : ℤ × ℤ, bPiece5 y p :=
      ((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)).tsum_eq (bPiece5 y)
    have h2 : ∀ p : ℤ × ℤ, bPiece5 y (((Equiv.neg ℤ).prodCongr (Equiv.neg ℤ)) p)
        = -bMirror5 y p := by
      rintro ⟨u, v⟩
      show bPiece5 y (-u, -v) = -bMirror5 y (u, v)
      simp only [bPiece5, bMirror5]
      by_cases h : u % 4 = 1 ∧ v % 4 = 2
      · rw [if_pos (show (-u) % 4 = 3 ∧ (-v) % 4 = 2 by omega), if_pos h, envF_neg_both,
          show 2 * ((-u) ^ 2 + (-v) ^ 2) = 2 * (u ^ 2 + v ^ 2) from by ring]
        push_cast
        ring
      · rw [if_neg (show ¬((-u) % 4 = 3 ∧ (-v) % 4 = 2) by omega), if_neg h, neg_zero]
    rw [← h1, tsum_congr h2]
    exact tsum_neg
  calc ∑' p : ℤ × ℤ, hFinal5 y p
      = ∑' p : ℤ × ℤ, ((4 : ℂ) * aPiece5 y p - 4 * bMirror5 y p) := tsum_congr hfin
    _ = (∑' p : ℤ × ℤ, (4 : ℂ) * aPiece5 y p) - ∑' p : ℤ × ℤ, (4 : ℂ) * bMirror5 y p :=
        ((summable_aPiece5 hy).mul_left 4).tsum_sub ((summable_bMirror5 hy).mul_left 4)
    _ = 4 * (∑' p : ℤ × ℤ, aPiece5 y p) - 4 * ∑' p : ℤ × ℤ, bMirror5 y p := by
        rw [tsum_mul_left, tsum_mul_left]
    _ = 4 * ((∑' p : ℤ × ℤ, aPiece5 y p) + ∑' p : ℤ × ℤ, bPiece5 y p) := by
        rw [hbm]; ring
    _ = 4 * ∑' p : ℤ × ℤ, (aPiece5 y p + bPiece5 y p) := by
        rw [(summable_aPiece5 hy).tsum_add (summable_bPiece5 hy)]
    _ = 4 * ∑' p : ℤ × ℤ, hPlus5 y p := by
        rw [tsum_congr hsplit]

/-- The complete dual chain: the collapsed dual family equals the gathered target. -/
private lemma tsum_dual5_eq_hFinal5 {y : ℝ} (hy : 0 < y) :
    ∑' p : ℤ × ℤ, dual5 y p = ∑' p : ℤ × ℤ, hFinal5 y p := by
  have hsplit : ∀ p : ℤ × ℤ, dual5 y p = dual5Even y p + dual5Odd y p := by
    intro p
    simp only [dual5Even, dual5Odd]
    split_ifs <;> ring
  rw [tsum_congr hsplit, (summable_dual5Even hy).tsum_add (summable_dual5Odd hy),
    tsum_dual5Even_eq_zero y, zero_add, tsum_dual5Odd_eq_gLadder5 y,
    tsum_gLadder5_eq_two_gEven5 hy, tsum_gEven5_eq_hHalf5 hy, tsum_hHalf5_eq_two_hPlus5 hy,
    tsum_hFinal5_eq_four_hPlus5 hy]
  ring

/-! ## 13. The grid landing and the primal reassembly -/

private lemma summable_hFinal5 {y : ℝ} (hy : 0 < y) : Summable (hFinal5 y) := by
  have h := summable_piece hy 40 (by norm_num) (by norm_num)
    (fun p : ℤ × ℤ => p.1 % 4 = 1)
    (fun p => cs4 p.2 * ((chi5 (2 * (p.1 ^ 2 + p.2 ^ 2)) : ℤ) : ℂ))
    (fun p => norm_cs_chi_le _ _)
  refine h.congr fun p => ?_
  unfold hFinal5
  split_ifs <;> push_cast <;> ring

private lemma hFinal5_support (y : ℝ) : ∀ p ∉ Set.range gridEmb, hFinal5 y p = 0 := by
  rintro ⟨u, v⟩ hp
  have hcond : ¬(u % 4 = 1 ∧ v % 2 = 0) := by
    intro ⟨hu, hv⟩
    exact hp ⟨((u - 1) / 4, v / 2), by
      simp only [gridEmb, Prod.mk.injEq]
      exact ⟨by omega, by omega⟩⟩
  by_cases hu : u % 4 = 1
  · have hv : ¬(v % 2 = 0) := fun hv => hcond ⟨hu, hv⟩
    show (if u % 4 = 1 then _ else 0) = 0
    rw [if_pos hu, show cs4 v = 0 from by
      unfold cs4; rw [if_neg (by omega), if_neg (by omega)]]
    ring
  · show (if u % 4 = 1 then _ else 0) = 0
    rw [if_neg hu]

private lemma tsum_gridEmb_eq_hFinal5 (y : ℝ) :
    ∑' q : ℤ × ℤ, hFinal5 y (gridEmb q) = ∑' p : ℤ × ℤ, hFinal5 y p := by
  refine gridEmb_injective.tsum_eq ?_
  rw [Function.support_subset_iff]
  intro p hne
  by_contra hc
  exact hne (hFinal5_support y p hc)

/-- The residue equivalence: `(Fin 5 × Fin 10) × ℤ² ≃ ℤ²` by the division algorithm. -/
private def resEquiv : (Fin 5 × Fin 10) × (ℤ × ℤ) ≃ ℤ × ℤ where
  toFun x := (5 * x.2.1 + ((x.1.1 : ℕ) : ℤ), 10 * x.2.2 + ((x.1.2 : ℕ) : ℤ))
  invFun p := ((⟨(p.1 % 5).toNat, by omega⟩, ⟨(p.2 % 10).toNat, by omega⟩),
    (p.1 / 5, p.2 / 10))
  left_inv := by
    rintro ⟨⟨e, d⟩, ⟨n', m'⟩⟩
    have he := e.isLt
    have hd := d.isLt
    simp only [Prod.mk.injEq]
    refine ⟨⟨Fin.ext ?_, Fin.ext ?_⟩, ?_, ?_⟩
    · show ((5 * n' + ((e : ℕ) : ℤ)) % 5).toNat = (e : ℕ)
      omega
    · show ((10 * m' + ((d : ℕ) : ℤ)) % 10).toNat = (d : ℕ)
      omega
    · show (5 * n' + ((e : ℕ) : ℤ)) / 5 = n'
      omega
    · show (10 * m' + ((d : ℕ) : ℤ)) / 10 = m'
      omega
  right_inv := by
    rintro ⟨k, l⟩
    simp only [Prod.mk.injEq]
    constructor <;> omega

/-- The `oddKernel` summand at scale `800y`, coerced whole. -/
private def oddT (y : ℝ) (e : ℕ) (n : ℤ) : ℂ :=
  ((((n : ℝ) + (4 * (e : ℝ) + 1) / 20) *
      rexp (-π * ((n : ℝ) + (4 * (e : ℝ) + 1) / 20) ^ 2 * (800 * y)) : ℝ) : ℂ)

/-- The `evenKernel` summand at scale `800y`, coerced whole. -/
private def evenT (y : ℝ) (d : ℕ) (m : ℤ) : ℂ :=
  ((rexp (-π * ((m : ℝ) + (d : ℝ) / 10) ^ 2 * (800 * y)) : ℝ) : ℂ)

/-- The kernel product at scale `800y`, as a lattice double sum. -/
private def primalT (y : ℝ) (e d : ℕ) (p : ℤ × ℤ) : ℂ := oddT y e p.1 * evenT y d p.2

private lemma hasSum_oddT {y : ℝ} (hy : 0 < y) (e : ℕ) :
    HasSum (oddT y e)
      ((oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (800 * y) : ℝ) : ℂ) :=
  Complex.hasSum_ofReal.mpr
    (HurwitzZeta.hasSum_int_oddKernel ((4 * (e : ℝ) + 1) / 20)
      (show (0 : ℝ) < 800 * y by positivity))

private lemma hasSum_evenT {y : ℝ} (hy : 0 < y) (d : ℕ) :
    HasSum (evenT y d)
      ((evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (800 * y) : ℝ) : ℂ) :=
  Complex.hasSum_ofReal.mpr
    (HurwitzZeta.hasSum_int_evenKernel ((d : ℝ) / 10)
      (show (0 : ℝ) < 800 * y by positivity))

private lemma summable_primalT {y : ℝ} (hy : 0 < y) (e d : ℕ) :
    Summable (primalT y e d) :=
  summable_norm_iff.mp
    ((summable_norm_iff.mpr (hasSum_oddT hy e).summable).mul_norm
      (summable_norm_iff.mpr (hasSum_evenT hy d).summable))

private lemma oddK_evenK_product {y : ℝ} (hy : 0 < y) (e d : ℕ) :
    ((oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (800 * y) : ℝ) : ℂ) *
        ((evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (800 * y) : ℝ) : ℂ)
      = ∑' p : ℤ × ℤ, primalT y e d p :=
  (hasSum_oddT hy e).mul_eq (hasSum_evenT hy d) (summable_primalT hy e d).hasSum

private lemma cs4_grid (m' : ℤ) (d : ℕ) :
    cs4 (2 * (10 * m' + (d : ℤ))) = (((-1 : ℤ) ^ d : ℤ) : ℂ) := by
  rcases Nat.even_or_odd d with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [show cs4 (2 * (10 * m' + (d : ℤ))) = 1 from by
      unfold cs4; rw [if_pos (by omega)]]
    rw [ht, show ((-1 : ℤ) ^ (t + t) : ℤ) = 1 from by
      rw [show t + t = 2 * t from by ring, pow_mul]; norm_num]
    norm_num
  · rw [show cs4 (2 * (10 * m' + (d : ℤ))) = -1 from by
      unfold cs4; rw [if_neg (by omega), if_pos (by omega)]]
    rw [ht, show ((-1 : ℤ) ^ (2 * t + 1) : ℤ) = -1 from by
      rw [pow_add, pow_mul]; norm_num]
    norm_num

private lemma chi5_grid (n' m' : ℤ) (e d : ℕ) :
    chi5 (2 * ((4 * (5 * n' + (e : ℤ)) + 1) ^ 2 + (2 * (10 * m' + (d : ℤ))) ^ 2))
      = -chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) := by
  have hu : (4 * (5 * n' + (e : ℤ)) + 1) ≡ 4 * (e : ℤ) + 1 [ZMOD 5] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-4 * n', by ring⟩
  have hv : (2 * (10 * m' + (d : ℤ))) ≡ 2 * (d : ℤ) [ZMOD 5] := by
    rw [Int.modEq_iff_dvd]
    exact ⟨-4 * m', by ring⟩
  have hX : (4 * (5 * n' + (e : ℤ)) + 1) ^ 2 + (2 * (10 * m' + (d : ℤ))) ^ 2
      ≡ (4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2 [ZMOD 5] := by
    have h := (hu.pow 2).add (hv.pow 2)
    have harg : (2 * (d : ℤ)) ^ 2 = 4 * (d : ℤ) ^ 2 := by ring
    rwa [harg] at h
  calc chi5 (2 * ((4 * (5 * n' + (e : ℤ)) + 1) ^ 2 + (2 * (10 * m' + (d : ℤ))) ^ 2))
      = chi5 2 * chi5 ((4 * (5 * n' + (e : ℤ)) + 1) ^ 2 + (2 * (10 * m' + (d : ℤ))) ^ 2) :=
        chi5_mul _ _
    _ = chi5 2 * chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) := by rw [chi5_congr hX]
    _ = -chi5 ((4 * (e : ℤ) + 1) ^ 2 + 4 * (d : ℤ) ^ 2) := by rw [chi5_two]; ring

private lemma envF_grid (y : ℝ) (n' m' : ℤ) (e d : ℕ) :
    envF y (4 * (5 * n' + (e : ℤ)) + 1) (2 * (10 * m' + (d : ℤ)))
      = rexp (-π * ((n' : ℝ) + (4 * (e : ℝ) + 1) / 20) ^ 2 * (800 * y)) *
        rexp (-π * ((m' : ℝ) + (d : ℝ) / 10) ^ 2 * (800 * y)) := by
  unfold envF
  rw [← Real.exp_add]
  congr 1
  push_cast
  ring

/-- The pointwise landing: the gathered target at a grid point is `−800` times the
weighted primal kernel summand. -/
private lemma hFinal5_land (y : ℝ) (e : Fin 5) (d : Fin 10) (q : ℤ × ℤ) :
    hFinal5 y (gridEmb (resEquiv ((e, d), q)))
      = -800 * ((w5 (e : ℕ) (d : ℕ) : ℤ) : ℂ) * primalT y (e : ℕ) (d : ℕ) q := by
  obtain ⟨n', m'⟩ := q
  have hres : resEquiv ((e, d), (n', m'))
      = (5 * n' + ((e : ℕ) : ℤ), 10 * m' + ((d : ℕ) : ℤ)) := rfl
  have hgrid : gridEmb (5 * n' + ((e : ℕ) : ℤ), 10 * m' + ((d : ℕ) : ℤ))
      = (4 * (5 * n' + ((e : ℕ) : ℤ)) + 1, 2 * (10 * m' + ((d : ℕ) : ℤ))) := rfl
  rw [hres, hgrid]
  unfold hFinal5
  rw [if_pos (show (4 * (5 * n' + ((e : ℕ) : ℤ)) + 1) % 4 = 1 by omega)]
  show 40 * ((4 * (5 * n' + ((e : ℕ) : ℤ)) + 1 : ℤ) : ℂ) *
      cs4 (2 * (10 * m' + ((d : ℕ) : ℤ))) * _ * _ = _
  rw [cs4_grid m' (d : ℕ), chi5_grid n' m' (e : ℕ) (d : ℕ), envF_grid y n' m' (e : ℕ) (d : ℕ)]
  unfold w5 primalT oddT evenT
  push_cast
  ring

/-- The primal side: the gathered target equals `−800` times the fifty weighted
`oddKernel`–`evenKernel` products at scale `800y`. -/
private lemma primal_side_eq {y : ℝ} (hy : 0 < y) :
    ∑' p : ℤ × ℤ, hFinal5 y p
      = -800 * ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
          ((w5 e d : ℤ) : ℂ) *
            (((oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (800 * y) : ℝ) : ℂ) *
             ((evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (800 * y) : ℝ) : ℂ)) := by
  rw [← tsum_gridEmb_eq_hFinal5 y]
  rw [← resEquiv.tsum_eq (fun q => hFinal5 y (gridEmb q))]
  have hsum : Summable fun x : (Fin 5 × Fin 10) × (ℤ × ℤ) =>
      hFinal5 y (gridEmb (resEquiv x)) := by
    rw [show (fun x : (Fin 5 × Fin 10) × (ℤ × ℤ) => hFinal5 y (gridEmb (resEquiv x)))
        = ((hFinal5 y ∘ gridEmb) ∘ resEquiv) from rfl]
    rw [resEquiv.summable_iff]
    exact (gridEmb_injective.summable_iff (hFinal5_support y)).mpr (summable_hFinal5 hy)
  rw [hsum.tsum_prod' hsum.prod_factor, tsum_fintype]
  rw [Fintype.sum_prod_type]
  have hout : ∀ e : Fin 5, ∀ d : Fin 10,
      ∑' q : ℤ × ℤ, hFinal5 y (gridEmb (resEquiv ((e, d), q)))
        = -800 * (((w5 (e : ℕ) (d : ℕ) : ℤ) : ℂ) *
            (((oddKernel (((4 * ((e : ℕ) : ℝ) + 1) / 20 : ℝ) : UnitAddCircle)
                (800 * y) : ℝ) : ℂ) *
             ((evenKernel ((((d : ℕ) : ℝ) / 10 : ℝ) : UnitAddCircle) (800 * y) : ℝ) : ℂ))) := by
    intro e d
    rw [tsum_congr fun q => hFinal5_land y e d q]
    rw [tsum_mul_left, oddK_evenK_product hy (e : ℕ) (d : ℕ)]
    ring
  rw [Finset.sum_congr rfl fun e _ => Finset.sum_congr rfl fun d _ => hout e d]
  have hpull : ∑ e : Fin 5, ∑ d : Fin 10,
      (-800 : ℂ) * (((w5 (e : ℕ) (d : ℕ) : ℤ) : ℂ) *
        (((oddKernel (((4 * ((e : ℕ) : ℝ) + 1) / 20 : ℝ) : UnitAddCircle)
            (800 * y) : ℝ) : ℂ) *
         ((evenKernel ((((d : ℕ) : ℝ) / 10 : ℝ) : UnitAddCircle) (800 * y) : ℝ) : ℂ)))
      = -800 * ∑ e : Fin 5, ∑ d : Fin 10,
          ((w5 (e : ℕ) (d : ℕ) : ℤ) : ℂ) *
            (((oddKernel (((4 * ((e : ℕ) : ℝ) + 1) / 20 : ℝ) : UnitAddCircle)
                (800 * y) : ℝ) : ℂ) *
             ((evenKernel ((((d : ℕ) : ℝ) / 10 : ℝ) : UnitAddCircle) (800 * y) : ℝ) : ℂ)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
  rw [hpull]
  congr 1

/-! ## 14. The five-duplication identity -/

/-- **The level-five duplication identity.**  The fifty weighted `sinKernel`–`cosKernel`
products at scale `y` equal `−800` times the fifty weighted `oddKernel`–`evenKernel`
products at scale `800y`.  The fifty phases collapse through the quadratic Gauss sum
mod five, the lattice folds exactly as at level one, and the fold deposits the sign
`χ₅(2) = −1` — the root number of the curve at five, returned by finite arithmetic. -/
theorem theFiveDuplicationIdentity {y : ℝ} (hy : 0 < y) :
    ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
        (w5 e d : ℝ) *
          (sinKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) y *
           cosKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) y)
      = -800 * ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
          (w5 e d : ℝ) *
            (oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (800 * y) *
             evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (800 * y)) := by
  have hC : ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
        ((w5 e d : ℤ) : ℂ) *
          (((sinKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) y : ℝ) : ℂ) *
           ((cosKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) y : ℝ) : ℂ))
      = -800 * ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
          ((w5 e d : ℤ) : ℂ) *
            (((oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (800 * y) : ℝ) : ℂ) *
             ((evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (800 * y) : ℝ) : ℂ)) := by
    rw [dual_side_eq hy, tsum_dual5_eq_hFinal5 hy, primal_side_eq hy]
  exact_mod_cast hC

/-! ## 15. The functional equation of the theta at five -/

private lemma rpow_two_of_pos {t : ℝ} (ht : 0 < t) :
    t ^ ((3 : ℝ) / 2) * t ^ ((1 : ℝ) / 2) = t ^ 2 := by
  rw [← Real.rpow_add ht, show (3 : ℝ) / 2 + 1 / 2 = ((2 : ℕ) : ℝ) from by norm_num,
    Real.rpow_natCast]

/-- **The theta functional equation of the congruent-number curve at five.**
`θ₅(1/x) = −x²·θ₅(x)` for `x > 0`: weight two, **sign `−1`**, level 800 — the two
mathlib Hurwitz-kernel functional equations composed through the five-duplication
identity.  The odd hand of the reflection, from which `Λ₅(1) = 0` follows. -/
theorem theFiveThetaFunctionalEquation {x : ℝ} (hx : 0 < x) :
    theta5 (1 / x) = -(x ^ 2) * theta5 x := by
  have hs : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos
  have hy : (0 : ℝ) < x / (20 * Real.sqrt 2) := by positivity
  have hss : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hne : (20 : ℝ) * Real.sqrt 2 ≠ 0 := by positivity
  unfold theta5
  rw [show 20 * Real.sqrt 2 * (1 / x) = 1 / (x / (20 * Real.sqrt 2)) from by
    rw [one_div_div]; ring]
  have hterm : ∀ e ∈ Finset.range 5, ∀ d ∈ Finset.range 10,
      (w5 e d : ℝ) *
        (oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle)
            (1 / (x / (20 * Real.sqrt 2))) *
         evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (1 / (x / (20 * Real.sqrt 2))))
      = (x ^ 2 / 800) * ((w5 e d : ℝ) *
          (sinKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (x / (20 * Real.sqrt 2)) *
           cosKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (x / (20 * Real.sqrt 2)))) := by
    intro e _ d _
    rw [oddKernel_functional_equation _ (1 / (x / (20 * Real.sqrt 2))),
      evenKernel_functional_equation _ (1 / (x / (20 * Real.sqrt 2))),
      one_div_one_div,
      show (1 / (x / (20 * Real.sqrt 2))) = (x / (20 * Real.sqrt 2))⁻¹ from one_div _,
      Real.inv_rpow hy.le, Real.inv_rpow hy.le, one_div, one_div, inv_inv, inv_inv]
    have hpow : (x / (20 * Real.sqrt 2)) ^ ((3 : ℝ) / 2) *
        (x / (20 * Real.sqrt 2)) ^ ((1 : ℝ) / 2) = x ^ 2 / 800 := by
      rw [rpow_two_of_pos hy, div_pow]
      congr 1
      rw [mul_pow]
      linear_combination (400 : ℝ) * hss
    calc (w5 e d : ℝ) *
          ((x / (20 * Real.sqrt 2)) ^ ((3 : ℝ) / 2) *
            sinKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (x / (20 * Real.sqrt 2)) *
           ((x / (20 * Real.sqrt 2)) ^ ((1 : ℝ) / 2) *
            cosKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (x / (20 * Real.sqrt 2))))
        = ((x / (20 * Real.sqrt 2)) ^ ((3 : ℝ) / 2) *
            (x / (20 * Real.sqrt 2)) ^ ((1 : ℝ) / 2)) * ((w5 e d : ℝ) *
            (sinKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (x / (20 * Real.sqrt 2)) *
             cosKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (x / (20 * Real.sqrt 2)))) := by
          ring
      _ = _ := by rw [hpow]
  rw [Finset.sum_congr rfl fun e he => Finset.sum_congr rfl fun d hd => hterm e he d hd]
  have hpull : ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
      (x ^ 2 / 800) * ((w5 e d : ℝ) *
        (sinKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (x / (20 * Real.sqrt 2)) *
         cosKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (x / (20 * Real.sqrt 2))))
      = (x ^ 2 / 800) * ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
          (w5 e d : ℝ) *
            (sinKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (x / (20 * Real.sqrt 2)) *
             cosKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (x / (20 * Real.sqrt 2))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ => by rw [Finset.mul_sum]
  rw [hpull, theFiveDuplicationIdentity hy]
  have h800 : 800 * (x / (20 * Real.sqrt 2)) = 20 * Real.sqrt 2 * x := by
    rw [show 800 * (x / (20 * Real.sqrt 2)) = 800 * x / (20 * Real.sqrt 2) from by ring,
      div_eq_iff hne]
    linear_combination (-400 * x) * hss
  rw [h800]
  ring

/-! ## 16. The strong FE-pair with the odd hand, and the central vanishing -/

lemma continuousOn_theta5 : ContinuousOn theta5 (Set.Ioi 0) := by
  unfold theta5
  refine ContinuousOn.mul continuousOn_const ?_
  refine continuousOn_finset_sum _ fun e _ => ?_
  refine continuousOn_finset_sum _ fun d _ => ?_
  refine ContinuousOn.mul continuousOn_const (ContinuousOn.mul ?_ ?_)
  · refine (continuousOn_oddKernel _).comp (Continuous.continuousOn (by fun_prop)) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx ⊢
    positivity
  · refine (continuousOn_evenKernel _).comp (Continuous.continuousOn (by fun_prop)) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx ⊢
    positivity

private lemma isBigO_term_rpow (e d : ℕ) (r : ℝ) :
    (fun x : ℝ => (w5 e d : ℝ) *
        (oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x) *
         evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x)))
      =O[Filter.atTop] fun x : ℝ => x ^ r := by
  have hs : (0 : ℝ) < Real.sqrt 2 := sqrt2_pos
  have ht : Filter.Tendsto (fun x : ℝ => 20 * Real.sqrt 2 * x) Filter.atTop Filter.atTop :=
    Filter.tendsto_id.const_mul_atTop (by positivity)
  obtain ⟨p, hp, hp'⟩ := isBigO_atTop_oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle)
  obtain ⟨q, hq, hq'⟩ := isBigO_atTop_evenKernel_sub (((d : ℝ) / 10 : ℝ) : UnitAddCircle)
  have hodd : (fun x : ℝ =>
      oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x))
      =O[Filter.atTop] fun x => rexp (-(20 * Real.sqrt 2 * p) * x) := by
    refine (hp'.comp_tendsto ht).congr' Filter.EventuallyEq.rfl ?_
    exact Filter.Eventually.of_forall fun x => by
      show rexp (-p * (20 * Real.sqrt 2 * x)) = rexp (-(20 * Real.sqrt 2 * p) * x)
      congr 1
      ring
  have heven : (fun x : ℝ =>
      evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x))
      =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
    have hsub : (fun x : ℝ =>
        evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x)
          - (if (((d : ℝ) / 10 : ℝ) : UnitAddCircle) = 0 then 1 else 0))
        =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
      refine (hq'.comp_tendsto ht).trans ?_
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards [Filter.eventually_ge_atTop (0 : ℝ)] with x hx
      show |((fun x => rexp (-q * x)) ∘ fun x => 20 * Real.sqrt 2 * x) x| ≤ 1 * ‖(1 : ℝ)‖
      simp only [Function.comp_apply]
      rw [abs_of_nonneg (Real.exp_nonneg _), norm_one, mul_one]
      refine Real.exp_le_one_iff.mpr ?_
      have : 0 ≤ q * (20 * Real.sqrt 2 * x) := by positivity
      linarith
    have hconst : (fun _ : ℝ => (if (((d : ℝ) / 10 : ℝ) : UnitAddCircle) = 0 then (1:ℝ) else 0))
        =O[Filter.atTop] fun _ : ℝ => (1 : ℝ) := by
      refine Asymptotics.IsBigO.of_bound 1 ?_
      filter_upwards with x
      split_ifs <;> simp
    have := hsub.add hconst
    refine this.congr_left fun x => ?_
    ring
  have hprod := (hodd.const_mul_left (w5 e d : ℝ)).mul heven
  have hexp : (fun x : ℝ => (w5 e d : ℝ) *
      oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x) *
      evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x))
      =O[Filter.atTop] fun x => rexp (-(20 * Real.sqrt 2 * p) * x) := by
    refine hprod.congr_right fun x => mul_one _
  have hfin := hexp.trans
    (isLittleO_exp_neg_mul_rpow_atTop (by positivity : (0:ℝ) < 20 * Real.sqrt 2 * p) r).isBigO
  refine hfin.congr_left fun x => ?_
  ring

lemma isBigO_atTop_theta5 (r : ℝ) :
    theta5 =O[Filter.atTop] fun x : ℝ => x ^ r := by
  unfold theta5
  have hsum : (fun x : ℝ => ∑ e ∈ Finset.range 5, ∑ d ∈ Finset.range 10,
      (w5 e d : ℝ) *
        (oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x) *
         evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x)))
      =O[Filter.atTop] fun x : ℝ => x ^ r := by
    have h1 : ∀ e ∈ Finset.range 5, (fun x : ℝ => ∑ d ∈ Finset.range 10,
        (w5 e d : ℝ) *
          (oddKernel (((4 * (e : ℝ) + 1) / 20 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x) *
           evenKernel (((d : ℝ) / 10 : ℝ) : UnitAddCircle) (20 * Real.sqrt 2 * x)))
        =O[Filter.atTop] fun x : ℝ => x ^ r := fun e _ =>
      Asymptotics.IsBigO.sum fun d _ => isBigO_term_rpow e d r
    exact Asymptotics.IsBigO.sum h1
  exact hsum.const_mul_left 20

/-- The strong FE-pair of the congruent-number curve at five: `f = g = θ₅`, weight `2`,
**sign `−1`**, no constant terms. -/
def fiveFEPair : StrongFEPair ℂ where
  f := Complex.ofReal ∘ theta5
  g := Complex.ofReal ∘ theta5
  k := 2
  hk := two_pos
  ε := -1
  hε := by norm_num
  f₀ := 0
  g₀ := 0
  hf₀ := rfl
  hg₀ := rfl
  hf_int := (Complex.continuous_ofReal.comp_continuousOn
    continuousOn_theta5).locallyIntegrableOn measurableSet_Ioi
  hg_int := (Complex.continuous_ofReal.comp_continuousOn
    continuousOn_theta5).locallyIntegrableOn measurableSet_Ioi
  h_feq x hx := by
    have hfe := theFiveThetaFunctionalEquation (Set.mem_Ioi.mp hx)
    simp only [Function.comp_apply, smul_eq_mul, hfe]
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    push_cast
    ring
  hf_top r := by
    simpa using isBigO_ofReal_left.mpr (isBigO_atTop_theta5 r)
  hg_top r := by
    simpa using isBigO_ofReal_left.mpr (isBigO_atTop_theta5 r)

/-- **The completed L-function of the congruent-number curve at five**: the Mellin
transform of `θ₅`, with no convergence region. -/
def lambda5 : ℂ → ℂ := fiveFEPair.Λ

/-- **`Λ₅` is entire** — the strong FE-pair machinery returns differentiability on all
of `ℂ` at once, no continuation step. -/
theorem theCompletedLFunctionAtFiveIsEntire : Differentiable ℂ lambda5 :=
  fiveFEPair.differentiable_Λ

/-- The Mellin representation of `Λ₅` at every `s`. -/
theorem theCompletedLFunctionAtFiveHasMellin (s : ℂ) :
    HasMellin (Complex.ofReal ∘ theta5) s (lambda5 s) :=
  fiveFEPair.hasMellin s

/-- **The functional equation at five**: `Λ₅(2−s) = −Λ₅(s)`.  Weight two, sign `−1` —
the odd hand of the reflection, kernel-checked. -/
theorem theCompletedLFunctionalEquationAtFive (s : ℂ) :
    lambda5 (2 - s) = -lambda5 s := by
  have h := fiveFEPair.functional_equation s
  rw [show fiveFEPair.k = (2 : ℝ) from rfl, show fiveFEPair.ε = (-1 : ℂ) from rfl] at h
  have hsymm : fiveFEPair.symm.Λ = fiveFEPair.Λ := by
    rfl
  rw [hsymm] at h
  simpa [lambda5, neg_smul, one_smul] using h

/-- **The odd hand forces the central vanishing: `Λ₅(1) = 0`.**  The value at the fixed
point of an odd reflection dies by parity alone — analytic rank at least one at five,
kernel-checked with no L-value computation. -/
theorem theOddHandForcesTheCentralVanishingAtFive : lambda5 1 = 0 := by
  have h := theCompletedLFunctionalEquationAtFive 1
  rw [show (2 : ℂ) - 1 = 1 from by norm_num] at h
  linear_combination h / 2

end Soma.Holonics.Millennium.FiveTheta
