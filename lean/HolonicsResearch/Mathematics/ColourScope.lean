import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-!
# Neutral is a ratio of one: the scope decides what a colour reads

The record `research/records/2026-10-26_NEUTRAL_IS_A_RATIO_OF_ONE_AGAINST_WHERE_THE_RECEIVER_STANDS_AND_THE_SCOPE_DECIDES_WHAT_A_COLOUR_READS.md`
reads Brandon's lens (October 26) on the Galois colours of `Mathematics/ColourTrace`: a colour is
never intrinsic, repeating a cycle already held reads neutral, the sign of a new cycle depends on the
cycles already held, and a coarser scope reads the same colour differently.

[proved-standard; formal-checked] What is proved.

1. **No colour is intrinsic** (`no_intrinsic_colour`): for every unit `j` mod `n`, an automorphism
   of `ℚ(ζ_n)` carries `ζ_n` to `ζ_n^j`. Nothing algebraic tells two colours of one order apart; only
   their relations survive.
2. **A repeated prime's colours come in fibres that cancel** (`fibre_primitive`, `fibre_cancels`):
   when `p² ∣ n`, multiplying a primitive colour by the `p`-th roots of unity keeps it primitive,
   and each such fibre of `p` colours sums to `0`. This is why `μ(n) = 0` there: the new colours sit
   over a cycle already present and cancel against each other.
3. **A new prime flips the sign** (`new_prime_flips_sign`): `μ(p n) = −μ(n)` when `p ∤ n`. The
   reading of a new cycle depends on how many independent cycles were already held.
4. **The scope decides the reading** (`colour12_primitive`, `scope_quarter_turn`, `scope_real`,
   `scope_cube_root`, `scope_rational`): the twelfth-turn colour `ζ = e^(iπ/6)` compressed to the
   quarter-turn scope `ℚ(i)` reads `ζ + ζ⁵ = i`, to the real scope `ℚ(√3)` reads `ζ + ζ¹¹ = √3`,
   to the cube-root scope `ℚ(ζ₃)` reads `ζ + ζ⁷ = 0`, and to `ℚ` reads `0 = μ(12)`. One colour, a
   turn, a size or neutral, by the scope that coarse-grains it.

Consumers: the atlas rows `colour.scope-reading` and `colour.neutral-fibre`.
-/

namespace Holonics.Mathematics.ColourScope

open ArithmeticFunction Finset Polynomial Complex
open scoped ArithmeticFunction.Moebius

-- `CyclotomicField n ℚ` carries two `ℚ`-algebra instances (its own and `DivisionRing.toRatAlgebra`);
-- Mathlib unifies them under this option (`NumberField/Cyclotomic/Basic`).
set_option backward.isDefEq.respectTransparency false in
/-- [proved-standard; formal-checked] **No colour is intrinsic.** For every unit `j` mod `n`, an
automorphism of the cyclotomic field carries the chosen primitive colour to its `j`-th power. -/
theorem no_intrinsic_colour (n : ℕ) [NeZero n] (j : (ZMod n)ˣ) :
    ∃ σ : CyclotomicField n ℚ ≃ₐ[ℚ] CyclotomicField n ℚ,
      σ (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ)) =
        IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ (j : ZMod n).val := by
  have hirr : Irreducible (cyclotomic n ℚ) :=
    cyclotomic.irreducible_rat (Nat.pos_of_ne_zero (NeZero.ne n))
  have hμ : IsPrimitiveRoot
      (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ (j : ZMod n).val) n :=
    (IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)).pow_of_coprime _
      (ZMod.val_coe_unit_coprime j)
  exact ⟨IsCyclotomicExtension.fromZetaAut hμ hirr,
    IsCyclotomicExtension.fromZetaAut_spec hμ hirr⟩

/-- [proved-standard; formal-checked] **A repeated prime's fibre keeps the order.** When `p² ∣ n`,
`ζ · (ζ^(n/p))^k` is again a primitive `n`-th root for every `k`. -/
theorem fibre_primitive {R : Type*} [CommRing R] {ζ : R} {n p : ℕ} (hζ : IsPrimitiveRoot ζ n)
    (hp : p.Prime) (hpp : p ^ 2 ∣ n) (k : ℕ) :
    IsPrimitiveRoot (ζ * (ζ ^ (n / p)) ^ k) n := by
  rw [← pow_mul, ← pow_succ']
  apply hζ.pow_of_coprime
  apply Nat.coprime_of_dvd
  intro q hq hqa hqn
  have hqd : q ∣ n / p := by
    by_cases hqp : q = p
    · subst hqp
      exact Nat.dvd_div_of_mul_dvd (by rw [← pow_two]; exact hpp)
    · have hpn : p ∣ n := (dvd_pow_self p two_ne_zero).trans hpp
      have hq' : q ∣ p * (n / p) := by rwa [Nat.mul_div_cancel' hpn]
      rcases (Nat.Prime.dvd_mul hq).mp hq' with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp h) hqp
      · exact h
  have h1 : q ∣ 1 := (Nat.dvd_add_right (dvd_mul_of_dvd_left hqd k)).mp hqa
  exact hq.one_lt.ne' (Nat.dvd_one.mp h1)

/-- [proved-standard; formal-checked] **A fibre cancels.** The `p` colours `ζ · (ζ^(n/p))^k`,
`k < p`, sum to `0`. -/
theorem fibre_cancels {R : Type*} [CommRing R] [IsDomain R] {ζ : R} {n p : ℕ} (hn : 0 < n)
    (hζ : IsPrimitiveRoot ζ n) (hp : p.Prime) (hpn : p ∣ n) :
    ∑ k ∈ range p, ζ * (ζ ^ (n / p)) ^ k = 0 := by
  rw [← mul_sum]
  have hω : IsPrimitiveRoot (ζ ^ (n / p)) p :=
    IsPrimitiveRoot.pow hn hζ (Nat.div_mul_cancel hpn).symm
  rw [hω.geom_sum_eq_zero hp.one_lt, mul_zero]

/-- [proved-standard; formal-checked] **A new prime flips the sign:** `μ(p n) = −μ(n)` when
`p ∤ n`. -/
theorem new_prime_flips_sign {p n : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    μ (p * n) = -μ n := by
  rw [isMultiplicative_moebius.map_mul_of_coprime ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpn),
    moebius_apply_prime hp]
  ring

/-- The twelfth-turn colour `e^(iπ/6)`. -/
noncomputable def colour12 : ℂ := exp (↑(Real.pi / 6) * I)

/-- [proved-standard; formal-checked] It is a primitive twelfth root of unity. -/
theorem colour12_primitive : IsPrimitiveRoot colour12 12 := by
  have h := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  rw [colour12]
  convert h using 2
  push_cast
  ring

/-- [proved-standard; formal-checked] Its powers: `ζᵏ = e^(i k π/6)`. -/
theorem colour12_pow (k : ℕ) : colour12 ^ k = exp (↑((k : ℝ) * (Real.pi / 6)) * I) := by
  rw [colour12, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- [proved-standard; formal-checked] The half-turn: `ζ⁶ = −1`. -/
theorem colour12_pow_six : colour12 ^ 6 = -1 := by
  rw [colour12_pow, show ((6 : ℕ) : ℝ) * (Real.pi / 6) = Real.pi by push_cast; ring]
  exact Complex.exp_pi_mul_I

/-- [proved-standard; formal-checked] **To the cube-root scope `ℚ(ζ₃)` the colour reads neutral:**
`ζ + ζ⁷ = 0`. -/
theorem scope_cube_root : colour12 + colour12 ^ 7 = 0 := by
  rw [show colour12 ^ 7 = colour12 * colour12 ^ 6 by ring, colour12_pow_six]
  ring

/-- [proved-standard; formal-checked] **To the quarter-turn scope `ℚ(i)` the colour reads a turn:**
`ζ + ζ⁵ = i`. -/
theorem scope_quarter_turn : colour12 + colour12 ^ 5 = I := by
  have h5 : ((5 : ℕ) : ℝ) * (Real.pi / 6) = Real.pi - Real.pi / 6 := by push_cast; ring
  apply Complex.ext
  · rw [add_re, colour12_pow, colour12, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_re, I_re, h5, Real.cos_pi_sub]
    ring
  · rw [add_im, colour12_pow, colour12, Complex.exp_ofReal_mul_I_im,
      Complex.exp_ofReal_mul_I_im, I_im, h5, Real.sin_pi_sub, Real.sin_pi_div_six]
    ring

/-- [proved-standard; formal-checked] **To the real scope `ℚ(√3)` the colour reads a size:**
`ζ + ζ¹¹ = √3`. -/
theorem scope_real : colour12 + colour12 ^ 11 = (Real.sqrt 3 : ℂ) := by
  have h11 : ((11 : ℕ) : ℝ) * (Real.pi / 6) = -(Real.pi / 6) + 2 * Real.pi := by push_cast; ring
  apply Complex.ext
  · rw [add_re, colour12_pow, colour12, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_re, ofReal_re, h11, Real.cos_add_two_pi, Real.cos_neg,
      Real.cos_pi_div_six]
    ring
  · rw [add_im, colour12_pow, colour12, Complex.exp_ofReal_mul_I_im,
      Complex.exp_ofReal_mul_I_im, ofReal_im, h11, Real.sin_add_two_pi, Real.sin_neg]
    ring

/-- [proved-standard; formal-checked] **To `ℚ` the colour reads `μ(12) = 0`:** the four colours of
order twelve cancel. -/
theorem scope_rational : colour12 + colour12 ^ 5 + colour12 ^ 7 + colour12 ^ 11 = 0 := by
  rw [show colour12 ^ 11 = colour12 ^ 5 * colour12 ^ 6 by ring,
    show colour12 ^ 7 = colour12 * colour12 ^ 6 by ring, colour12_pow_six]
  ring

end Holonics.Mathematics.ColourScope
