import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.ZMod.Units
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
5. **A scope that holds a repeated prime's fibre reads neutral** (`scopeReading`, `fibre_step_sq`,
   `fibre_generator_pow`, `scopeReading_eq_zero_of_fibre`, `fibre_generator_mem_ker`,
   `scopeReading_eq_zero_of_ker_le`). Let `n = p·m` with `p` prime and `p ∣ m`, so `p² ∣ n`. The
   unit `g = 1 + m` steps along the fibre (`gⁱ = 1 + i·m`, since `m² ≡ 0`) and lies in the kernel of
   `(ℤ/n)ˣ → (ℤ/m)ˣ`. A scope `H ≤ (ℤ/n)ˣ` that contains `g` (in particular, one that contains that
   kernel) reads `Tr_H(ζ_n) = ∑_(h ∈ H) ζ_n^h = 0`: right multiplication by `g` moves each `h` along
   its fibre inside `H`, and each fibre's `p` colours cancel. `scope_cube_root` is the case
   `n = 12`, `p = 2`, `m = 6`, `H = {1, 7}`. The converse, that a neutral reading forces such a
   fibre, is checked for `n ≤ 200` and owed to #410 (p).

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

/-! ### A scope that holds a fibre reads neutral -/

/-- [definition] The reading of the colour `ζ` in the scope `H ≤ (ℤ/n)ˣ`:
`Tr_H(ζ) = ∑_(h ∈ H) ζ^h`. -/
noncomputable def scopeReading {n : ℕ} [NeZero n] (H : Subgroup (ZMod n)ˣ)
    [DecidablePred (· ∈ H)] (ζ : ℂ) : ℂ :=
  ∑ h : H, ζ ^ ((h : (ZMod n)ˣ) : ZMod n).val

/-- [proved-standard; formal-checked] **The fibre's step squares to zero:** when `n = p·m` and
`p ∣ m`, `m² ≡ 0 (mod n)`. -/
theorem fibre_step_sq {n p m : ℕ} (hn : n = p * m) (hpm : p ∣ m) :
    (m : ZMod n) * (m : ZMod n) = 0 := by
  rw [← Nat.cast_mul, CharP.cast_eq_zero_iff (ZMod n) n]
  obtain ⟨k, rfl⟩ := hpm
  exact ⟨k, by rw [hn]; ring⟩

/-- [proved-standard; formal-checked] **The fibre generator steps along the fibre:** if
`g = 1 + m` then `gⁱ = 1 + i·m`. -/
theorem fibre_generator_pow {n p m : ℕ} (hn : n = p * m) (hpm : p ∣ m) {g : (ZMod n)ˣ}
    (hgv : (g : ZMod n) = 1 + (m : ZMod n)) (i : ℕ) :
    ((g ^ i : (ZMod n)ˣ) : ZMod n) = 1 + (i : ZMod n) * (m : ZMod n) := by
  have hsq := fibre_step_sq hn hpm
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, Units.val_mul, ih, hgv]
    push_cast
    linear_combination (i : ZMod n) * hsq

/-- [proved-standard; formal-checked] **A scope that holds the fibre generator reads neutral:**
if `n = p·m` with `p` prime and `p ∣ m`, and `H` contains the unit `g = 1 + m`, then
`Tr_H(ζ_n) = 0` for every primitive `n`-th root `ζ_n`. -/
theorem scopeReading_eq_zero_of_fibre {n p m : ℕ} [NeZero n] (hp : p.Prime) (hn : n = p * m)
    (hpm : p ∣ m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (H : Subgroup (ZMod n)ˣ)
    [DecidablePred (· ∈ H)] {g : (ZMod n)ˣ} (hgv : (g : ZMod n) = 1 + (m : ZMod n))
    (hgH : g ∈ H) : scopeReading H ζ = 0 := by
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  have hζn : ζ ^ n = 1 := hζ.pow_eq_one
  -- `ζ^a` reads `a` only modulo `n`.
  have hmod : ∀ a : ℕ, ζ ^ ((a : ZMod n).val) = ζ ^ a := by
    intro a
    rw [ZMod.val_natCast]
    conv_rhs => rw [← Nat.mod_add_div a n, pow_add, pow_mul, hζn, one_pow, mul_one]
  -- Moving along the fibre multiplies the reading by a power of a primitive `p`-th root.
  have key : ∀ (u : (ZMod n)ˣ) (i : ℕ), ζ ^ ((u * g ^ i : (ZMod n)ˣ) : ZMod n).val =
      ζ ^ (u : ZMod n).val * ((ζ ^ m) ^ (u : ZMod n).val) ^ i := by
    intro u i
    have hu : ((u * g ^ i : (ZMod n)ˣ) : ZMod n) =
        (((u : ZMod n).val * (1 + i * m) : ℕ) : ZMod n) := by
      rw [Units.val_mul, fibre_generator_pow hn hpm hgv]
      simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, ZMod.natCast_zmod_val]
    rw [hu, hmod, ← pow_mul, ← pow_mul, ← pow_add]
    congr 1
    ring
  have hω : IsPrimitiveRoot (ζ ^ m) p := hζ.pow hn0 (by rw [hn, mul_comm])
  have hpn : p ∣ n := ⟨m, hn⟩
  -- Each fibre cancels.
  have hfibre : ∀ u : (ZMod n)ˣ, ∑ i ∈ range p, ((ζ ^ m) ^ (u : ZMod n).val) ^ i = 0 := by
    intro u
    have hcop : Nat.Coprime (u : ZMod n).val p :=
      (ZMod.val_coe_unit_coprime u).coprime_dvd_right hpn
    exact (hω.pow_of_coprime _ hcop).geom_sum_eq_zero hp.one_lt
  -- Right multiplication by `gⁱ ∈ H` permutes the scope.
  have hshift : ∀ i : ℕ, ∑ h : H, ζ ^ ((h : (ZMod n)ˣ) : ZMod n).val =
      ∑ h : H, ζ ^ (((h : (ZMod n)ˣ) * g ^ i : (ZMod n)ˣ) : ZMod n).val := by
    intro i
    symm
    exact Fintype.sum_equiv (Equiv.mulRight (⟨g ^ i, H.pow_mem hgH i⟩ : H)) _ _ fun h => rfl
  have hsum : (p : ℂ) * scopeReading H ζ = 0 := by
    unfold scopeReading
    calc (p : ℂ) * ∑ h : H, ζ ^ ((h : (ZMod n)ˣ) : ZMod n).val
        = ∑ i ∈ range p, ∑ h : H, ζ ^ ((h : (ZMod n)ˣ) : ZMod n).val := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ = ∑ i ∈ range p, ∑ h : H, ζ ^ (((h : (ZMod n)ˣ) * g ^ i : (ZMod n)ˣ) : ZMod n).val :=
          Finset.sum_congr rfl fun i _ => hshift i
      _ = ∑ h : H, ζ ^ ((h : (ZMod n)ˣ) : ZMod n).val *
            ∑ i ∈ range p, ((ζ ^ m) ^ ((h : (ZMod n)ˣ) : ZMod n).val) ^ i := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => key h i
      _ = 0 := by simp [hfibre]
  rcases mul_eq_zero.mp hsum with h | h
  · exact absurd h (by exact_mod_cast hp.ne_zero)
  · exact h

/-- [proved-standard; formal-checked] **The fibre generator lies in the kernel of
`(ℤ/n)ˣ → (ℤ/m)ˣ`.** -/
theorem fibre_generator_mem_ker {n m : ℕ} (hmn : m ∣ n) {g : (ZMod n)ˣ}
    (hgv : (g : ZMod n) = 1 + (m : ZMod n)) : g ∈ (ZMod.unitsMap hmn).ker := by
  rw [MonoidHom.mem_ker, Units.ext_iff, Units.val_one]
  show ZMod.castHom hmn (ZMod m) (g : ZMod n) = 1
  rw [hgv, map_add, map_one, map_natCast, ZMod.natCast_self, add_zero]

/-- [proved-standard; formal-checked] **A scope that holds the kernel of `(ℤ/n)ˣ → (ℤ/m)ˣ` reads
neutral**, when `n = p·m` with `p` prime and `p ∣ m`. This is the `⇐` half of the neutral
criterion; its converse is owed to #410 (p). -/
theorem scopeReading_eq_zero_of_ker_le {n p m : ℕ} [NeZero n] (hp : p.Prime) (hn : n = p * m)
    (hpm : p ∣ m) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ n) (H : Subgroup (ZMod n)ˣ)
    [DecidablePred (· ∈ H)] (hK : (ZMod.unitsMap (Dvd.intro_left p hn.symm)).ker ≤ H) :
    scopeReading H ζ = 0 := by
  have hsq := fibre_step_sq hn hpm
  let g : (ZMod n)ˣ :=
    ⟨1 + (m : ZMod n), 1 - (m : ZMod n), by linear_combination -hsq, by linear_combination -hsq⟩
  exact scopeReading_eq_zero_of_fibre hp hn hpm hζ H (g := g) rfl
    (hK (fibre_generator_mem_ker _ rfl))

end Holonics.Mathematics.ColourScope
