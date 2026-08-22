import ElementaryHolonics.Millennium.HeckeTheta
import ElementaryHolonics.Millennium.BirchSwinnertonDyer
import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# GaussCoefficient: the point count is the Jacobsthal sum

**The arithmetic identification, first stage.**  For an odd prime `p` the trace of
Frobenius of `y² = x³ − x` is the negative of a quadratic character sum, and that sum
is a Jacobsthal sum — the object whose square ledger `E² + F² = 4p` carries the
two-squares decomposition of `p`.  This file builds the Jacobsthal engine:

* `trace_eq_neg_charSum` — `a_p = −Σ_x χ(x³−x)`, by the square-count law
  `#{y : y² = c} = χ(c) + 1`;
* `charSum_eq_jac` — the curve sum is `jac p (−1)`;
* `jac_mul_sq` — the scaling law `jac (t²D) = χ(t)·jac D`;
* `sum_char_shift` — the complete quadratic sum `Σ_D χ((D+a)(D+b)) = −1` for `a ≠ b`;
* `sum_jac_sq` — the double count `Σ_D jac(D)² = 2p(p−1)`;
* `jac_sq_add_jac_sq` — the two-squares ledger `jac(1)² + jac(r)² = 4p`.

Everything is exact and `sorryAx`-free; the normalization congruence and the shell
identification are the following stages.
-/

namespace Soma.Holonics.Millennium.GaussCoefficient

open Finset
open Soma.Holonics.Millennium.BirchSwinnertonDyer

variable {p : ℕ} [Fact p.Prime]

/-- The Jacobsthal sum `φ(D) = Σ_x χ(x)·χ(x² + D)`, exact over `ℤ`. -/
noncomputable def jac (p : ℕ) [Fact p.Prime] (D : ZMod p) : ℤ :=
  ∑ x : ZMod p, quadraticChar (ZMod p) x * quadraticChar (ZMod p) (x ^ 2 + D)

/-- The square-count expansion: the trace of Frobenius is the negative character sum. -/
theorem trace_eq_neg_charSum (hp2 : p ≠ 2) :
    traceOfFrobenius 1 p = -∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - x) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  unfold traceOfFrobenius affineCount
  have hcard : ∀ x : ZMod p,
      ((univ.filter fun y : ZMod p => y ^ 2 = x ^ 3 - (1 : ZMod p) ^ 2 * x).card : ℤ)
      = quadraticChar (ZMod p) (x ^ 3 - x) + 1 := by
    intro x
    have h := quadraticChar_card_sqrts hchar (x ^ 3 - x)
    rw [← h]
    congr 1
    rw [Set.toFinset_setOf]
    congr 1
    ext y
    norm_num
  push_cast
  rw [Finset.sum_congr rfl fun x _ => hcard x, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, ZMod.card]
  push_cast
  ring

/-- The curve sum is the Jacobsthal sum at `−1`. -/
theorem charSum_eq_jac :
    ∑ x : ZMod p, quadraticChar (ZMod p) (x ^ 3 - x) = jac p (-1) := by
  unfold jac
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [show x ^ 3 - x = x * (x ^ 2 + -1) from by ring, map_mul]

/-- The scaling law: `jac (t²·D) = χ(t)·jac D`. -/
theorem jac_mul_sq {t : ZMod p} (ht : t ≠ 0) (D : ZMod p) :
    jac p (t ^ 2 * D) = quadraticChar (ZMod p) t * jac p D := by
  unfold jac
  rw [Finset.mul_sum]
  rw [← Equiv.sum_comp (Equiv.mulLeft₀ t ht)
    (fun x => quadraticChar (ZMod p) x * quadraticChar (ZMod p) (x ^ 2 + t ^ 2 * D))]
  refine Finset.sum_congr rfl fun x _ => ?_
  show quadraticChar (ZMod p) (t * x) * quadraticChar (ZMod p) ((t * x) ^ 2 + t ^ 2 * D) = _
  rw [show (t * x) ^ 2 + t ^ 2 * D = t ^ 2 * (x ^ 2 + D) from by ring, map_mul, map_mul,
    quadraticChar_sq_one' ht]
  ring

/-- The complete quadratic sum: `Σ_D χ((D+a)(D+b)) = −1` when `a ≠ b`. -/
theorem sum_char_shift (hp2 : p ≠ 2) {a b : ZMod p} (hab : a ≠ b) :
    ∑ D : ZMod p, quadraticChar (ZMod p) ((D + a) * (D + b)) = -1 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  set c : ZMod p := b - a with hc
  have hc0 : c ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  have h1 : ∑ D : ZMod p, quadraticChar (ZMod p) ((D + a) * (D + b))
      = ∑ E : ZMod p, quadraticChar (ZMod p) (E * (E + c)) := by
    rw [← Equiv.sum_comp (Equiv.subRight a)
      (fun D => quadraticChar (ZMod p) ((D + a) * (D + b)))]
    refine Finset.sum_congr rfl fun E _ => ?_
    show quadraticChar (ZMod p) ((E - a + a) * (E - a + b)) = _
    congr 2 <;> [skip; rw [hc]] <;> ring
  rw [h1, ← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod p)),
    show quadraticChar (ZMod p) ((0 : ZMod p) * (0 + c)) = 0 from by
      rw [zero_mul]; exact (quadraticChar (ZMod p)).map_zero,
    zero_add]
  have h2 : ∑ E ∈ (univ : Finset (ZMod p)).erase 0, quadraticChar (ZMod p) (E * (E + c))
      = ∑ u ∈ (univ : Finset (ZMod p)).erase 1, quadraticChar (ZMod p) u := by
    refine Finset.sum_bij' (fun E _ => 1 + c * E⁻¹) (fun u _ => c / (u - 1))
      ?_ ?_ ?_ ?_ ?_
    · intro E hE
      rw [Finset.mem_erase] at hE ⊢
      refine ⟨?_, mem_univ _⟩
      intro hcon
      have hE0 := hE.1
      have : c * E⁻¹ = 0 := by linear_combination hcon
      rcases mul_eq_zero.mp this with h | h
      · exact hc0 h
      · exact hE0 (inv_eq_zero.mp h)
    · intro u hu
      rw [Finset.mem_erase] at hu ⊢
      refine ⟨?_, mem_univ _⟩
      exact div_ne_zero hc0 (sub_ne_zero.mpr hu.1)
    · intro E hE
      rw [Finset.mem_erase] at hE
      have hE0 := hE.1
      show c / (1 + c * E⁻¹ - 1) = E
      rw [show (1 : ZMod p) + c * E⁻¹ - 1 = c * E⁻¹ from by ring,
        div_eq_iff (mul_ne_zero hc0 (inv_ne_zero hE0))]
      field_simp
    · intro u hu
      rw [Finset.mem_erase] at hu
      have h1 : u - 1 ≠ 0 := sub_ne_zero.mpr hu.1
      show 1 + c * (c / (u - 1))⁻¹ = u
      rw [inv_div, mul_div_assoc']
      rw [show c * (u - 1) = (u - 1) * c from mul_comm _ _, mul_div_assoc, div_self hc0,
        mul_one]
      ring
    · intro E hE
      rw [Finset.mem_erase] at hE
      have hE0 := hE.1
      have hfac : E * (E + c) = E ^ 2 * (1 + c * E⁻¹) := by
        field_simp
      rw [hfac, map_mul, quadraticChar_sq_one' hE0, one_mul]
  rw [h2, Finset.sum_erase_eq_sub (mem_univ (1 : ZMod p)), quadraticChar_sum_zero hchar,
    map_one]
  norm_num

/-- Squares sum to `p − 1`: `Σ_E χ(E²) = p − 1`. -/
private lemma sum_char_sq (hp2 : p ≠ 2) :
    ∑ E : ZMod p, quadraticChar (ZMod p) (E ^ 2) = (p : ℤ) - 1 := by
  rw [← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod p)),
    show quadraticChar (ZMod p) ((0 : ZMod p) ^ 2) = 0 from by
      rw [show ((0 : ZMod p)) ^ 2 = 0 from by ring]
      exact (quadraticChar (ZMod p)).map_zero,
    zero_add]
  rw [Finset.sum_congr rfl fun E hE => quadraticChar_sq_one' (Finset.mem_erase.mp hE).1]
  rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, ZMod.card,
    nsmul_eq_mul, mul_one, Nat.cast_sub (Fact.out : p.Prime).one_lt.le]
  norm_num

/-- The double count: `Σ_D jac(D)² = 2p(p−1)`. -/
theorem sum_jac_sq (hp2 : p ≠ 2) (hp1 : p % 4 = 1) :
    ∑ D : ZMod p, jac p D ^ 2 = 2 * p * ((p : ℤ) - 1) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hneg1 : quadraticChar (ZMod p) (-1) = 1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card]
    exact ZMod.χ₄_nat_one_mod_four hp1
  -- expand the square and push the D-sum inside
  have step1 : ∀ D : ZMod p, jac p D ^ 2
      = ∑ x : ZMod p, ∑ y : ZMod p, quadraticChar (ZMod p) (x * y) *
          quadraticChar (ZMod p) ((x ^ 2 + D) * (y ^ 2 + D)) := by
    intro D
    rw [jac, sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [map_mul, map_mul]
    ring
  rw [Finset.sum_congr rfl fun D _ => step1 D, Finset.sum_comm]
  have hswap : ∀ x : ZMod p, ∑ D : ZMod p, ∑ y : ZMod p, quadraticChar (ZMod p) (x * y) *
      quadraticChar (ZMod p) ((x ^ 2 + D) * (y ^ 2 + D))
      = ∑ y : ZMod p, ∑ D : ZMod p, quadraticChar (ZMod p) (x * y) *
          quadraticChar (ZMod p) ((x ^ 2 + D) * (y ^ 2 + D)) := fun x => Finset.sum_comm
  rw [Finset.sum_congr rfl fun x _ => hswap x]
  -- the inner D-sum is the complete quadratic sum
  have step2 : ∀ x y : ZMod p, ∑ D : ZMod p, quadraticChar (ZMod p) (x * y) *
      quadraticChar (ZMod p) ((x ^ 2 + D) * (y ^ 2 + D))
      = quadraticChar (ZMod p) (x * y) * (if x ^ 2 = y ^ 2 then (p : ℤ) - 1 else -1) := by
    intro x y
    rw [← Finset.mul_sum]
    congr 1
    by_cases hxy : x ^ 2 = y ^ 2
    · rw [if_pos hxy]
      rw [Finset.sum_congr rfl fun D _ => show quadraticChar (ZMod p) ((x ^ 2 + D) * (y ^ 2 + D))
          = quadraticChar (ZMod p) ((D + x ^ 2) ^ 2) from by rw [← hxy]; ring_nf]
      rw [← Equiv.sum_comp (Equiv.subRight (x ^ 2))
        (fun D => quadraticChar (ZMod p) ((D + x ^ 2) ^ 2))]
      refine Eq.trans (Finset.sum_congr rfl fun E _ => ?_) (sum_char_sq hp2)
      show quadraticChar (ZMod p) ((E - x ^ 2 + x ^ 2) ^ 2) = quadraticChar (ZMod p) (E ^ 2)
      congr 1
      ring
    · rw [if_neg hxy]
      rw [Finset.sum_congr rfl fun D _ => show quadraticChar (ZMod p) ((x ^ 2 + D) * (y ^ 2 + D))
          = quadraticChar (ZMod p) ((D + x ^ 2) * (D + y ^ 2)) from by ring_nf]
      exact sum_char_shift hp2 hxy
  rw [Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => step2 x y]
  -- evaluate the weighted pair sum
  have hinner : ∀ x : ZMod p, ∑ y : ZMod p, quadraticChar (ZMod p) (x * y) *
      (if x ^ 2 = y ^ 2 then (p : ℤ) - 1 else -1)
      = (p : ℤ) * (∑ y : ZMod p, if x ^ 2 = y ^ 2 then quadraticChar (ZMod p) (x * y) else 0)
        - ∑ y : ZMod p, quadraticChar (ZMod p) (x * y) := by
    intro x
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    by_cases hxy : x ^ 2 = y ^ 2
    · rw [if_pos hxy, if_pos hxy]
      ring
    · rw [if_neg hxy, if_neg hxy]
      ring
  rw [Finset.sum_congr rfl fun x _ => hinner x, Finset.sum_sub_distrib, ← Finset.mul_sum]
  -- the unrestricted double sum vanishes
  have hzero : ∑ x : ZMod p, ∑ y : ZMod p, quadraticChar (ZMod p) (x * y) = 0 := by
    rw [Finset.sum_congr rfl fun x _ => show ∑ y : ZMod p, quadraticChar (ZMod p) (x * y)
        = quadraticChar (ZMod p) x * ∑ y : ZMod p, quadraticChar (ZMod p) y from by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => (map_mul _ _ _)]
    rw [quadraticChar_sum_zero hchar]
    simp
  rw [hzero, sub_zero]
  -- the restricted pair sum is 2(p−1)
  have hpair : ∀ x : ZMod p, (∑ y : ZMod p, if x ^ 2 = y ^ 2 then
      quadraticChar (ZMod p) (x * y) else 0)
      = if x = 0 then 0 else 2 := by
    intro x
    by_cases hx : x = 0
    · subst hx
      rw [if_pos rfl]
      rw [Finset.sum_congr rfl fun y _ => show (if (0 : ZMod p) ^ 2 = y ^ 2 then
          quadraticChar (ZMod p) (0 * y) else 0) = 0 from by
        split_ifs with h
        · rw [zero_mul]
          exact (quadraticChar (ZMod p)).map_zero
        · rfl]
      simp
    · rw [if_neg hx]
      have hfilter : (univ.filter fun y : ZMod p => x ^ 2 = y ^ 2)
          = ({x, -x} : Finset (ZMod p)) := by
        ext y
        rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro ⟨-, h⟩
          rcases sq_eq_sq_iff_eq_or_eq_neg.mp h.symm with h1 | h1
          · exact Or.inl h1
          · exact Or.inr h1
        · rintro (rfl | rfl)
          · exact ⟨mem_univ _, rfl⟩
          · exact ⟨mem_univ _, by ring⟩
      rw [← Finset.sum_filter, hfilter]
      have hxne : x ≠ -x := by
        intro hcon
        apply hx
        have h2 : (2 : ZMod p) * x = 0 := by linear_combination hcon
        rcases mul_eq_zero.mp h2 with h | h
        · exact absurd h (Ring.two_ne_zero hchar)
        · exact h
      rw [Finset.sum_insert (by rw [Finset.mem_singleton]; exact hxne), Finset.sum_singleton]
      rw [show x * -x = -1 * x ^ 2 from by ring, map_mul, map_mul, quadraticChar_sq_one' hx,
        hneg1]
      have hsq := quadraticChar_sq_one (F := ZMod p) hx
      linear_combination hsq
  rw [Finset.sum_congr rfl fun x _ => hpair x]
  rw [← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod p)), if_pos rfl, zero_add]
  rw [Finset.sum_congr rfl fun x hx => if_neg (Finset.mem_erase.mp hx).1]
  rw [Finset.sum_const, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, ZMod.card]
  have hp1' : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  rw [nsmul_eq_mul, Nat.cast_sub hp1']
  push_cast
  ring

private lemma jac_zero (hp2 : p ≠ 2) : jac p 0 = 0 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  unfold jac
  refine Eq.trans (Finset.sum_congr rfl fun x _ => ?_) (quadraticChar_sum_zero hchar)
  by_cases hx : x = 0
  · subst hx
    rw [show ((0 : ZMod p)) ^ 2 + 0 = 0 from by ring, (quadraticChar (ZMod p)).map_zero]
    ring
  · rw [add_zero, quadraticChar_sq_one' hx, mul_one]

/-- **The two-squares ledger**: `jac(1)² + jac(r)² = 4p` for any non-residue `r`. -/
theorem jac_sq_ledger (hp2 : p ≠ 2) (hp1 : p % 4 = 1) {r : ZMod p}
    (hr : quadraticChar (ZMod p) r = -1) :
    jac p 1 ^ 2 + jac p r ^ 2 = 4 * (p : ℤ) := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have hr0 : r ≠ 0 := by
    intro hcon
    rw [hcon, (quadraticChar (ZMod p)).map_zero] at hr
    norm_num at hr
  have hkey : ∀ D : ZMod p, D ≠ 0 →
      2 * jac p D ^ 2 = (jac p 1 ^ 2 + jac p r ^ 2) +
        quadraticChar (ZMod p) D * (jac p 1 ^ 2 - jac p r ^ 2) := by
    intro D hD
    by_cases hsq : IsSquare D
    · obtain ⟨t, rfl⟩ := hsq
      have ht : t ≠ 0 := by
        intro h
        apply hD
        rw [h, mul_zero]
      have h1 : jac p (t * t) = quadraticChar (ZMod p) t * jac p 1 := by
        rw [show t * t = t ^ 2 * 1 from by ring]
        exact jac_mul_sq ht 1
      have hχ : quadraticChar (ZMod p) (t * t) = 1 := by
        rw [show t * t = t ^ 2 from (sq t).symm]
        exact quadraticChar_sq_one' ht
      rw [h1, hχ, mul_pow, quadraticChar_sq_one ht]
      ring
    · have hχD : quadraticChar (ZMod p) D = -1 :=
        quadraticChar_neg_one_iff_not_isSquare.mpr hsq
      have hu : IsSquare (D / r) := by
        rw [← quadraticChar_one_iff_isSquare (div_ne_zero hD hr0)]
        have hmul : quadraticChar (ZMod p) (D / r * r)
            = quadraticChar (ZMod p) (D / r) * quadraticChar (ZMod p) r := map_mul _ _ _
        rw [div_mul_cancel₀ _ hr0, hχD, hr] at hmul
        linarith
      obtain ⟨t, ht2⟩ := hu
      rw [div_eq_iff hr0] at ht2
      have ht : t ≠ 0 := by
        intro h
        rw [h, mul_zero, zero_mul] at ht2
        exact hD ht2
      have hD2 : D = t ^ 2 * r := by
        rw [ht2]
        ring
      have h1 : jac p D = quadraticChar (ZMod p) t * jac p r := by
        rw [hD2]
        exact jac_mul_sq ht r
      rw [h1, hχD, mul_pow, quadraticChar_sq_one ht]
      ring
  have hsum0 : ∑ D ∈ (univ : Finset (ZMod p)).erase 0, jac p D ^ 2
      = 2 * p * ((p : ℤ) - 1) := by
    have h := sum_jac_sq (p := p) hp2 hp1
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod p)), jac_zero hp2] at h
    simpa using h
  have hchi0 : ∑ D ∈ (univ : Finset (ZMod p)).erase 0, quadraticChar (ZMod p) D = 0 := by
    have h := quadraticChar_sum_zero (F := ZMod p) hchar
    rw [← Finset.add_sum_erase _ _ (mem_univ (0 : ZMod p)),
      (quadraticChar (ZMod p)).map_zero, zero_add] at h
    exact h
  have hp3 : (3 : ℕ) ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    omega
  have hbig : 2 * (2 * p * ((p : ℤ) - 1))
      = ((p : ℤ) - 1) * (jac p 1 ^ 2 + jac p r ^ 2) := by
    calc 2 * (2 * p * ((p : ℤ) - 1))
        = 2 * ∑ D ∈ (univ : Finset (ZMod p)).erase 0, jac p D ^ 2 := by rw [hsum0]
      _ = ∑ D ∈ (univ : Finset (ZMod p)).erase 0, 2 * jac p D ^ 2 := Finset.mul_sum _ _ _
      _ = ∑ D ∈ (univ : Finset (ZMod p)).erase 0, ((jac p 1 ^ 2 + jac p r ^ 2) +
            quadraticChar (ZMod p) D * (jac p 1 ^ 2 - jac p r ^ 2)) :=
          Finset.sum_congr rfl fun D hD => hkey D (Finset.mem_erase.mp hD).1
      _ = ((p : ℤ) - 1) * (jac p 1 ^ 2 + jac p r ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.sum_mul, hchi0, zero_mul,
            add_zero, Finset.card_erase_of_mem (mem_univ _), Finset.card_univ, ZMod.card,
            nsmul_eq_mul, Nat.cast_sub (Fact.out : p.Prime).one_lt.le]
          push_cast
          ring
  have hne : ((p : ℤ) - 1) ≠ 0 := by
    have : (3 : ℤ) ≤ (p : ℤ) := by exact_mod_cast hp3
    omega
  apply mul_left_cancel₀ hne
  linarith [hbig]

/-- A finset carrying a free action of the Klein four-group has cardinality divisible
by four.  Stated with two commuting involutions whose composite is also fixed-point
free. -/
private lemma card_dvd_four_of_klein {α : Type*} [DecidableEq α] :
    ∀ s : Finset α, ∀ σ τ : α → α,
    (∀ x ∈ s, σ x ∈ s) → (∀ x ∈ s, τ x ∈ s) →
    (∀ x ∈ s, σ (σ x) = x) → (∀ x ∈ s, τ (τ x) = x) →
    (∀ x ∈ s, σ (τ x) = τ (σ x)) →
    (∀ x ∈ s, σ x ≠ x) → (∀ x ∈ s, τ x ≠ x) → (∀ x ∈ s, σ (τ x) ≠ x) →
    4 ∣ s.card := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro σ τ hσm hτm hσσ hττ hcomm hσne hτne hστne
    rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
    · simp
    have hτa : τ a ∈ s := hτm a ha
    have hσa : σ a ∈ s := hσm a ha
    have hστa : σ (τ a) ∈ s := hσm _ hτa
    have hd1 : σ a ≠ a := hσne a ha
    have hd2 : τ a ≠ a := hτne a ha
    have hd3 : σ (τ a) ≠ a := hστne a ha
    have hd4 : τ a ≠ σ a := by
      intro h
      apply hd3
      rw [h, hσσ a ha]
    have hd5 : σ (τ a) ≠ σ a := by
      intro h
      apply hd2
      have h2 := congrArg σ h
      rwa [hσσ _ hτa, hσσ _ ha] at h2
    have hd6 : σ (τ a) ≠ τ a := hσne _ hτa
    set O : Finset α := insert a (insert (σ a) (insert (τ a) {σ (τ a)})) with hO
    have hcard : O.card = 4 := by
      rw [hO, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · rw [Finset.mem_singleton]
        exact hd6.symm
      · rw [Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨hd4.symm, hd5.symm⟩
      · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
        push_neg
        exact ⟨hd1.symm, hd2.symm, hd3.symm⟩
    have hmemO : ∀ x, x ∈ O ↔ x = a ∨ x = σ a ∨ x = τ a ∨ x = σ (τ a) := by
      intro x
      rw [hO]
      simp [Finset.mem_insert, Finset.mem_singleton]
    have hOsub : O ⊆ s := by
      intro x hx
      rcases (hmemO x).mp hx with rfl | rfl | rfl | rfl <;> assumption
    have hσO : ∀ x ∈ O, σ x ∈ O := by
      intro x hx
      rcases (hmemO x).mp hx with rfl | rfl | rfl | rfl <;> rw [hmemO]
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl (hσσ a ha)
      · exact Or.inr (Or.inr (Or.inr rfl))
      · exact Or.inr (Or.inr (Or.inl (hσσ _ hτa)))
    have hτO : ∀ x ∈ O, τ x ∈ O := by
      intro x hx
      rcases (hmemO x).mp hx with rfl | rfl | rfl | rfl <;> rw [hmemO]
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (hcomm a ha).symm))
      · exact Or.inl (hττ a ha)
      · refine Or.inr (Or.inl ?_)
        rw [← hcomm _ hτa, hττ _ ha]
    set s' : Finset α := s \ O with hs'
    have hs'card : s.card = s'.card + 4 := by
      rw [hs', Finset.card_sdiff, Finset.inter_eq_left.mpr hOsub, hcard]
      have := Finset.card_le_card hOsub
      omega
    have hlt : s' ⊂ s := by
      rw [hs']
      refine Finset.sdiff_ssubset hOsub ?_
      exact ⟨a, (hmemO a).mpr (Or.inl rfl)⟩
    have hmem' : ∀ x ∈ s', x ∈ s ∧ x ∉ O := by
      intro x hx
      rw [hs', Finset.mem_sdiff] at hx
      exact hx
    have hstep : ∀ (ρ : α → α), (∀ x ∈ s, ρ x ∈ s) → (∀ x ∈ O, ρ x ∈ O) →
        (∀ x ∈ s, ρ (ρ x) = x) → ∀ x ∈ s', ρ x ∈ s' := by
      intro ρ hρs hρO hρρ x hx
      obtain ⟨hxs, hxO⟩ := hmem' x hx
      rw [hs', Finset.mem_sdiff]
      refine ⟨hρs x hxs, fun hcon => hxO ?_⟩
      have := hρO _ hcon
      rwa [hρρ x hxs] at this
    have ih' := ih s' hlt σ τ
      (hstep σ hσm hσO hσσ) (hstep τ hτm hτO hττ)
      (fun x hx => hσσ x (hmem' x hx).1) (fun x hx => hττ x (hmem' x hx).1)
      (fun x hx => hcomm x (hmem' x hx).1)
      (fun x hx => hσne x (hmem' x hx).1) (fun x hx => hτne x (hmem' x hx).1)
      (fun x hx => hστne x (hmem' x hx).1)
    omega

/-- **The normalization congruence**: `jac p 1 ≡ −2 (mod 8)`.  The summand
`χ(x(x²+1))` is invariant under the free Klein action `x ↦ −x, x ↦ x⁻¹` away from its
zero set and the two points `±1`, so the minus-population has size divisible by four;
the points `±1` contribute `2χ(2)`, and the supplement `χ(2) = ±1` at `p ≡ 1, 5
(mod 8)` closes both cases uniformly. -/
theorem jac_one_mod_eight (hp2 : p ≠ 2) (hp1 : p % 4 = 1) :
    ∃ k : ℤ, jac p 1 = 8 * k - 2 := by
  have hchar : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    exact hp2
  have h2Z : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero hchar
  have hneg1 : quadraticChar (ZMod p) (-1) = 1 := by
    rw [quadraticChar_neg_one hchar, ZMod.card]
    exact ZMod.χ₄_nat_one_mod_four hp1
  obtain ⟨i0, hi⟩ : IsSquare (-1 : ZMod p) := by
    rw [ZMod.exists_sq_eq_neg_one_iff]
    omega
  have hi2 : i0 * i0 = -1 := hi.symm
  have hi0 : i0 ≠ 0 := by
    intro h
    apply one_ne_zero (α := ZMod p)
    have h0 : (0 : ZMod p) = -1 := by rw [← hi2, h, mul_zero]
    linear_combination h0
  have hm1ne1 : (1 : ZMod p) ≠ -1 := by
    intro h
    apply h2Z
    linear_combination h
  set f : ZMod p → ℤ := fun x => quadraticChar (ZMod p) (x * (x ^ 2 + 1)) with hf_def
  have hjac : jac p 1 = ∑ x : ZMod p, f x := by
    rw [jac]
    refine Finset.sum_congr rfl fun x _ => ?_
    show quadraticChar (ZMod p) x * quadraticChar (ZMod p) (x ^ 2 + 1)
      = quadraticChar (ZMod p) (x * (x ^ 2 + 1))
    rw [map_mul]
  set Z : Finset (ZMod p) := univ.filter fun x => x * (x ^ 2 + 1) = 0 with hZ_def
  have hZ3 : Z.card = 3 := by
    have hZeq : Z = insert 0 (insert i0 {-i0}) := by
      ext x
      rw [hZ_def, Finset.mem_filter, Finset.mem_insert, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · rintro ⟨-, h⟩
        rcases mul_eq_zero.mp h with h | h
        · exact Or.inl h
        · have hfac : (x - i0) * (x + i0) = 0 := by linear_combination h - hi2
          rcases mul_eq_zero.mp hfac with h1 | h1
          · exact Or.inr (Or.inl (by linear_combination h1))
          · exact Or.inr (Or.inr (by linear_combination h1))
      · rintro (rfl | h | h)
        · exact ⟨mem_univ _, by ring⟩
        · exact ⟨mem_univ _, by rw [h]; linear_combination i0 * hi2⟩
        · exact ⟨mem_univ _, by rw [h]; linear_combination -(i0 * hi2)⟩
    rw [hZeq, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
      Finset.card_singleton]
    · rw [Finset.mem_singleton]
      intro h
      apply hi0
      have h4 : (2 : ZMod p) * i0 = 0 := by linear_combination h
      rcases mul_eq_zero.mp h4 with h | h
      · exact absurd h h2Z
      · exact h
    · rw [Finset.mem_insert, Finset.mem_singleton]
      push_neg
      exact ⟨fun h => hi0 h.symm, fun h => hi0 (neg_eq_zero.mp h.symm)⟩
  have hZ0 : ∑ x ∈ Z, f x = 0 := by
    refine Finset.sum_eq_zero fun x hx => ?_
    rw [hZ_def, Finset.mem_filter] at hx
    show quadraticChar (ZMod p) (x * (x ^ 2 + 1)) = 0
    rw [hx.2]
    exact (quadraticChar (ZMod p)).map_zero
  have h1Z : (1 : ZMod p) ∉ Z := by
    rw [hZ_def, Finset.mem_filter]
    push_neg
    intro _ h
    apply h2Z
    linear_combination h
  have hm1Z : (-1 : ZMod p) ∉ Z := by
    rw [hZ_def, Finset.mem_filter]
    push_neg
    intro _ h
    apply h2Z
    linear_combination -h
  set B : Finset (ZMod p) := insert (1 : ZMod p) {(-1 : ZMod p)} with hB_def
  have hm1memB : (1 : ZMod p) ∉ ({(-1 : ZMod p)} : Finset (ZMod p)) := by
    rw [Finset.mem_singleton]
    exact hm1ne1
  have hcardB : B.card = 2 := by
    rw [hB_def, Finset.card_insert_of_notMem hm1memB, Finset.card_singleton]
  have hsumB : ∑ x ∈ B, f x = 2 * quadraticChar (ZMod p) 2 := by
    rw [hB_def, Finset.sum_insert hm1memB, Finset.sum_singleton]
    show quadraticChar (ZMod p) (1 * (1 ^ 2 + 1)) +
      quadraticChar (ZMod p) (-1 * ((-1) ^ 2 + 1)) = _
    rw [show (1 : ZMod p) * (1 ^ 2 + 1) = 2 from by ring,
      show (-1 : ZMod p) * ((-1) ^ 2 + 1) = -1 * 2 from by ring, map_mul, hneg1]
    ring
  have hdisj : Disjoint Z B := by
    rw [Finset.disjoint_right]
    intro x hx
    rw [hB_def, Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact h1Z
    · exact hm1Z
  set ZB : Finset (ZMod p) := Z ∪ B with hZB_def
  have hcardZB : ZB.card = 5 := by
    rw [hZB_def, Finset.card_union_of_disjoint hdisj, hZ3, hcardB]
  have hsumZB : ∑ x ∈ ZB, f x = 2 * quadraticChar (ZMod p) 2 := by
    rw [hZB_def, Finset.sum_union hdisj, hZ0, hsumB, zero_add]
  set S : Finset (ZMod p) := univ \ ZB with hS_def
  have hcardS : S.card = p - 5 := by
    rw [hS_def, Finset.card_sdiff, Finset.inter_eq_left.mpr (Finset.subset_univ _),
      hcardZB, Finset.card_univ, ZMod.card]
  have hsplit : ∑ x : ZMod p, f x = ∑ x ∈ S, f x + ∑ x ∈ ZB, f x := by
    rw [hS_def]
    exact (Finset.sum_sdiff (Finset.subset_univ _)).symm
  have hSiff : ∀ x : ZMod p, x ∈ S ↔ x ≠ 0 ∧ x ^ 2 + 1 ≠ 0 ∧ x ≠ 1 ∧ x ≠ -1 := by
    intro x
    rw [hS_def, Finset.mem_sdiff, hZB_def, Finset.mem_union, hZ_def, Finset.mem_filter,
      hB_def, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hx⟩
      push_neg at hx
      obtain ⟨hZc, h1c, hm1c⟩ := hx
      have hprod : x * (x ^ 2 + 1) ≠ 0 := hZc (mem_univ _)
      obtain ⟨hx0, hx1⟩ := mul_ne_zero_iff.mp hprod
      exact ⟨hx0, hx1, h1c, hm1c⟩
    · rintro ⟨hx0, hx1, h1, hm1⟩
      refine ⟨mem_univ _, ?_⟩
      push_neg
      exact ⟨fun _ => mul_ne_zero hx0 hx1, h1, hm1⟩
  have hSne : ∀ x ∈ S, f x = 1 ∨ f x = -1 := by
    intro x hx
    obtain ⟨hx0, hx1, -, -⟩ := (hSiff x).mp hx
    exact quadraticChar_dichotomy (mul_ne_zero hx0 hx1)
  have hfneg : ∀ x : ZMod p, f (-x) = f x := by
    intro x
    show quadraticChar (ZMod p) (-x * ((-x) ^ 2 + 1)) = quadraticChar (ZMod p) (x * (x ^ 2 + 1))
    rw [show -x * ((-x) ^ 2 + 1) = -1 * (x * (x ^ 2 + 1)) from by ring, map_mul, hneg1,
      one_mul]
  have hfinv : ∀ x : ZMod p, x ≠ 0 → f x⁻¹ = f x := by
    intro x hx0
    show quadraticChar (ZMod p) (x⁻¹ * ((x⁻¹) ^ 2 + 1)) = quadraticChar (ZMod p) (x * (x ^ 2 + 1))
    have hfac : x⁻¹ * ((x⁻¹) ^ 2 + 1) = (x⁻¹ ^ 2) ^ 2 * (x * (x ^ 2 + 1)) := by
      field_simp
      ring
    rw [hfac, map_mul, quadraticChar_sq_one' (pow_ne_zero 2 (inv_ne_zero hx0)), one_mul]
  have hSneg : ∀ x ∈ S, -x ∈ S := by
    intro x hx
    obtain ⟨hx0, hx1, h1, hm1⟩ := (hSiff x).mp hx
    refine (hSiff (-x)).mpr ⟨neg_ne_zero.mpr hx0, ?_, ?_, ?_⟩
    · rw [show (-x) ^ 2 + 1 = x ^ 2 + 1 from by ring]
      exact hx1
    · intro h
      exact hm1 (by linear_combination -h)
    · intro h
      exact h1 (by linear_combination -h)
  have hSinv : ∀ x ∈ S, x⁻¹ ∈ S := by
    intro x hx
    obtain ⟨hx0, hx1, h1, hm1⟩ := (hSiff x).mp hx
    refine (hSiff x⁻¹).mpr ⟨inv_ne_zero hx0, ?_, ?_, ?_⟩
    · intro h
      apply hx1
      have h2 : x ^ 2 * ((x⁻¹) ^ 2 + 1) = 0 := by rw [h, mul_zero]
      rw [mul_add, mul_one, show x ^ 2 * (x⁻¹) ^ 2 = (x * x⁻¹) ^ 2 from by ring,
        mul_inv_cancel₀ hx0] at h2
      linear_combination h2
    · intro h
      exact h1 (inv_eq_one.mp h)
    · intro h
      apply hm1
      rw [← inv_neg_one] at h
      exact inv_injective h
  set M : Finset (ZMod p) := S.filter (fun x => f x = -1) with hM_def
  have hMmem : ∀ x ∈ M, x ∈ S ∧ f x = -1 := by
    intro x hx
    rw [hM_def, Finset.mem_filter] at hx
    exact hx
  have hM4 : 4 ∣ M.card := by
    refine card_dvd_four_of_klein M (fun x => -x) (fun x => x⁻¹) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · intro x hx
      obtain ⟨hxS, hxf⟩ := hMmem x hx
      rw [hM_def, Finset.mem_filter]
      exact ⟨hSneg x hxS, by rw [hfneg]; exact hxf⟩
    · intro x hx
      obtain ⟨hxS, hxf⟩ := hMmem x hx
      obtain ⟨hx0, -, -, -⟩ := (hSiff x).mp hxS
      rw [hM_def, Finset.mem_filter]
      exact ⟨hSinv x hxS, by rw [hfinv x hx0]; exact hxf⟩
    · intro x _
      exact neg_neg x
    · intro x _
      exact inv_inv x
    · intro x _
      exact (inv_neg (a := x)).symm
    · intro x hx
      obtain ⟨hxS, -⟩ := hMmem x hx
      obtain ⟨hx0, -, -, -⟩ := (hSiff x).mp hxS
      intro h
      apply hx0
      have h2 : (2 : ZMod p) * x = 0 := by linear_combination -h
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h h2Z
      · exact h
    · intro x hx
      obtain ⟨hxS, -⟩ := hMmem x hx
      obtain ⟨hx0, -, h1, hm1⟩ := (hSiff x).mp hxS
      intro h
      have h' : x⁻¹ = x := h
      have hsq : x * x = 1 := by
        nth_rewrite 2 [← h']
        exact mul_inv_cancel₀ hx0
      have hfac : (x - 1) * (x + 1) = 0 := by linear_combination hsq
      rcases mul_eq_zero.mp hfac with h | h
      · exact h1 (by linear_combination h)
      · exact hm1 (by linear_combination h)
    · intro x hx
      obtain ⟨hxS, -⟩ := hMmem x hx
      obtain ⟨hx0, hx1, -, -⟩ := (hSiff x).mp hxS
      intro h
      apply hx1
      have h' : -x⁻¹ = x := h
      have h2 : x * -x⁻¹ = x * x := by rw [h']
      rw [mul_neg, mul_inv_cancel₀ hx0] at h2
      linear_combination -h2
  set N : Finset (ZMod p) := S.filter (fun x => ¬f x = -1) with hN_def
  have hsumS : ∑ x ∈ S, f x = (N.card : ℤ) - (M.card : ℤ) := by
    rw [← Finset.sum_filter_add_sum_filter_not S (fun x => f x = -1)]
    have hM1 : ∑ x ∈ M, f x = -(M.card : ℤ) := by
      rw [Finset.sum_congr rfl (fun x hx => (hMmem x hx).2), Finset.sum_const,
        nsmul_eq_mul]
      ring
    have hpt : ∀ x ∈ N, f x = 1 := by
      intro x hx
      rw [hN_def, Finset.mem_filter] at hx
      rcases hSne x hx.1 with h | h
      · exact h
      · exact absurd h hx.2
    have hN1 : ∑ x ∈ N, f x = (N.card : ℤ) := by
      rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [show S.filter (fun x => f x = -1) = M from (hM_def).symm,
      show S.filter (fun x => ¬f x = -1) = N from (hN_def).symm, hM1, hN1]
    ring
  have hcardMN : M.card + N.card = p - 5 := by
    have h := Finset.filter_card_add_filter_neg_card_eq_card
      (s := S) (p := fun x => f x = -1)
    rw [show S.filter (fun x => f x = -1) = M from (hM_def).symm] at h
    rw [show S.filter (fun x => ¬f x = -1) = N from (hN_def).symm] at h
    rw [hcardS] at h
    exact h
  obtain ⟨m, hm⟩ := hM4
  have hp5 : 5 ≤ p := by
    have h2 := (Fact.out : p.Prime).two_le
    omega
  have hp8 : p % 8 = 1 ∨ p % 8 = 5 := by omega
  have hNz : (N.card : ℤ) = (p : ℤ) - 5 - 4 * (m : ℤ) := by
    have h1 : (M.card : ℤ) + (N.card : ℤ) = (p : ℤ) - 5 := by
      have := congrArg (Nat.cast : ℕ → ℤ) hcardMN
      push_cast [Nat.cast_sub hp5] at this
      linarith [this]
    have h2 : (M.card : ℤ) = 4 * (m : ℤ) := by exact_mod_cast hm
    linarith
  have hMz : (M.card : ℤ) = 4 * (m : ℤ) := by exact_mod_cast hm
  rcases hp8 with h8 | h8
  · have hc2 : quadraticChar (ZMod p) 2 = 1 := by
      rw [quadraticChar_one_iff_isSquare h2Z, ZMod.exists_sq_eq_two_iff hp2]
      exact Or.inl h8
    obtain ⟨t, ht⟩ : ∃ t, p = 8 * t + 1 := ⟨p / 8, by omega⟩
    refine ⟨(t : ℤ) - (m : ℤ), ?_⟩
    rw [hjac, hsplit, hsumS, hsumZB, hc2]
    have hpz : (p : ℤ) = 8 * (t : ℤ) + 1 := by exact_mod_cast ht
    linarith [hNz, hMz, hpz]
  · have hc2 : quadraticChar (ZMod p) 2 = -1 := by
      rw [quadraticChar_neg_one_iff_not_isSquare, ZMod.exists_sq_eq_two_iff hp2]
      push_neg
      omega
    obtain ⟨t, ht⟩ : ∃ t, p = 8 * t + 5 := ⟨p / 8, by omega⟩
    refine ⟨(t : ℤ) - (m : ℤ), ?_⟩
    rw [hjac, hsplit, hsumS, hsumZB, hc2]
    have hpz : (p : ℤ) = 8 * (t : ℤ) + 5 := by exact_mod_cast ht
    linarith [hNz, hMz, hpz]

end Soma.Holonics.Millennium.GaussCoefficient
