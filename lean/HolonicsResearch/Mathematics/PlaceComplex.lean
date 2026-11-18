import Mathlib

/-!
# The place complex: a number is a class of digit chains, carrying is solving for the boundary, and a width is a need

[proved-standard] The source is the record of November 8
(`research/records/2026-11-08_A_NUMBER_IS_A_CLASS_ON_A_GRAPH_OF_PLACES_AND_EVERY_METHOD_IS_A_BRACKETING_A_CHART_OR_AN_END.md`,
§2.1, §5.1, §9 N3 and §10 step 1; atlas `radix.place-complex`, `radix.digit-face-calculus`, `radix.product-decomposition`,
`arith.inversion-two-ends`). These are the Lean obligations that record's build order names for the number owner.

What is proved.

1. **The carry-complex identity** (§2.1). A digit chain is a polynomial in the place variable `x`; the boundary of the
   carry edge `k → k+1` is `b·xᵏ − xᵏ⁺¹` (`boundary_edge`). Two chains name one value at radix `b` exactly when their
   difference is a boundary `(b − x)·t` (`names_one_iff`; on digit lists, `digits_name_one_iff`), the boundaries are the
   ideal of `x − b` (`mem_span_iff_boundary`), the carry chain `t` is unique over a domain (`boundary_injective`), and
   evaluation at `x = b` identifies the classes with the ring (`placeHomology`, `placeHomology_mk`; Mathlib's
   `Polynomial.quotientSpanXSubCAlgEquiv`). Canonical digits are one section (`eval_chain_digits`). Binary addition is one
   boundary step: `a + b = (a ⊕ b) + 2(a ∧ b)` (`add_eq_xor_add_two_mul_and`).
2. **The carries of a sum and of counting** (§2.1 and atlas `radix.digit-face-calculus`). For every radix, the carry chain
   of a sum exists (`exists_sum_carry`) and the digit sums' defect is `(b − 1)` times its total (`digit_sum_defect`);
   the carry chain of the raw count `N` at place zero exists (`exists_count_carry`) and its total is the summed
   valuation `Σ_(k ≤ N) v_b(k)` (`count_carry_total`).
3. **Kummer, Legendre and Lucas at a prime radix, joined to the place complex.** Mathlib's digit forms restated
   (`legendre`, `kummer_carries`, `lucas_digits`); a carry into a place is zero or one and Kummer's count is the sum of
   those carries (`carry_le_one`, `carry_eq_one_iff`, `kummer_sum_of_carries`); the valuation of `C(m + n, m)` is the
   total of the sum's carry chain (`kummer_is_total_carry`); and the valuation of `N!` is the total of the count's carry
   chain (`legendre_is_total_carry`), equal to the summed valuations (`sum_valuation_eq_factorial`).
4. **The increment's digit-sum identity** at every radix `b ≥ 2`, with `v_b` the multiplicity of `b`:
   `s_b(n + 1) − s_b(n) = 1 − (b − 1)·v_b(n + 1)` (`digit_sum_succ`), and summed,
   `(b − 1)·Σ_(k ≤ N) v_b(k) = N − s_b(N)` (`sum_valuation_eq`). At a composite radix the sum is not the valuation of
   the factorial (`composite_radix_differs`: radix ten, `N = 5`, zero against one), and Lucas's congruence fails at
   radix four (`lucas_fails_at_four`).
5. **The Newton residual square** (§5.1) in any ring, commutative or not: `1 − A·X(2 − AX) = (1 − AX)²`
   (`newton_residual_square`), the carried form `X′ = X(1 + E)`, `E′ = E²` (`newton_step_carried`, `newton_carried`),
   the iterate `E_k = E^(2^k)` (`newton_iterate`), the released top end `e′ = e² − a·r` with `r` the released value less
   the unreleased one (`newton_released`), and the bottom end's doubling of the places that agree
   (`newton_bottom_end`).
6. **A width is a need** (§9 N3). In the low section a sum of two needs the wider plus one (`sum_width`,
   `sum_width_needed`), `n` terms the widest plus `⌈log₂ n⌉` (`sum_n_width`), a product `w_a + w_b` (`product_width`).
   With the signed section of `w` places `−2^(w−1) ≤ x < 2^(w−1)` (`Signed`): a low operand of `w` places takes `w + 1`
   signed places (`low_in_signed`), signed sums need the wider plus one (`signed_add`), a low operand meeting a signed one
   needs `max(w_a + 1, w_b) + 1` (`low_add_signed`, with the witness `3 + 1` at two places each, `low_add_signed_witness`,
   and one fewer when the signed operand has a single place, `low_add_single_signed`), a difference of two low operands
   is signed at the wider plus one (`low_sub_low`), and a product needs `w_a + w_b` in every pair of sections
   (`low_mul_low`, `low_mul_signed`, `signed_mul_signed`).

Limits. The chains are polynomials, so finitely many places from the lowest one; the closing edges of §2.2 (rings,
twists, Solinas) are not here. Statement 2 names the carry chain as the boundary's solution; that its coefficients are
the place-by-place carries of the schoolbook sum is Kummer's reading in Mathlib's form (`kummer_sum_of_carries`), not a
separate identification of coefficients. The widths are those of N3 for sums, differences and products; the release
widths of N5 are not here.

The computational object is the helical pair interaction: a carry edge is the pair contact of two neighbouring places,
and the boundary is its slip. Of the winding guide's six general objects this touches the helix (a place's digit and
its carry are a winding and its phase), faces and placement (the digit face and its derivative) and the tower thread
(the places of one radix); the pair, cell holonomy and tube stay attached.

Consumers: #410's box for the number owner's laws; atlas `radix.place-complex`, `radix.digit-face-calculus`,
`radix.product-decomposition` (Kummer), `arith.inversion-two-ends`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Mathematics.PlaceComplex

open Polynomial

/-! ## 1. The complex -/

section Complex

variable {R : Type*} [CommRing R]

/-- The boundary of a carry chain `t` at radix `b`: `(b − x)·t`. -/
noncomputable def boundary (b : R) (t : R[X]) : R[X] := (C b - X) * t

/-- [proved-standard] The boundary of the carry edge `k → k+1` is `b·e_k − e_(k+1)`. -/
theorem boundary_edge (b : R) (k : ℕ) : boundary b (X ^ k) = C b * X ^ k - X ^ (k + 1) := by
  unfold boundary
  ring

/-- [proved-standard] A boundary names zero. -/
theorem eval_boundary (b : R) (t : R[X]) : (boundary b t).eval b = 0 := by
  simp [boundary]

/-- [proved-standard] A boundary's reading at `x = 1` is `(b − 1)` times the carry chain's total. -/
theorem eval_one_boundary (b : R) (t : R[X]) : (boundary b t).eval 1 = (b - 1) * t.eval 1 := by
  simp [boundary]

/-- [proved-standard] **The carry-complex identity**: two chains name one value at radix `b` exactly when their
difference is a boundary `(b − x)·t`. -/
theorem names_one_iff (b : R) (c d : R[X]) : c.eval b = d.eval b ↔ ∃ t, d - c = boundary b t := by
  constructor
  · intro h
    have hroot : (d - c).IsRoot b := by
      rw [IsRoot, eval_sub, h, sub_self]
    obtain ⟨q, hq⟩ := dvd_iff_isRoot.mpr hroot
    refine ⟨-q, ?_⟩
    rw [hq]
    unfold boundary
    ring
  · rintro ⟨t, ht⟩
    have h := congrArg (eval b) ht
    rw [eval_sub, eval_boundary] at h
    exact (sub_eq_zero.mp h).symm

/-- [proved-standard] The boundaries are the ideal of `x − b`. -/
theorem mem_span_iff_boundary (b : R) (p : R[X]) :
    p ∈ Ideal.span ({X - C b} : Set R[X]) ↔ ∃ t, p = boundary b t := by
  rw [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨-q, ?_⟩
    rw [hq]
    unfold boundary
    ring
  · rintro ⟨t, ht⟩
    refine ⟨-t, ?_⟩
    rw [ht]
    unfold boundary
    ring

/-- [proved-standard] Over a domain the carry chain is unique. -/
theorem boundary_injective [IsDomain R] (b : R) : Function.Injective (boundary b) := by
  intro s t h
  have hne : C b - X ≠ (0 : R[X]) := by
    intro h0
    have h1 : X - C b = (0 : R[X]) := by
      rw [← neg_sub, h0, neg_zero]
    exact X_sub_C_ne_zero b h1
  exact mul_left_cancel₀ hne h

/-- **The values are the zeroth homology of the place complex**: chains modulo boundaries are the ring, by evaluation
at `x = b` (Mathlib's `Polynomial.quotientSpanXSubCAlgEquiv`). -/
noncomputable def placeHomology (b : R) : (R[X] ⧸ Ideal.span ({X - C b} : Set R[X])) ≃ₐ[R] R :=
  quotientSpanXSubCAlgEquiv b

/-- [proved-standard] The identification reads a chain's class as its value at `x = b`. -/
theorem placeHomology_mk (b : R) (p : R[X]) : placeHomology b (Ideal.Quotient.mk _ p) = p.eval b :=
  rfl

end Complex

/-- The chain of a digit list: place `k` holds the `k`-th digit, lowest first. -/
noncomputable def chain : List ℕ → ℤ[X]
  | [] => 0
  | a :: L => C (a : ℤ) + X * chain L

/-- [proved-standard] A chain's value at radix `b` is the digit list's. -/
theorem eval_chain (b : ℤ) (L : List ℕ) : (chain L).eval b = Nat.ofDigits b L := by
  induction L with
  | nil => simp [chain, Nat.ofDigits]
  | cons a L ih =>
    have hcons : Nat.ofDigits b (a :: L) = (a : ℤ) + b * Nat.ofDigits b L := rfl
    rw [hcons, ← ih]
    simp [chain]

/-- [proved-standard] A chain's reading at `x = 1` is its digit sum. -/
theorem eval_one_chain (L : List ℕ) : (chain L).eval 1 = ((L.sum : ℕ) : ℤ) := by
  induction L with
  | nil => simp [chain]
  | cons a L ih => simp [chain, ih]

/-- [proved-standard] **Canonical digits are one section**: the chain of `n`'s digits names `n`. -/
theorem eval_chain_digits (b n : ℕ) : (chain (Nat.digits b n)).eval (b : ℤ) = n := by
  rw [eval_chain, ← Nat.coe_ofDigits, Nat.ofDigits_digits]

/-- [proved-standard] **Digit vectors `c`, `d` name one integer exactly when `d − c = (b − x)·t`.** -/
theorem digits_name_one_iff (b : ℤ) (L M : List ℕ) :
    Nat.ofDigits b L = Nat.ofDigits b M ↔ ∃ t, chain M - chain L = boundary b t := by
  rw [← eval_chain, ← eval_chain]
  exact names_one_iff b (chain L) (chain M)

/-- [proved-standard] **Binary addition is one boundary step**: `a + b = (a ⊕ b) + 2(a ∧ b)`, the AND moved up a place. -/
theorem add_eq_xor_add_two_mul_and (a b : ℕ) : a + b = (a ^^^ b) + 2 * (a &&& b) := by
  induction a using Nat.strong_induction_on generalizing b with
  | _ a ih =>
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    · have h := ih (a / 2) (Nat.div_lt_self ha (by norm_num)) (b / 2)
      have hx := @Nat.xor_div_two a b
      have hn := @Nat.and_div_two a b
      have hx1 := @Nat.xor_mod_two_eq_one a b
      have hn1 := @Nat.and_mod_two_eq_one a b
      rw [← hx, ← hn] at h
      omega

/-! ## 2. The carries of a sum and of counting -/

/-- [proved-standard] The carry chain of a sum exists at every radix. -/
theorem exists_sum_carry (b m n : ℕ) :
    ∃ t, chain (Nat.digits b m) + chain (Nat.digits b n) - chain (Nat.digits b (m + n)) = boundary (b : ℤ) t := by
  apply (names_one_iff (b : ℤ) _ _).mp
  rw [eval_add, eval_chain_digits, eval_chain_digits, eval_chain_digits]
  push_cast
  ring

/-- [proved-standard] **The digit sums' defect is `(b − 1)` times the total carry.** -/
theorem digit_sum_defect (b m n : ℕ) (t : ℤ[X])
    (ht : chain (Nat.digits b m) + chain (Nat.digits b n) - chain (Nat.digits b (m + n)) = boundary (b : ℤ) t) :
    (((Nat.digits b m).sum : ℕ) : ℤ) + ((Nat.digits b n).sum : ℕ) - ((Nat.digits b (m + n)).sum : ℕ) =
      ((b : ℤ) - 1) * t.eval 1 := by
  have h := congrArg (eval 1) ht
  rw [eval_sub, eval_add, eval_one_chain, eval_one_chain, eval_one_chain, eval_one_boundary] at h
  exact h

/-- [proved-standard] The carry chain of the raw count `N` at place zero exists at every radix. -/
theorem exists_count_carry (b N : ℕ) :
    ∃ t, C (N : ℤ) - chain (Nat.digits b N) = boundary (b : ℤ) t := by
  apply (names_one_iff (b : ℤ) _ _).mp
  rw [eval_chain_digits, eval_C]

/-! ## 3. The increment's digit-sum identity -/

private theorem digit_sum_step {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    (Nat.digits b n).sum = n % b + (Nat.digits b (n / b)).sum := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [Nat.digits_def' (by omega) hn, List.sum_cons]

/-- [proved-standard] **The increment's digit-sum identity**: at every radix `b ≥ 2`, with `v_b` the multiplicity of
`b`, `s_b(n + 1) − s_b(n) = 1 − (b − 1)·v_b(n + 1)`. The carry run is the defect of the digit face's derivative. -/
theorem digit_sum_succ {b : ℕ} (hb : 2 ≤ b) (n : ℕ) :
    (((Nat.digits b (n + 1)).sum : ℕ) : ℤ) - ((Nat.digits b n).sum : ℕ) =
      1 - ((b : ℤ) - 1) * (padicValNat b (n + 1) : ℕ) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have hq := Nat.div_add_mod n b
    have hr : n % b < b := Nat.mod_lt n (by omega)
    rw [digit_sum_step hb (n + 1), digit_sum_step hb n]
    by_cases hcase : n % b + 1 < b
    · have hsplit : n + 1 = (n % b + 1) + b * (n / b) := by omega
      have h1 : (n + 1) % b = n % b + 1 := by
        rw [hsplit, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hcase]
      have h2 : (n + 1) / b = n / b := by
        rw [hsplit, Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hcase, zero_add]
      have h3 : padicValNat b (n + 1) = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        rw [Nat.dvd_iff_mod_eq_zero, h1]
        omega
      rw [h1, h2, h3]
      simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
      ring
    · have hr' : n % b = b - 1 := by omega
      have hn1 : n + 1 = b * (n / b + 1) := by
        rw [mul_add, mul_one]
        omega
      have h1 : (n + 1) % b = 0 := by
        rw [hn1]
        exact Nat.mul_mod_right _ _
      have h2 : (n + 1) / b = n / b + 1 := by
        rw [hn1]
        exact Nat.mul_div_cancel_left _ (by omega)
      have h3 : padicValNat b (n + 1) = padicValNat b (n / b + 1) + 1 := by
        rw [hn1]
        exact padicValNat_base_mul (by omega) (Nat.succ_ne_zero _)
      have hle := Nat.mod_le n b
      have hnpos : 0 < n := by omega
      have hlt : n / b < n := Nat.div_lt_self hnpos (by omega)
      have hih := ih (n / b) hlt
      have hb1 : ((b - 1 : ℕ) : ℤ) = (b : ℤ) - 1 := by omega
      rw [h1, h2, h3, hr']
      simp only [zero_add, Nat.cast_add, Nat.cast_one, hb1]
      linear_combination hih

/-- [proved-standard] **Summing the carry run counts the carries of counting**: at every radix `b ≥ 2`,
`(b − 1)·Σ_(k ≤ N) v_b(k) = N − s_b(N)`. -/
theorem sum_valuation_eq {b : ℕ} (hb : 2 ≤ b) (N : ℕ) :
    ((b : ℤ) - 1) * ∑ k ∈ Finset.Icc 1 N, ((padicValNat b k : ℕ) : ℤ) = N - ((Nat.digits b N).sum : ℕ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    have h := digit_sum_succ hb N
    rw [Nat.cast_add, Nat.cast_one]
    linear_combination h

/-- [proved-standard] The total of the count's carry chain is the summed valuation, at every radix `b ≥ 2`. -/
theorem count_carry_total {b : ℕ} (hb : 2 ≤ b) (N : ℕ) (t : ℤ[X])
    (ht : C (N : ℤ) - chain (Nat.digits b N) = boundary (b : ℤ) t) :
    t.eval 1 = ∑ k ∈ Finset.Icc 1 N, ((padicValNat b k : ℕ) : ℤ) := by
  have h := congrArg (eval 1) ht
  rw [eval_sub, eval_C, eval_one_chain, eval_one_boundary] at h
  have hs := sum_valuation_eq hb N
  have hne : (b : ℤ) - 1 ≠ 0 := by
    have : (2 : ℤ) ≤ b := by exact_mod_cast hb
    omega
  apply mul_left_cancel₀ hne
  rw [← h, hs]

/-! ## 4. Kummer, Legendre and Lucas at a prime radix -/

section Prime

variable (p : ℕ) [hp : Fact p.Prime]

/-- [proved-standard] **Legendre** (Mathlib's `sub_one_mul_padicValNat_factorial`): `(p − 1)·v_p(N!) = N − s_p(N)`. -/
theorem legendre (N : ℕ) : (p - 1) * padicValNat p N.factorial = N - (Nat.digits p N).sum :=
  sub_one_mul_padicValNat_factorial N

/-- [proved-standard] Legendre in the integers, with no truncated subtraction. -/
theorem legendre_int (N : ℕ) :
    ((p : ℤ) - 1) * (padicValNat p N.factorial : ℕ) = N - ((Nat.digits p N).sum : ℕ) := by
  have h := legendre p N
  have hle := Nat.digit_sum_le p N
  have hp1 : 1 ≤ p := hp.out.one_le
  have h' : (((p - 1) * padicValNat p N.factorial : ℕ) : ℤ) = ((N - (Nat.digits p N).sum : ℕ) : ℤ) := by
    rw [h]
  rw [Nat.cast_mul, Nat.cast_sub hp1, Nat.cast_sub hle, Nat.cast_one] at h'
  exact h'

/-- [proved-standard] At a prime radix the summed valuations are the valuation of the factorial. -/
theorem sum_valuation_eq_factorial (N : ℕ) :
    ∑ k ∈ Finset.Icc 1 N, padicValNat p k = padicValNat p N.factorial := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      padicValNat.mul (by omega) (Nat.factorial_ne_zero N), add_comm]

/-- [proved-standard] **The valuation of `N!` is the total of the count's carry chain.** -/
theorem legendre_is_total_carry (N : ℕ) (t : ℤ[X])
    (ht : C (N : ℤ) - chain (Nat.digits p N) = boundary (p : ℤ) t) :
    ((padicValNat p N.factorial : ℕ) : ℤ) = t.eval 1 := by
  rw [count_carry_total hp.out.two_le N t ht, ← sum_valuation_eq_factorial p N, Nat.cast_sum]

/-- [proved-standard] **Kummer** (Mathlib's `padicValNat_choose'`): the valuation of `C(n + k, k)` counts the places
`i ≥ 1` that receive a carry when `k` and `n` are added at radix `p`. -/
theorem kummer_carries {n k b : ℕ} (hnb : Nat.log p (n + k) < b) :
    padicValNat p ((n + k).choose k) = {i ∈ Finset.Ico 1 b | p ^ i ≤ k % p ^ i + n % p ^ i}.card :=
  padicValNat_choose' hnb

end Prime

/-- [proved-standard] A carry into a place is zero or one. -/
theorem carry_le_one {b : ℕ} (hb : 1 ≤ b) (k n i : ℕ) : (k % b ^ i + n % b ^ i) / b ^ i ≤ 1 := by
  have hpos : 0 < b ^ i := Nat.pow_pos hb
  have h1 := Nat.mod_lt k hpos
  have h2 := Nat.mod_lt n hpos
  have h3 : k % b ^ i + n % b ^ i < 2 * b ^ i := by omega
  have := (Nat.div_lt_iff_lt_mul hpos).mpr h3
  omega

/-- [proved-standard] A place receives a carry exactly when the low parts overflow it. -/
theorem carry_eq_one_iff {b : ℕ} (hb : 1 ≤ b) (k n i : ℕ) :
    (k % b ^ i + n % b ^ i) / b ^ i = 1 ↔ b ^ i ≤ k % b ^ i + n % b ^ i := by
  have hpos : 0 < b ^ i := Nat.pow_pos hb
  have hle := carry_le_one hb k n i
  constructor
  · intro h
    by_contra hlt
    rw [Nat.div_eq_of_lt (not_le.mp hlt)] at h
    omega
  · intro h
    have : 1 ≤ (k % b ^ i + n % b ^ i) / b ^ i := (Nat.one_le_div_iff hpos).mpr h
    omega

/-- [proved-standard] **Kummer as a sum of carries**: the valuation of `C(n + k, k)` is the sum of the carries into the
places `1 ≤ i < b`. -/
theorem kummer_sum_of_carries (p : ℕ) [hp : Fact p.Prime] {n k b : ℕ} (hnb : Nat.log p (n + k) < b) :
    padicValNat p ((n + k).choose k) = ∑ i ∈ Finset.Ico 1 b, (k % p ^ i + n % p ^ i) / p ^ i := by
  rw [kummer_carries p hnb, Finset.card_filter]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 := carry_le_one hp.out.one_le k n i
  have h2 := carry_eq_one_iff hp.out.one_le k n i
  split_ifs with h
  · exact (h2.mpr h).symm
  · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h1 with h0 | h1'
    · exact h0.symm
    · exact absurd (h2.mp h1') h

/-- [proved-standard] **The valuation of `C(m + n, m)` is the total of the sum's carry chain**: Kummer joined to the
place complex. -/
theorem kummer_is_total_carry (p : ℕ) [hp : Fact p.Prime] (m n : ℕ) (t : ℤ[X])
    (ht : chain (Nat.digits p m) + chain (Nat.digits p n) - chain (Nat.digits p (m + n)) = boundary (p : ℤ) t) :
    ((padicValNat p ((m + n).choose m) : ℕ) : ℤ) = t.eval 1 := by
  rw [Nat.choose_symm_add]
  have hdef := digit_sum_defect p m n t ht
  have hfac := Nat.add_choose_mul_factorial_mul_factorial m n
  have hc : (m + n).choose n ≠ 0 := (Nat.choose_pos (Nat.le_add_left n m)).ne'
  have hv : padicValNat p (m + n).factorial =
      padicValNat p ((m + n).choose n) + padicValNat p m.factorial + padicValNat p n.factorial := by
    rw [← hfac, padicValNat.mul (mul_ne_zero hc (Nat.factorial_ne_zero m)) (Nat.factorial_ne_zero n),
      padicValNat.mul hc (Nat.factorial_ne_zero m)]
  have h1 := legendre_int p (m + n)
  have h2 := legendre_int p m
  have h3 := legendre_int p n
  rw [hv] at h1
  have hne : (p : ℤ) - 1 ≠ 0 := by
    have : (2 : ℤ) ≤ p := by exact_mod_cast hp.out.two_le
    omega
  apply mul_left_cancel₀ hne
  simp only [Nat.cast_add] at h1
  linear_combination h1 - h2 - h3 + hdef

/-- [proved-standard] **Lucas on the digits** (Mathlib's `Choose.choose_modEq_prod_range_choose_nat`): at a prime radix
`C(n, k) ≡ ∏_i C(n_i, k_i) (mod p)`, the digits read from `Nat.digits`. -/
theorem lucas_digits (p : ℕ) [hp : Fact p.Prime] {n k a : ℕ} (hn : n < p ^ a) (hk : k < p ^ a) :
    n.choose k ≡
      ∏ i ∈ Finset.range a, ((Nat.digits p n).getD i 0).choose ((Nat.digits p k).getD i 0) [MOD p] := by
  simp_rw [Nat.getD_digits _ _ hp.out.two_le]
  exact Choose.choose_modEq_prod_range_choose_nat hn hk

/-- [proved-standard] At radix ten the summed valuations to five are zero and the valuation of `5!` is one: Legendre's
reading is a prime radix's. -/
theorem composite_radix_differs :
    ∑ k ∈ Finset.Icc 1 5, padicValNat 10 k = 0 ∧ padicValNat 10 (Nat.factorial 5) = 1 := by
  constructor
  · apply Finset.sum_eq_zero
    intro k hk
    rw [Finset.mem_Icc] at hk
    apply padicValNat.eq_zero_of_not_dvd
    omega
  · have h5 : Nat.factorial 5 = 10 * 12 := by decide
    rw [h5, padicValNat_base_mul (by norm_num) (by norm_num), padicValNat.eq_zero_of_not_dvd (by norm_num)]

/-- [proved-standard] Lucas's one-place step fails at radix four: `C(4, 2) = 6` against `C(0, 2)·C(1, 0) = 0`. -/
theorem lucas_fails_at_four :
    ¬ (Nat.choose 4 2 ≡ (4 % 4).choose (2 % 4) * (4 / 4).choose (2 / 4) [MOD 4]) := by
  decide

/-! ## 5. Inversion: the residual squares -/

section Newton

variable {S : Type*} [Ring S]

/-- [proved-standard] **The Newton residual square** in any ring: `1 − A·X(2 − AX) = (1 − AX)²`. -/
theorem newton_residual_square (A X : S) : 1 - A * (X * (2 - A * X)) = (1 - A * X) ^ 2 := by
  noncomm_ring

/-- [proved-standard] The step in its carried form: `X(2 − AX) = X(1 + E)` with `E = 1 − AX`. -/
theorem newton_step_carried (A X : S) : X * (2 - A * X) = X * (1 + (1 - A * X)) := by
  noncomm_ring

/-- [proved-standard] **The carried form**: with `E = 1 − AX` and `X′ = X(1 + E)`, `1 − AX′ = E²`, so a step's two
products need no recomputed residual. -/
theorem newton_carried (A X : S) : 1 - A * (X * (1 + (1 - A * X))) = (1 - A * X) ^ 2 := by
  noncomm_ring

/-- [proved-standard] After `k` steps the residual is the `2^k`-th power of the first. -/
theorem newton_iterate (A X : S) (k : ℕ) :
    1 - A * ((fun Y => Y * (2 - A * Y))^[k] X) = (1 - A * X) ^ 2 ^ k := by
  induction k generalizing X with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih, newton_residual_square, ← pow_mul, pow_succ, mul_comm]

/-- [proved-standard] **The released top end**: with `r` the released value less the unreleased one,
`1 − A(X(2 − AX) + r) = E² − A·r`. -/
theorem newton_released (A X r : S) : 1 - A * (X * (2 - A * X) + r) = (1 - A * X) ^ 2 - A * r := by
  noncomm_ring

end Newton

/-- [proved-standard] **The bottom end doubles the places that agree**: if `m` divides the residual `1 − ax` then `m²`
divides the next one. -/
theorem newton_bottom_end {T : Type*} [CommRing T] (a x m : T) (h : m ∣ 1 - a * x) :
    m ^ 2 ∣ 1 - a * (x * (2 - a * x)) := by
  rw [newton_residual_square]
  exact pow_dvd_pow_of_dvd h 2

/-! ## 6. A width is a need -/

/-- [proved-standard] **A sum of two needs the wider plus one.** -/
theorem sum_width {a b wa wb : ℕ} (ha : a < 2 ^ wa) (hb : b < 2 ^ wb) : a + b < 2 ^ (max wa wb + 1) := by
  have h1 : 2 ^ wa ≤ 2 ^ max wa wb := Nat.pow_le_pow_right (by norm_num) (le_max_left _ _)
  have h2 : 2 ^ wb ≤ 2 ^ max wa wb := Nat.pow_le_pow_right (by norm_num) (le_max_right _ _)
  rw [pow_succ]
  omega

/-- [proved-standard] The place is needed: two full operands of `w ≥ 1` places pass `w` places. -/
theorem sum_width_needed {w : ℕ} (hw : 1 ≤ w) : ¬ ((2 ^ w - 1) + (2 ^ w - 1) < 2 ^ w) := by
  have h : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) hw
  omega

/-- [proved-standard] **A sum of `n` terms needs the widest plus `⌈log₂ n⌉`.** -/
theorem sum_n_width {ι : Type*} (s : Finset ι) (f : ι → ℕ) (w : ℕ) (hf : ∀ i ∈ s, f i < 2 ^ w) :
    ∑ i ∈ s, f i < 2 ^ (w + Nat.clog 2 s.card) := by
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  · have h1 : ∑ i ∈ s, f i < ∑ _i ∈ s, 2 ^ w := Finset.sum_lt_sum_of_nonempty hs hf
    rw [Finset.sum_const, smul_eq_mul] at h1
    have h2 : s.card ≤ 2 ^ Nat.clog 2 s.card := Nat.le_pow_clog (by norm_num) _
    calc ∑ i ∈ s, f i < s.card * 2 ^ w := h1
      _ ≤ 2 ^ Nat.clog 2 s.card * 2 ^ w := Nat.mul_le_mul_right _ h2
      _ = 2 ^ (w + Nat.clog 2 s.card) := by rw [pow_add, mul_comm]

/-- [proved-standard] **A product needs `w_a + w_b`.** -/
theorem product_width {a b wa wb : ℕ} (ha : a < 2 ^ wa) (hb : b < 2 ^ wb) : a * b < 2 ^ (wa + wb) := by
  rw [pow_add]
  exact Nat.mul_lt_mul'' ha hb

/-- The low section of `w` places: `0 ≤ x < 2^w`. -/
def Low (w : ℕ) (x : ℤ) : Prop := 0 ≤ x ∧ x < (2 : ℤ) ^ w

/-- The signed section of `w` places, `−2^(w−1) ≤ x < 2^(w−1)`, written without the half so that no place holds
zero alone: `−2^w ≤ 2x < 2^w`. -/
def Signed (w : ℕ) (x : ℤ) : Prop := -(2 : ℤ) ^ w ≤ 2 * x ∧ 2 * x < (2 : ℤ) ^ w

/-- [proved-standard] The signed section of `w + 1` places is `−2^w ≤ x < 2^w`. -/
theorem signed_succ_iff (w : ℕ) (x : ℤ) : Signed (w + 1) x ↔ -(2 : ℤ) ^ w ≤ x ∧ x < (2 : ℤ) ^ w := by
  unfold Signed
  rw [pow_succ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- [proved-standard] **A low operand of `w` places takes `w + 1` signed places.** -/
theorem low_in_signed {w : ℕ} {x : ℤ} (h : Low w x) : Signed (w + 1) x := by
  rw [signed_succ_iff]
  have hpos : (0 : ℤ) < 2 ^ w := by positivity
  exact ⟨by linarith [h.1], h.2⟩

/-- [proved-standard] **Signed sums need the wider plus one.** -/
theorem signed_add {wa wb : ℕ} {x y : ℤ} (hx : Signed wa x) (hy : Signed wb y) :
    Signed (max wa wb + 1) (x + y) := by
  have h1 : (2 : ℤ) ^ wa ≤ 2 ^ max wa wb := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  have h2 : (2 : ℤ) ^ wb ≤ 2 ^ max wa wb := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
  unfold Signed at *
  rw [pow_succ]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- [proved-standard] **A low operand meeting a signed one needs `max(w_a + 1, w_b) + 1` signed places.** -/
theorem low_add_signed {wa wb : ℕ} {x y : ℤ} (hx : Low wa x) (hy : Signed wb y) :
    Signed (max (wa + 1) wb + 1) (x + y) :=
  signed_add (low_in_signed hx) hy

/-- [proved-standard] The witness of the record: `3 + 1` at two places each needs four signed places. -/
theorem low_add_signed_witness : Low 2 3 ∧ Signed 2 1 ∧ ¬ Signed 3 (3 + 1) ∧ Signed 4 (3 + 1) := by
  unfold Low Signed
  norm_num

/-- [proved-standard] One place fewer when the signed operand has a single place. -/
theorem low_add_single_signed {wa : ℕ} {x y : ℤ} (hx : Low wa x) (hy : Signed 1 y) : Signed (wa + 1) (x + y) := by
  rw [signed_succ_iff]
  have hpos : (1 : ℤ) ≤ 2 ^ wa := one_le_pow₀ (by norm_num)
  unfold Signed at hy
  obtain ⟨hy1, hy2⟩ := hy
  norm_num at hy1 hy2
  constructor <;> linarith [hx.1, hx.2]

/-- [proved-standard] **A difference of two low operands is signed at the wider plus one.** -/
theorem low_sub_low {wa wb : ℕ} {x y : ℤ} (hx : Low wa x) (hy : Low wb y) : Signed (max wa wb + 1) (x - y) := by
  have h1 : (2 : ℤ) ^ wa ≤ 2 ^ max wa wb := pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
  have h2 : (2 : ℤ) ^ wb ≤ 2 ^ max wa wb := pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
  rw [signed_succ_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- [proved-standard] **Low times low is low at `w_a + w_b`.** -/
theorem low_mul_low {wa wb : ℕ} {x y : ℤ} (hx : Low wa x) (hy : Low wb y) : Low (wa + wb) (x * y) := by
  unfold Low at *
  rw [pow_add]
  have hpa : (0 : ℤ) < 2 ^ wa := by positivity
  constructor
  · exact mul_nonneg hx.1 hy.1
  · nlinarith [hx.1, hx.2, hy.1, hy.2]

/-- [proved-standard] **Low times signed is signed at `w_a + w_b`**: the low operand enters at its own places. -/
theorem low_mul_signed {wa wb : ℕ} {x y : ℤ} (hx : Low wa x) (hy : Signed wb y) : Signed (wa + wb) (x * y) := by
  unfold Low Signed at *
  rw [pow_add]
  have hpa : (0 : ℤ) < 2 ^ wa := by positivity
  have hpb : (0 : ℤ) < 2 ^ wb := by positivity
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · nlinarith [mul_nonneg hx1 (sub_nonneg.mpr hy1), mul_nonneg (sub_nonneg.mpr hx2.le) hpb.le]
  · nlinarith [mul_nonneg hx1 (sub_nonneg.mpr hy2.le), mul_pos (sub_pos.mpr hx2) hpb]

/-- [proved-standard] **Signed times signed is signed at `w_a + w_b`.** -/
theorem signed_mul_signed {wa wb : ℕ} {x y : ℤ} (hx : Signed wa x) (hy : Signed wb y) :
    Signed (wa + wb) (x * y) := by
  unfold Signed at *
  rw [pow_add]
  have hpa : (0 : ℤ) < 2 ^ wa := by positivity
  have hpb : (0 : ℤ) < 2 ^ wb := by positivity
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  constructor
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy2.le),
      mul_nonneg (sub_nonneg.mpr hx2.le) (sub_nonneg.mpr hy1), mul_pos hpa hpb]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hx1) (sub_nonneg.mpr hy1),
      mul_nonneg (sub_nonneg.mpr hx2.le) (sub_nonneg.mpr hy2.le), mul_pos hpa hpb]

end Holonics.Mathematics.PlaceComplex
