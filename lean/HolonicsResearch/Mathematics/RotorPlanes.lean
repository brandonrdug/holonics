import HolonicsResearch.Mathematics.OnePlaneRing
import HolonicsResearch.Mathematics.RotorStep
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The rotor's planes: a prime ring needs `|⟨b, −1⟩|` real dimensions, and the rotor has them

The record `research/records/2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`
(§7(c) and (d)) reads one digit of radix `b` as the move `x ↦ b x + d` on a ring `ℤ/q`
(`Mathematics/BaseAction.digitMove`) and owes to #410 the rotor's plane count as a lower bound,
with the rotor attaining it. `Mathematics/OnePlaneRing` settles one plane; this file settles any
number of them for a prime ring.

[proved-derived; formal-checked] What is proved.

1. **The bound** (`colour`, `cx`, `colour_digit`, `rotor_plane_bound`). Let `q` be prime, `b` a
   unit of `ℤ/q`, and let a real space `ℝ^ι` carry the residues as distinct points `p(x)`, with the
   digits `0` and `1` acting by real-affine maps. Then `dim ℝ^ι ≥ |⟨b, −1⟩|` in `(ℤ/q)ˣ`. The proof
   reads the points through their colours `Q(k) = 𝓕p(k) ∈ ℂ^ι`. The complexified linear part of
   digit `0` carries `Q(k)` to `Q(b⁻¹k)`, so with `o = ord(b)` the composite of `o − 1` zeros and one
   `1` has every `Q(j)` (`j ≠ 0`) as an eigenvector of eigenvalue `ψ(j)`. Distinct eigenvalues give
   linearly independent colours. The present colours are closed under `×b` (digit `0`) and `×(−1)`
   (reality, `colour_neg`), and some colour `k ≠ 0` is present because the points are distinct, so
   the orbit `⟨b, −1⟩·k` gives `|⟨b, −1⟩|` independent vectors.
2. **The count** (`card_closure_neg_one`). For `q` an odd prime, `|⟨b, −1⟩| = ord(b)` when the order
   is even (then `b^(ord/2) = −1`) and `2·ord(b)` when it is odd. So the rotor needs `ord(b)/2`
   planes for even order and `ord(b)` for odd.
3. **The rotor attains it** (`cas`, `hartley`, `hartley_injective`, `hartley_digit`). Take one real
   coordinate `cas(u x) = Re ψ(u x) + Im ψ(u x)` for each `u` in a subgroup `H ∋ b, −1`. The digit
   `d` is the linear map `v_u ↦ Re ψ(u d)·v_(ub) + Im ψ(u d)·v_(−ub)`: this is
   `χ_a(b x + d) = ψ(a d) χ_(ba)(x)` in real coordinates, mode `a` taking the old mode `ba` and
   turning by `a·d`. The coordinates `u = ±1` recover `ψ(x)`, so the points are distinct.
4. **The least dimension** (`rotor_planes`, `rotor_planes_count`). The two halves make
   `|⟨b, −1⟩|` the least real dimension, stated over `Fin n`.
5. **Base ten** (`card_ten`, `rotor_planes_ten`). The primes `3, 7, 11, 13, 17, 37, 41, 73, 101`
   need `1, 3, 1, 3, 8, 3, 5, 4, 2` planes.
6. **The chain of `k` modes** (`wordValue`, `chain_modes`, `chain_reads_last_digits`). On
   `ℤ/bᵏ` the keyed rotor `Mathematics/RotorStep.keyedStep` with modes `1, b, b², …`, read from
   rest, holds `ψ(bʲ n)` at mode `j`, and every mode from `k` on is the constant `1`: the chain
   `mode 1 ← mode b ← … ← mode bᵏ⁻¹ ← constant`. Mode `0` of two words agrees exactly when their
   numbers agree modulo `bᵏ`, so the chain holds the last `k` digits.

Not proved here: rings that are not prime (the record's `9` and `1001`), where `(ℤ/m)ˣ` need not be
cyclic and the colours split by divisor; the uncoupled bank's dihedral bound (§7(b)) is a separate
#410 box.

Consumers: the atlas row `radix.rotor-planes`.
-/

open Complex ZMod Finset
open scoped ComplexConjugate

namespace Holonics.Mathematics.RotorPlanes

section Colours

variable {q : ℕ} [NeZero q] {E : Type*} [AddCommGroup E] [Module ℂ E]

/-- [proved-standard; formal-checked] A complex-linear map commutes with the colours. -/
theorem dft_map {F : Type*} [AddCommGroup F] [Module ℂ F] (L : E →ₗ[ℂ] F) (Φ : ZMod q → E)
    (k : ZMod q) : 𝓕 (fun x => L (Φ x)) k = L (𝓕 Φ k) := by
  simp only [dft_apply, map_sum, _root_.map_smul]

end Colours

section Real

variable {q : ℕ} [NeZero q] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The colours of a real configuration `p : ℤ/q → ℝ^ι`, vectors of `ℂ^ι`. -/
noncomputable def colour (p : ZMod q → ι → ℝ) : ZMod q → ι → ℂ :=
  𝓕 (fun x i => (p x i : ℂ))

/-- The complexification of a real linear map. -/
noncomputable def cx (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  Matrix.toLin' ((LinearMap.toMatrix' L).map (fun r : ℝ => (r : ℂ)))

/-- [proved-standard; formal-checked] The complexification agrees with the map on real vectors. -/
theorem cx_apply (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ)) (v : ι → ℝ) :
    cx L (fun i => (v i : ℂ)) = fun i => ((L v) i : ℂ) := by
  ext i
  rw [cx, Matrix.toLin'_apply, ← LinearMap.toMatrix'_mulVec L v]
  have := RingHom.map_mulVec Complex.ofRealHom (LinearMap.toMatrix' L) v i
  exact this.symm

omit [Fintype ι] [DecidableEq ι] in
/-- [proved-standard; formal-checked] Reality: colour `−k` is the conjugate of colour `k`. -/
theorem colour_neg (p : ZMod q → ι → ℝ) (k : ZMod q) :
    colour p (-k) = fun i => conj (colour p k i) := by
  ext i
  simp only [colour, dft_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    Complex.conj_ofReal]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [← AddChar.map_neg_eq_conj]
  congr 2
  ring

/-- [proved-derived; formal-checked] **A digit acting by a real-affine map, read on the colours.**
If `p(b x + e) = L p(x) + c`, then for `k ≠ 0` the complexified `L` carries colour `k` to colour
`b⁻¹k`, turned by `ψ(e b⁻¹ k)`. -/
theorem colour_digit (p : ZMod q → ι → ℝ) (b : (ZMod q)ˣ) (L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))
    (c : ι → ℝ) (e : ZMod q) (h : ∀ x, p ((b : ZMod q) * x + e) = L (p x) + c) {k : ZMod q}
    (hk : k ≠ 0) :
    stdAddChar (e * (b⁻¹.val * k)) • colour p (b⁻¹.val * k) = cx L (colour p k) := by
  set P : ZMod q → ι → ℂ := fun x i => (p x i : ℂ)
  have h1 : 𝓕 (fun x => P ((b : ZMod q) * x + e)) k =
      stdAddChar (e * (b⁻¹.val * k)) • 𝓕 P (b⁻¹.val * k) := by
    have := dft_comp_unitMul (fun y => P (y + e)) b k
    rw [this, OnePlaneRing.dft_comp_add]
  have h2 : (fun x => P ((b : ZMod q) * x + e)) =
      fun x => cx L (P x) + fun i => (c i : ℂ) := by
    funext x
    rw [cx_apply]
    funext i
    simp [P, h x]
  have h3 : 𝓕 (fun x => P ((b : ZMod q) * x + e)) k = cx L (𝓕 P k) := by
    rw [h2]
    have := OnePlaneRing.dft_const (E := ι → ℂ) (fun i => (c i : ℂ)) hk
    rw [show (fun x => cx L (P x) + fun i => (c i : ℂ)) =
        (fun x => cx L (P x)) + (fun _ => fun i => (c i : ℂ)) from rfl, map_add, Pi.add_apply,
      dft_map, this, add_zero]
  change stdAddChar (e * (b⁻¹.val * k)) • 𝓕 P (b⁻¹.val * k) = cx L (𝓕 P k)
  rw [← h1, h3]

omit [Fintype ι] [DecidableEq ι] in
/-- [proved-standard; formal-checked] If every colour present is annihilated by `t`, the real
points repeat with period `t`. -/
theorem real_period (p : ZMod q → ι → ℝ) (t : ZMod q) (h : ∀ k, colour p k ≠ 0 → k * t = 0)
    (x : ZMod q) : p (x + t) = p x := by
  have hP := OnePlaneRing.period (fun x i => (p x i : ℂ)) t h x
  funext i
  have := congrFun hP i
  exact_mod_cast this

end Real

section Bound

variable {q : ℕ} [Fact q.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- [proved-derived; formal-checked] **The rotor's plane bound.** A real realization of the prime
ring `ℤ/q` as distinct points of `ℝ^ι`, with the digits `0` and `1` of the unit base `b` acting by
real-affine maps, has `dim ℝ^ι ≥ |⟨b, −1⟩|`. -/
theorem rotor_plane_bound (b : (ZMod q)ˣ) (p : ZMod q → ι → ℝ) (hp : Function.Injective p)
    (hA : ∀ e : ZMod q, e = 0 ∨ e = 1 →
      ∃ L : (ι → ℝ) →ₗ[ℝ] (ι → ℝ), ∃ c : ι → ℝ, ∀ x, p ((b : ZMod q) * x + e) = L (p x) + c) :
    Nat.card (Subgroup.closure ({b, -1} : Set (ZMod q)ˣ)) ≤ Fintype.card ι := by
  classical
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  obtain ⟨L0, c0, h0⟩ := hA 0 (Or.inl rfl)
  obtain ⟨L1, c1, h1⟩ := hA 1 (Or.inr rfl)
  set Q := colour p with hQ
  set c : ZMod q := b⁻¹.val with hc
  have hbc : (b : ZMod q) * c = 1 := b.mul_inv
  have hcu : c ≠ 0 := (b⁻¹).ne_zero
  have hc0 : ∀ j : ZMod q, j ≠ 0 → c * j ≠ 0 := fun j hj => mul_ne_zero hcu hj
  have hN0 : ∀ j, j ≠ 0 → cx L0 (Q j) = Q (c * j) := by
    intro j hj
    have := colour_digit p b L0 c0 0 h0 hj
    rw [zero_mul, AddChar.map_zero_eq_one, one_smul] at this
    exact this.symm
  have hN1 : ∀ j, j ≠ 0 → cx L1 (Q j) = stdAddChar (c * j) • Q (c * j) := by
    intro j hj
    have := colour_digit p b L1 c1 1 h1 hj
    rw [one_mul] at this
    exact this.symm
  have hcpow : ∀ n : ℕ, ∀ j : ZMod q, j ≠ 0 → c ^ n * j ≠ 0 :=
    fun n j hj => mul_ne_zero (pow_ne_zero n hcu) hj
  have hpow : ∀ n : ℕ, ∀ j, j ≠ 0 → (cx L0 ^ n) (Q j) = Q (c ^ n * j) := by
    intro n
    induction n with
    | zero => intro j hj; simp
    | succ n ih =>
      intro j hj
      rw [pow_succ, Module.End.mul_apply, hN0 j hj, ih _ (hc0 j hj), pow_succ, mul_assoc]
  set o := orderOf b with ho_def
  have ho : 0 < o := orderOf_pos b
  have hco : c ^ o = 1 := by
    rw [hc, ← Units.val_pow_eq_pow_val, inv_pow, pow_orderOf_eq_one, inv_one, Units.val_one]
  -- the digits compose into a map with every colour `j ≠ 0` an eigenvector of eigenvalue `ψ(j)`
  set f := cx L1 * cx L0 ^ (o - 1) with hf_def
  have hf : ∀ j, j ≠ 0 → f (Q j) = stdAddChar j • Q j := by
    intro j hj
    rw [hf_def, Module.End.mul_apply, hpow _ j hj, hN1 _ (hcpow _ j hj), ← mul_assoc, ← pow_succ',
      Nat.sub_add_cancel ho, hco, one_mul]
  -- the present colours are closed under `×b⁻¹`, `×b` and `×(−1)`
  have hcl : ∀ j, j ≠ 0 → Q j ≠ 0 → Q (c * j) ≠ 0 := by
    intro j hj hq hz
    have hfix : (cx L0 ^ o) (Q j) = Q j := by rw [hpow o j hj, hco, one_mul]
    have hzero : (cx L0 ^ o) (Q j) = 0 := by
      rw [← Nat.sub_add_cancel ho, pow_succ, Module.End.mul_apply, hN0 j hj, hz, map_zero]
    exact hq (hfix.symm.trans hzero)
  have hcln : ∀ n : ℕ, ∀ j, j ≠ 0 → Q j ≠ 0 → Q (c ^ n * j) ≠ 0 := by
    intro n
    induction n with
    | zero => intro j hj hq; simpa using hq
    | succ n ih =>
      intro j hj hq
      rw [pow_succ', mul_assoc]
      exact hcl _ (hcpow n j hj) (ih j hj hq)
  have hb' : (b : ZMod q) = c ^ (o - 1) := by
    calc (b : ZMod q) = b * c ^ o := by rw [hco, mul_one]
      _ = b * (c * c ^ (o - 1)) := by rw [← pow_succ', Nat.sub_add_cancel ho]
      _ = c ^ (o - 1) := by rw [← mul_assoc, hbc, one_mul]
  have hneg : ∀ j, Q j ≠ 0 → Q (-j) ≠ 0 := by
    intro j hq hz
    apply hq
    funext i
    have := congrFun hz i
    rw [hQ, colour_neg] at this
    simpa using this
  set H := Subgroup.closure ({b, -1} : Set (ZMod q)ˣ) with hH_def
  have hH : ∀ u ∈ H, ∀ j, j ≠ 0 → Q j ≠ 0 → Q (u.val * j) ≠ 0 := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · intro j hj hq
        rw [hb']
        exact hcln _ j hj hq
      · intro j hj hq
        simpa using hneg j hq
    | one => intro j hj hq; simpa using hq
    | mul x y _ _ hx hy =>
      intro j hj hq
      rw [Units.val_mul, mul_assoc]
      exact hx _ (mul_ne_zero y.ne_zero hj) (hy j hj hq)
    | inv x _ hx =>
      intro j hj hq
      have hpw : ∀ n : ℕ, Q ((x ^ n).val * j) ≠ 0 := by
        intro n
        induction n with
        | zero => simpa using hq
        | succ n ih =>
          rw [pow_succ', Units.val_mul, mul_assoc]
          exact hx _ (mul_ne_zero (x ^ n).ne_zero hj) ih
      have hinv : x⁻¹ = x ^ (orderOf x - 1) := by
        refine (eq_inv_of_mul_eq_one_left ?_).symm
        rw [← pow_succ, Nat.sub_add_cancel (orderOf_pos x), pow_orderOf_eq_one]
      rw [hinv]
      exact hpw _
  -- the points are distinct, so some colour off `0` is present
  obtain ⟨k0, hk0, hq0⟩ : ∃ k, k ≠ 0 ∧ Q k ≠ 0 := by
    by_contra hno
    push Not at hno
    have hper : ∀ k, colour p k ≠ 0 → k * 1 = 0 := by
      intro k hk
      by_contra hk1
      rw [mul_one] at hk1
      exact hk (hno k hk1)
    have := hp (real_period p 1 hper 0)
    simp at this
  let S := {k : ZMod q // k ≠ 0 ∧ Q k ≠ 0}
  have hli : LinearIndependent ℂ (fun s : S => Q s.1) :=
    Module.End.eigenvectors_linearIndependent' f (fun s : S => stdAddChar s.1)
      (fun s s' h => Subtype.ext (injective_stdAddChar h)) (fun s : S => Q s.1)
      (fun s => Module.End.hasEigenvector_iff.mpr
        ⟨Module.End.mem_eigenspace_iff.mpr (hf s.1 s.2.1), s.2.2⟩)
  have hS : Fintype.card S ≤ Fintype.card ι := by
    have := hli.fintype_card_le_finrank
    simpa using this
  have hHS : Nat.card H ≤ Nat.card S := by
    refine Nat.card_le_card_of_injective
      (fun u => ⟨u.1.val * k0, mul_ne_zero u.1.ne_zero hk0, hH u.1 u.2 k0 hk0 hq0⟩) ?_
    intro u v huv
    have := congrArg Subtype.val huv
    simp only at this
    exact Subtype.ext (Units.ext (mul_right_cancel₀ hk0 this))
  calc Nat.card H ≤ Nat.card S := hHS
    _ = Fintype.card S := Nat.card_eq_fintype_card
    _ ≤ Fintype.card ι := hS

end Bound

section Count

variable {q : ℕ} [Fact q.Prime]

/-- [proved-standard; formal-checked] On an odd prime ring `−1 ≠ 1`. -/
theorem neg_one_ne_one_units (hq : q ≠ 2) : (-1 : (ZMod q)ˣ) ≠ 1 := by
  have : Fact (2 < q) := ⟨lt_of_le_of_ne (Fact.out : q.Prime).two_le (Ne.symm hq)⟩
  intro h
  have := congrArg Units.val h
  rw [Units.val_neg, Units.val_one] at this
  exact ZMod.neg_one_ne_one this

/-- [proved-standard; formal-checked] On an odd prime ring `−1` has order `2`. -/
theorem orderOf_neg_one_units (hq : q ≠ 2) : orderOf (-1 : (ZMod q)ˣ) = 2 :=
  orderOf_eq_prime neg_one_sq (neg_one_ne_one_units hq)

/-- [proved-standard; formal-checked] **The count.** On an odd prime ring, `|⟨b, −1⟩|` is `ord(b)`
when the order is even (then `b^(ord/2) = −1`) and `2·ord(b)` when it is odd. -/
theorem card_closure_neg_one (hq : q ≠ 2) (b : (ZMod q)ˣ) :
    Nat.card (Subgroup.closure ({b, -1} : Set (ZMod q)ˣ)) =
      if Even (orderOf b) then orderOf b else 2 * orderOf b := by
  set o := orderOf b with ho
  have hopos : 0 < o := orderOf_pos b
  split_ifs with he
  · obtain ⟨t, ht⟩ := he
    have htpos : 0 < t := by omega
    have hsq : (b ^ t : ZMod q) * (b ^ t : ZMod q) = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← pow_add, ← ht, ho,
        pow_orderOf_eq_one, Units.val_one]
    have hne : b ^ t ≠ 1 := pow_ne_one_of_lt_orderOf htpos.ne' (by omega)
    have hbt : b ^ t = -1 := by
      rcases mul_self_eq_one_iff.mp hsq with h | h
      · exact absurd (Units.ext (by rw [← Units.val_pow_eq_pow_val] at h; simpa using h)) hne
      · exact Units.ext (by rw [← Units.val_pow_eq_pow_val] at h; simpa using h)
    have : Subgroup.closure ({b, -1} : Set (ZMod q)ˣ) = Subgroup.zpowers b := by
      refine le_antisymm (Subgroup.closure_le _ |>.mpr ?_) (Subgroup.zpowers_le.mpr
        (Subgroup.subset_closure (by simp)))
      intro x hx
      rcases hx with h | h
      · rw [h]; exact Subgroup.mem_zpowers b
      · rw [Set.mem_singleton_iff.mp h, ← hbt]; exact Subgroup.npow_mem_zpowers b t
    rw [this, Nat.card_zpowers]
  · have hodd : Odd o := Nat.not_even_iff_odd.mp he
    have hord : orderOf (-b) = 2 * o := by
      rw [← neg_one_mul, Commute.orderOf_mul_eq_mul_orderOf_of_coprime (Commute.neg_one_left b),
        orderOf_neg_one_units hq]
      rw [orderOf_neg_one_units hq]
      exact Nat.coprime_two_left.mpr hodd
    have hb : (-b) ^ (o + 1) = b := by
      rw [neg_pow, (hodd.add_one).neg_one_pow, one_mul, pow_succ, ho, pow_orderOf_eq_one, one_mul]
    have hn : (-b) ^ o = -1 := by
      rw [neg_pow, hodd.neg_one_pow, ho, pow_orderOf_eq_one, mul_one]
    have : Subgroup.closure ({b, -1} : Set (ZMod q)ˣ) = Subgroup.zpowers (-b) := by
      refine le_antisymm (Subgroup.closure_le _ |>.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
      · intro x hx
        rcases hx with h | h
        · have := Subgroup.npow_mem_zpowers (-b) (o + 1)
          rw [hb] at this
          rw [h]; exact this
        · have := Subgroup.npow_mem_zpowers (-b) o
          rw [hn] at this
          rw [Set.mem_singleton_iff.mp h]; exact this
      · have h1 : (-1 : (ZMod q)ˣ) ∈ Subgroup.closure ({b, -1} : Set (ZMod q)ˣ) :=
          Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
        have h2 : b ∈ Subgroup.closure ({b, -1} : Set (ZMod q)ˣ) :=
          Subgroup.subset_closure (Set.mem_insert _ _)
        have := Subgroup.mul_mem _ h1 h2
        rwa [neg_one_mul] at this
    rw [this, Nat.card_zpowers, hord]

end Count

section Hartley

variable {q : ℕ} [NeZero q]

/-- The Hartley kernel `cas = cos + sin`, read on the phase `ψ(x)`. -/
noncomputable def cas (x : ZMod q) : ℝ := (stdAddChar x).re + (stdAddChar x).im

/-- [proved-standard; formal-checked] `cas(a + y) = Re ψ(a)·cas(y) + Im ψ(a)·cas(−y)`. -/
theorem cas_add (a y : ZMod q) :
    cas (a + y) = (stdAddChar a).re * cas y + (stdAddChar a).im * cas (-y) := by
  simp only [cas, AddChar.map_add_eq_mul, AddChar.map_neg_eq_conj, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im]
  ring

/-- The rotor's real coordinates, one `cas(u x)` for each `u` of `H`. -/
noncomputable def hartley (H : Subgroup (ZMod q)ˣ) (x : ZMod q) : H → ℝ :=
  fun u => cas (u.1.val * x)

/-- [proved-standard; formal-checked] With `−1 ∈ H` the coordinates `u = ±1` recover `ψ(x)`, so
the rotor holds the residues as distinct points. -/
theorem hartley_injective (H : Subgroup (ZMod q)ˣ) (hn : -1 ∈ H) :
    Function.Injective (hartley H) := by
  intro x y h
  have h1 := congrFun h ⟨1, H.one_mem⟩
  have h2 := congrFun h ⟨-1, hn⟩
  simp only [hartley, Units.val_one, one_mul, Units.val_neg, neg_one_mul, cas] at h1 h2
  rw [AddChar.map_neg_eq_conj, AddChar.map_neg_eq_conj] at h2
  simp only [Complex.conj_re, Complex.conj_im] at h2
  apply injective_stdAddChar
  apply Complex.ext <;> linarith

/-- [proved-derived; formal-checked] **The rotor attains the bound.** With `b, −1 ∈ H`, the digit
`d` acts on the rotor's coordinates by the linear map
`v_u ↦ Re ψ(u d)·v_(ub) + Im ψ(u d)·v_(−ub)`: mode `u` takes the old modes `±ub` and turns by
`u·d`, which is `χ_u(b x + d) = ψ(u d) χ_(ub)(x)` in real coordinates. -/
theorem hartley_digit (H : Subgroup (ZMod q)ˣ) (b : (ZMod q)ˣ) (hb : b ∈ H) (hn : -1 ∈ H)
    (d : ZMod q) : ∃ L : (H → ℝ) →ₗ[ℝ] (H → ℝ),
      ∀ x, hartley H ((b : ZMod q) * x + d) = L (hartley H x) := by
  refine ⟨LinearMap.pi fun u : H =>
      (stdAddChar (u.1.val * d)).re •
        LinearMap.proj (R := ℝ) (φ := fun _ : H => ℝ) ⟨u.1 * b, H.mul_mem u.2 hb⟩ +
      (stdAddChar (u.1.val * d)).im •
        LinearMap.proj (R := ℝ) (φ := fun _ : H => ℝ)
          ⟨-1 * (u.1 * b), H.mul_mem hn (H.mul_mem u.2 hb)⟩, fun x => ?_⟩
  funext u
  simp only [LinearMap.pi_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.proj_apply,
    smul_eq_mul, hartley, Units.val_mul, Units.val_neg, Units.val_one]
  rw [show u.1.val * ((b : ZMod q) * x + d) = u.1.val * d + u.1.val * b * x by ring, cas_add]
  congr 3
  ring

end Hartley

section Least

variable {q : ℕ} [Fact q.Prime]

/-- [proved-derived; formal-checked] **The rotor's planes.** The least real dimension holding the
prime ring `ℤ/q` as distinct points, with every digit `x ↦ b x + d` an affine map, is
`|⟨b, −1⟩|`. -/
theorem rotor_planes (b : (ZMod q)ˣ) :
    IsLeast {n : ℕ | ∃ p : ZMod q → (Fin n → ℝ), Function.Injective p ∧
      ∀ d : ZMod q, ∃ L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ), ∃ c : Fin n → ℝ,
        ∀ x, p ((b : ZMod q) * x + d) = L (p x) + c}
      (Nat.card (Subgroup.closure ({b, -1} : Set (ZMod q)ˣ))) := by
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  set H := Subgroup.closure ({b, -1} : Set (ZMod q)ˣ)
  have hb : b ∈ H := Subgroup.subset_closure (by simp)
  have hn : -1 ∈ H := Subgroup.subset_closure (by simp)
  refine ⟨?_, ?_⟩
  · set e := Finite.equivFin H
    set T := LinearEquiv.funCongrLeft ℝ ℝ e.symm
    refine ⟨fun x => T (hartley H x), fun x y h => hartley_injective H hn (T.injective h),
      fun d => ?_⟩
    obtain ⟨L, hL⟩ := hartley_digit H b hb hn d
    exact ⟨T.toLinearMap ∘ₗ L ∘ₗ T.symm.toLinearMap, 0, fun x => by simp [hL]⟩
  · rintro n ⟨p, hp, hd⟩
    have := rotor_plane_bound b p hp (fun e _ => hd e)
    simpa using this

/-- [proved-derived; formal-checked] **The planes counted.** On an odd prime ring the least real
dimension is `ord(b)` for even order (`ord(b)/2` planes) and `2·ord(b)` for odd (`ord(b)` planes). -/
theorem rotor_planes_count (hq : q ≠ 2) (b : (ZMod q)ˣ) :
    IsLeast {n : ℕ | ∃ p : ZMod q → (Fin n → ℝ), Function.Injective p ∧
      ∀ d : ZMod q, ∃ L : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ), ∃ c : Fin n → ℝ,
        ∀ x, p ((b : ZMod q) * x + d) = L (p x) + c}
      (if Even (orderOf b) then orderOf b else 2 * orderOf b) := by
  rw [← card_closure_neg_one hq]
  exact rotor_planes b

end Least

section Ten

/-- [proved-standard; formal-checked] The count from the order read off `bⁿ = 1` and `bᵐ ≠ 1` for
`0 < m < n`. -/
theorem card_closure_of_order {q : ℕ} [Fact q.Prime] (hq : q ≠ 2) (b : (ZMod q)ˣ) {n : ℕ}
    (hn : 0 < n) (h1 : (b : ZMod q) ^ n = 1) (h2 : ∀ m < n, 0 < m → (b : ZMod q) ^ m ≠ 1) :
    Nat.card (Subgroup.closure ({b, -1} : Set (ZMod q)ˣ)) = if Even n then n else 2 * n := by
  have : orderOf b = n := by
    rw [orderOf_eq_iff hn]
    refine ⟨Units.ext (by simpa using h1), fun m hm hm0 h => h2 m hm hm0 ?_⟩
    simpa using congrArg Units.val h
  rw [card_closure_neg_one hq, this]

/-- [proved-standard; formal-checked] The count for the base `10`. -/
theorem card_ten (p n : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hcop : Nat.Coprime 10 p) (hn : 0 < n)
    (h1 : ((10 : ℕ) : ZMod p) ^ n = 1) (h2 : ∀ m < n, 0 < m → ((10 : ℕ) : ZMod p) ^ m ≠ 1) :
    Nat.card (Subgroup.closure ({ZMod.unitOfCoprime 10 hcop, -1} : Set (ZMod p)ˣ)) =
      if Even n then n else 2 * n := by
  have : Fact p.Prime := ⟨hp⟩
  exact card_closure_of_order hp2 _ hn (by rw [ZMod.coe_unitOfCoprime]; exact h1)
    (by rw [ZMod.coe_unitOfCoprime]; exact h2)

/-- [proved-derived; formal-checked] **Base ten:** the least real dimension `2 · planes` for the
primes `3, 7, 11, 13, 17, 37, 41, 73, 101`; the planes are `1, 3, 1, 3, 8, 3, 5, 4, 2`. -/
theorem rotor_planes_ten :
    Nat.card (Subgroup.closure
      ({ZMod.unitOfCoprime 10 (by norm_num : Nat.Coprime 10 3), -1} : Set (ZMod 3)ˣ)) = 2 * 1 ∧
    Nat.card (Subgroup.closure
      ({ZMod.unitOfCoprime 10 (by norm_num : Nat.Coprime 10 7), -1} : Set (ZMod 7)ˣ)) = 2 * 3 ∧
    Nat.card (Subgroup.closure
      ({ZMod.unitOfCoprime 10 (by norm_num : Nat.Coprime 10 11), -1} : Set (ZMod 11)ˣ)) = 2 * 1 ∧
    Nat.card (Subgroup.closure
      ({ZMod.unitOfCoprime 10 (by norm_num : Nat.Coprime 10 13), -1} : Set (ZMod 13)ˣ)) = 2 * 3 ∧
    Nat.card (Subgroup.closure
      ({ZMod.unitOfCoprime 10 (by norm_num : Nat.Coprime 10 17), -1} : Set (ZMod 17)ˣ)) = 2 * 8 ∧
    Nat.card (Subgroup.closure
      ({ZMod.unitOfCoprime 10 (by norm_num : Nat.Coprime 10 37), -1} : Set (ZMod 37)ˣ)) = 2 * 3 ∧
    Nat.card (Subgroup.closure
      ({ZMod.unitOfCoprime 10 (by norm_num : Nat.Coprime 10 41), -1} : Set (ZMod 41)ˣ)) = 2 * 5 ∧
    Nat.card (Subgroup.closure
      ({ZMod.unitOfCoprime 10 (by norm_num : Nat.Coprime 10 73), -1} : Set (ZMod 73)ˣ)) = 2 * 4 ∧
    Nat.card (Subgroup.closure
      ({ZMod.unitOfCoprime 10 (by norm_num : Nat.Coprime 10 101), -1} : Set (ZMod 101)ˣ)) =
        2 * 2 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [card_ten 3 1 (by norm_num) (by norm_num) _ (by norm_num) (by decide) (by decide)]
    decide
  · rw [card_ten 7 6 (by norm_num) (by norm_num) _ (by norm_num) (by decide) (by decide)]
    decide
  · rw [card_ten 11 2 (by norm_num) (by norm_num) _ (by norm_num) (by decide) (by decide)]
    decide
  · rw [card_ten 13 6 (by norm_num) (by norm_num) _ (by norm_num) (by decide) (by decide)]
    decide
  · rw [card_ten 17 16 (by norm_num) (by norm_num) _ (by norm_num) (by decide) (by decide)]
    decide
  · rw [card_ten 37 3 (by norm_num) (by norm_num) _ (by norm_num) (by decide) (by decide)]
    decide
  · rw [card_ten 41 5 (by norm_num) (by norm_num) _ (by norm_num) (by decide) (by decide)]
    decide
  · rw [card_ten 73 8 (by norm_num) (by norm_num) _ (by norm_num) (by decide) (by decide)]
    decide
  · rw [card_ten 101 4 (by norm_num) (by norm_num) _ (by norm_num) (by decide) (by decide)]
    decide

end Ten

section Chain

open Holonics.Mathematics.BaseAction Holonics.Mathematics.RotorStep

/-- The number of a word of digits in base `b`, most significant digit first. -/
def wordValue (b : ℕ) (ds : List ℕ) : ℕ := ds.foldl (fun y d => b * y + d) 0

/-- [proved-standard; formal-checked] The number's residue is the digit moves' fold. -/
theorem cast_foldl {R : Type*} [CommRing R] (b : ℕ) (ds : List ℕ) (n : ℕ) :
    ((ds.foldl (fun y d => b * y + d) n : ℕ) : R) =
      (ds.map (fun d : ℕ => (d : R))).foldl (fun y d => digitMove (b : R) d y) (n : R) := by
  induction ds generalizing n with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.foldl_cons, List.map_cons]
    rw [ih]
    simp [digitMove]

/-- [proved-derived; formal-checked] **The chain of `k` modes.** On the ring `ℤ/bᵏ`, the keyed
rotor with modes `1, b, b², …` read from rest holds `ψ(bʲ n)` at mode `j` for the word's number
`n`, and every mode from `k` on is the constant `1`: the chain
`mode 1 ← mode b ← … ← mode bᵏ⁻¹ ← constant` has `k` live modes. -/
theorem chain_modes (b k : ℕ) [NeZero b] (ds : List ℕ) :
    (ds.map (fun d : ℕ => (d : ZMod (b ^ k)))).foldl
        (fun h d => keyedStep (stdAddChar : AddChar (ZMod (b ^ k)) ℂ) 1 (b : ZMod (b ^ k)) d h)
        (fun _ => 1) =
      (fun j => stdAddChar ((b : ZMod (b ^ k)) ^ j * (wordValue b ds : ZMod (b ^ k)))) ∧
    ∀ j, k ≤ j → (ds.map (fun d : ℕ => (d : ZMod (b ^ k)))).foldl
        (fun h d => keyedStep (stdAddChar : AddChar (ZMod (b ^ k)) ℂ) 1 (b : ZMod (b ^ k)) d h)
        (fun _ => 1) j = 1 := by
  have hrun := keyed_rotor_from_rest (stdAddChar : AddChar (ZMod (b ^ k)) ℂ) 1
    (b : ZMod (b ^ k)) (ds.map (fun d : ℕ => (d : ZMod (b ^ k))))
  have hval : ((wordValue b ds : ℕ) : ZMod (b ^ k)) =
      (ds.map (fun d : ℕ => (d : ZMod (b ^ k)))).foldl
        (fun y d => digitMove (b : ZMod (b ^ k)) d y) 0 := by
    rw [wordValue, cast_foldl, Nat.cast_zero]
  refine ⟨?_, fun j hj => ?_⟩
  · rw [hrun, hval]
    funext j
    rw [one_mul]
  · rw [hrun]
    beta_reduce
    rw [one_mul, ← hval]
    have : (b : ZMod (b ^ k)) ^ j = 0 := by
      rw [← Nat.sub_add_cancel hj, pow_add, ← Nat.cast_pow b k, ZMod.natCast_self, mul_zero]
    rw [this, zero_mul, AddChar.map_zero_eq_one]

/-- [proved-standard; formal-checked] **The chain holds the last `k` digits:** mode `0` of two
words agrees exactly when their numbers agree modulo `bᵏ`. -/
theorem chain_reads_last_digits (b k : ℕ) [NeZero b] (ds ds' : List ℕ) :
    (stdAddChar ((wordValue b ds : ℕ) : ZMod (b ^ k)) : ℂ) =
        stdAddChar ((wordValue b ds' : ℕ) : ZMod (b ^ k)) ↔
      wordValue b ds % b ^ k = wordValue b ds' % b ^ k := by
  rw [injective_stdAddChar.eq_iff, ZMod.natCast_eq_natCast_iff']

end Chain

end Holonics.Mathematics.RotorPlanes
