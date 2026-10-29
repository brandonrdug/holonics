import Mathlib.Analysis.Fourier.ZMod
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic

/-!
# One plane holds a ring coprime to the base only when the base is `±1`

The record `research/records/2026-10-26_THE_GENERATOR_AND_THE_MODULATOR_ARE_ONE_MOVE_AND_THE_PLACE_DECIDES_WHICH_SO_A_RING_COPRIME_TO_TEN_NEEDS_A_ROTOR.md`
(§7(a) and (d)) reads one digit of radix `b` as the move `x ↦ b x + d` on a ring `ℤ/m`
(`Mathematics/BaseAction.digitMove`) and owes to #410 the one-plane theorem for rings coprime to the
base. This file proves it.

[proved-derived; formal-checked] What is proved.

1. **The digits generate the affine group** (`affinePerm`, `affineGroup`, `closure_digits`,
   `card_affineGroup`). For a unit base `b`, the digit moves (any digit set containing `0` and `1`)
   generate exactly the moves `x ↦ bⁿ x + t`, every translation included, and there are
   `m · ord_m(b)` of them.
2. **The one-plane theorem** (`one_plane_modes`, `one_plane`). Let `m ≥ 3` distinct points of one
   real plane (the plane is `ℂ`; `affine_form` shows every real-affine map of it is
   `z ↦ α z + β z̄ + γ`) carry the residues, and let the digits `0` and `1` act by real-affine maps.
   Then `b ≡ ±1 (mod m)`. The proof reads the points through their colours `𝓕p(k)`: a digit acts
   on the pair `(𝓕p(k), conj 𝓕p(−k))` by one complex `2 × 2` matrix (`lin_pair`), the digits
   compose into a map with the pairs as eigenvectors of eigenvalue `ψ(k)`, so at most two colours
   `±k` are present, and the digit `0` carries colour `k` to `b⁻¹ k`, which must be `±k`.
3. **The points are a turned polygon** (`turned_polygon`). They are the image of the regular
   `m`-gon under an invertible real-affine map, centred on their barycentre, and the translation by
   `1` is a turn of order `m` about it. In particular they are never collinear.
4. **The phase chart** (`phase_chart_affine_iff`). Held as the turn `ψ(x)`, the residue admits the
   digit move as a real-affine map exactly when `b ≡ 1, −1` or `0 (mod m)`.
5. **Base ten** (`one_plane_ten_iff`, `phase_chart_ten_iff`). A ring `m ≥ 3` coprime to ten fits
   one plane exactly when `m ∈ {3, 9, 11}`: the converse of
   `Holonics.Mathematics.RadixWindowReceiver.cheap_faces`. In the phase chart the move is affine
   exactly when `m` divides `9`, `11` or `10`.

Not proved here: the record's routes through the barycentre's finite group of turns and through
eigenvalues of a real turn are replaced by the colours above; the bank of uncoupled planes and the
rotor's plane bound (§7(b), (c)) are separate #410 boxes.

Consumers: the atlas row `radix.one-plane-coprime-rings`.
-/

open Complex ZMod Finset
open scoped ComplexConjugate

namespace Holonics.Mathematics.OnePlaneRing

section Moves

variable {m : ℕ}

/-- The move `x ↦ u x + t` on `ℤ/m`, `u` a unit, as a permutation of the ring. -/
def affinePerm (u : (ZMod m)ˣ) (t : ZMod m) : Equiv.Perm (ZMod m) where
  toFun x := u * x + t
  invFun y := u⁻¹.val * (y - t)
  left_inv x := by simp only [add_sub_cancel_right, ← mul_assoc, Units.inv_mul, one_mul]
  right_inv y := by simp only [← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]

@[simp] theorem affinePerm_apply (u : (ZMod m)ˣ) (t x : ZMod m) :
    affinePerm u t x = u * x + t := rfl

/-- [proved-standard; formal-checked] Moves compose: `(u, t)·(u′, t′) = (u u′, u t′ + t)`. -/
theorem affinePerm_mul (u u' : (ZMod m)ˣ) (t t' : ZMod m) :
    affinePerm u t * affinePerm u' t' = affinePerm (u * u') (u * t' + t) := by
  ext x
  simp only [Equiv.Perm.mul_apply, affinePerm_apply, Units.val_mul]
  ring

/-- [proved-standard; formal-checked] The move `(1, 0)` is the identity. -/
theorem affinePerm_one_zero : affinePerm (1 : (ZMod m)ˣ) 0 = 1 := by
  ext x
  simp

/-- [proved-standard; formal-checked] The inverse move is `x ↦ u⁻¹ x − u⁻¹ t`. -/
theorem affinePerm_inv (u : (ZMod m)ˣ) (t : ZMod m) :
    (affinePerm u t)⁻¹ = affinePerm u⁻¹ (-(u⁻¹.val * t)) := by
  rw [inv_eq_iff_mul_eq_one, affinePerm_mul, mul_inv_cancel, ← affinePerm_one_zero]
  congr 1
  rw [mul_neg, ← mul_assoc, Units.mul_inv, one_mul, neg_add_cancel]

/-- [proved-standard; formal-checked] A move determines its unit and its translation (read it at
`0` and at `1`). -/
theorem affinePerm_injective :
    Function.Injective (fun ut : (ZMod m)ˣ × ZMod m => affinePerm ut.1 ut.2) := by
  rintro ⟨u, t⟩ ⟨u', t'⟩ h
  have h0 := congrArg (fun σ : Equiv.Perm (ZMod m) => σ 0) h
  have h1 := congrArg (fun σ : Equiv.Perm (ZMod m) => σ 1) h
  simp only [affinePerm_apply, mul_zero, zero_add, mul_one] at h0 h1
  subst h0
  exact Prod.ext (Units.ext (add_right_cancel h1)) rfl

/-- The affine group of base `b`: the moves `x ↦ u x + t` with `u` a power of `b`. -/
def affineGroup (b : (ZMod m)ˣ) : Subgroup (Equiv.Perm (ZMod m)) where
  carrier := {σ | ∃ u ∈ Subgroup.zpowers b, ∃ t, σ = affinePerm u t}
  mul_mem' := by
    rintro _ _ ⟨u, hu, t, rfl⟩ ⟨u', hu', t', rfl⟩
    exact ⟨u * u', Subgroup.mul_mem _ hu hu', _, affinePerm_mul u u' t t'⟩
  one_mem' := ⟨1, Subgroup.one_mem _, 0, affinePerm_one_zero.symm⟩
  inv_mem' := by
    rintro _ ⟨u, hu, t, rfl⟩
    exact ⟨u⁻¹, Subgroup.inv_mem _ hu, _, affinePerm_inv u t⟩

/-- Scaling by a unit, as a hom into the permutations of the ring. -/
def scale : (ZMod m)ˣ →* Equiv.Perm (ZMod m) where
  toFun u := affinePerm u 0
  map_one' := affinePerm_one_zero
  map_mul' u u' := by rw [affinePerm_mul, mul_zero, add_zero]

/-- [proved-derived; formal-checked] **The affine group has `m · ord_m(b)` moves**: the moves are
the pairs `(u, t)` with `u ∈ ⟨b⟩`, and a move determines its pair. -/
theorem card_affineGroup (b : (ZMod m)ˣ) : Nat.card (affineGroup b) = m * orderOf b := by
  let e : (Subgroup.zpowers b) × ZMod m ≃ affineGroup b :=
    Equiv.ofBijective (fun ut => ⟨affinePerm ut.1 ut.2, ut.1, ut.1.2, ut.2, rfl⟩)
      ⟨fun ⟨⟨u, hu⟩, t⟩ ⟨⟨u', hu'⟩, t'⟩ h => by
        have := @affinePerm_injective m (u, t) (u', t') (congrArg Subtype.val h)
        simp only [Prod.mk.injEq] at this
        obtain ⟨rfl, rfl⟩ := this
        rfl,
      fun ⟨σ, u, hu, t, hσ⟩ => ⟨(⟨u, hu⟩, t), Subtype.ext hσ.symm⟩⟩
  rw [← Nat.card_congr e, Nat.card_prod, Nat.card_zpowers, Nat.card_zmod, mul_comm]

variable [NeZero m]

/-- [proved-derived; formal-checked] **The digits generate the affine group** (§7(a)). For any
set of digits containing `0` and `1`, the moves `x ↦ b x + d` generate exactly the moves
`x ↦ bⁿ x + t`: the translation by `1` is `(b, 1)·(b, 0)⁻¹`, every translation is a power of it, and
every scaling is a power of `(b, 0)`. -/
theorem closure_digits (b : (ZMod m)ˣ) (D : Set (ZMod m)) (h0 : (0 : ZMod m) ∈ D)
    (h1 : (1 : ZMod m) ∈ D) :
    Subgroup.closure ((fun d => affinePerm b d) '' D) = affineGroup b := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro _ ⟨d, -, rfl⟩
    exact ⟨b, Subgroup.mem_zpowers b, d, rfl⟩
  · rintro _ ⟨u, hu, t, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    set H := Subgroup.closure ((fun d => affinePerm b d) '' D)
    have hb0 : affinePerm b 0 ∈ H := Subgroup.subset_closure ⟨0, h0, rfl⟩
    have hb1 : affinePerm b 1 ∈ H := Subgroup.subset_closure ⟨1, h1, rfl⟩
    have htr : affinePerm 1 1 ∈ H := by
      have : affinePerm 1 1 = affinePerm b 1 * (affinePerm b 0)⁻¹ := by
        rw [affinePerm_inv, affinePerm_mul, mul_inv_cancel]
        simp
      rw [this]
      exact H.mul_mem hb1 (H.inv_mem hb0)
    have htrn : ∀ k : ℕ, affinePerm 1 (k : ZMod m) ∈ H := by
      intro k
      induction k with
      | zero => rw [Nat.cast_zero, affinePerm_one_zero]; exact H.one_mem
      | succ k ih =>
        have : affinePerm 1 ((k + 1 : ℕ) : ZMod m) = affinePerm 1 1 * affinePerm 1 k := by
          rw [affinePerm_mul, mul_one, Units.val_one, one_mul, Nat.cast_succ, add_comm]
        rw [this]
        exact H.mul_mem htr ih
    have hscale : affinePerm (b ^ n) 0 ∈ H := by
      have : affinePerm (b ^ n) 0 = (affinePerm b 0) ^ n := map_zpow scale b n
      rw [this]
      exact H.zpow_mem hb0 n
    have : affinePerm (b ^ n) t = affinePerm 1 (t.val : ZMod m) * affinePerm (b ^ n) 0 := by
      rw [affinePerm_mul, ZMod.natCast_zmod_val]
      simp
    rw [this]
    exact H.mul_mem (htrn _) hscale

/-- [proved-derived; formal-checked] **Base ten** (§7(a)): for `m` coprime to ten, the ten digit
moves `x ↦ 10 x + d` generate the affine group `ℤ/m ⋊ ⟨10⟩`, which has `m · ord_m(10)` moves. -/
theorem digits_ten (hcop : Nat.Coprime 10 m) :
    Subgroup.closure ((fun d => affinePerm (ZMod.unitOfCoprime 10 hcop) d) ''
        ((fun d : ℕ => (d : ZMod m)) '' {d | d < 10})) =
        affineGroup (ZMod.unitOfCoprime 10 hcop) ∧
      Nat.card (affineGroup (ZMod.unitOfCoprime 10 hcop)) =
        m * orderOf (ZMod.unitOfCoprime 10 hcop) :=
  ⟨closure_digits _ _ ⟨0, by norm_num, Nat.cast_zero⟩ ⟨1, by norm_num, Nat.cast_one⟩,
    card_affineGroup _⟩

end Moves

section Plane

variable {m : ℕ} [NeZero m]

/-- [proved-standard; formal-checked] A translation turns every colour:
`𝓕(Φ(· + t))(k) = ψ(t k) 𝓕Φ(k)`. -/
theorem dft_comp_add (Φ : ZMod m → ℂ) (t k : ZMod m) :
    𝓕 (fun x => Φ (x + t)) k = stdAddChar (t * k) * 𝓕 Φ k := by
  simp only [dft_apply, smul_eq_mul, Finset.mul_sum]
  have := Equiv.sum_comp (Equiv.addRight t) (fun i => stdAddChar (-((i - t) * k)) * Φ i)
  simp only [Equiv.coe_addRight, add_sub_cancel_right] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- [proved-standard; formal-checked] The conjugate's colour `k` is the conjugate of colour `−k`. -/
theorem dft_conj (Φ : ZMod m → ℂ) (k : ZMod m) :
    𝓕 (fun x => conj (Φ x)) k = conj (𝓕 Φ (-k)) := by
  simp only [dft_apply, smul_eq_mul, map_sum, map_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← AddChar.map_neg_eq_conj]
  congr 2
  ring

/-- [proved-standard; formal-checked] A constant has no colour off frequency `0`. -/
theorem dft_const (γ : ℂ) {k : ZMod m} (hk : k ≠ 0) :
    𝓕 (fun _ : ZMod m => γ) k = 0 := by
  simp only [dft_apply, smul_eq_mul, ← Finset.sum_mul]
  have h := AddChar.sum_mulShift (-k) (isPrimitive_stdAddChar m)
  simp only [neg_eq_zero, hk, if_false] at h
  rw [show (∑ x : ZMod m, stdAddChar (-(x * k))) = ∑ x : ZMod m, stdAddChar (x * -k) by
    simp only [mul_neg], h]
  simp

/-- [proved-standard; formal-checked] Orthogonality of the characters of `ℤ/m`. -/
theorem char_sum (a : ZMod m) :
    ∑ x : ZMod m, stdAddChar (x * a) = if a = 0 then (m : ℂ) else 0 := by
  rw [AddChar.sum_mulShift a (isPrimitive_stdAddChar m)]
  split_ifs <;> simp

/-- [proved-derived; formal-checked] **A digit acting by a real-affine map, read on the colours.**
If `p(b x + e) = α p(x) + β conj(p(x)) + γ`, then for `k ≠ 0`, colour `c k` (`c = b⁻¹`) turned by
`ψ(e c k)` is `α` times colour `k` plus `β` times the mirror of colour `−k`. -/
theorem dft_digit (p : ZMod m → ℂ) (b : (ZMod m)ˣ) (α β γ : ℂ) (e : ZMod m)
    (h : ∀ x, p ((b : ZMod m) * x + e) = α * p x + β * conj (p x) + γ) {k : ZMod m} (hk : k ≠ 0) :
    stdAddChar (e * (b⁻¹.val * k)) * 𝓕 p (b⁻¹.val * k) = α * 𝓕 p k + β * conj (𝓕 p (-k)) := by
  have h1 : 𝓕 (fun x => p ((b : ZMod m) * x + e)) k =
      stdAddChar (e * (b⁻¹.val * k)) * 𝓕 p (b⁻¹.val * k) := by
    have := dft_comp_unitMul (fun y => p (y + e)) b k
    rw [this, dft_comp_add]
  have h2 : 𝓕 (fun x => p ((b : ZMod m) * x + e)) k = α * 𝓕 p k + β * conj (𝓕 p (-k)) := by
    have e1 : (fun x => p ((b : ZMod m) * x + e)) =
        α • p + β • (fun x => conj (p x)) + (fun _ => γ) := by
      funext x; simp [h x, smul_eq_mul]
    rw [e1, map_add, map_add, _root_.map_smul, _root_.map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, dft_conj, dft_const γ hk, add_zero]
  rw [← h1, h2]

/-- A colour and its mirror: `(𝓕p(k), conj(𝓕p(−k)))`. -/
noncomputable def pair (p : ZMod m → ℂ) (k : ZMod m) : Fin 2 → ℂ :=
  ![𝓕 p k, conj (𝓕 p (-k))]

/-- The complexified linear part of the real-affine map `z ↦ α z + β z̄ + γ`. -/
noncomputable def lin (α β : ℂ) : Module.End ℂ (Fin 2 → ℂ) :=
  Matrix.toLin' !![α, β; conj β, conj α]

/-- [proved-derived; formal-checked] On the pairs the digit is one complex `2 × 2` matrix:
`lin α β (pair k) = ψ(e c k) • pair (c k)` for every `k ≠ 0`. -/
theorem lin_pair (p : ZMod m → ℂ) (b : (ZMod m)ˣ) (α β γ : ℂ) (e : ZMod m)
    (h : ∀ x, p ((b : ZMod m) * x + e) = α * p x + β * conj (p x) + γ) {k : ZMod m} (hk : k ≠ 0) :
    lin α β (pair p k) = stdAddChar (e * (b⁻¹.val * k)) • pair p (b⁻¹.val * k) := by
  have e1 := dft_digit p b α β γ e h hk
  have e2 := dft_digit p b α β γ e h (neg_ne_zero.mpr hk)
  rw [neg_neg] at e2
  have e3 := congrArg conj e2
  simp only [map_mul, map_add, conj_conj, ← AddChar.map_neg_eq_conj] at e3
  ext i
  fin_cases i
  · simp only [lin, pair, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Fin.zero_eta,
      Fin.isValue]
    rw [e1]
  · simp only [lin, pair, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one, Pi.smul_apply, smul_eq_mul, Fin.mk_one,
      Fin.isValue]
    rw [show -(e * (b⁻¹.val * -k)) = e * (b⁻¹.val * k) by ring] at e3
    rw [show -(b⁻¹.val * k) = b⁻¹.val * -k by ring, e3]
    ring

/-- [proved-standard; formal-checked] One map on `ℂ²` has no three eigenvectors with distinct
eigenvalues. -/
theorem no_three_modes (f : Module.End ℂ (Fin 2 → ℂ)) (μ : Fin 3 → ℂ)
    (hμ : Function.Injective μ) (v : Fin 3 → Fin 2 → ℂ) (hv : ∀ i, f.HasEigenvector (μ i) (v i)) :
    False := by
  have hli := Module.End.eigenvectors_linearIndependent' f μ hμ v hv
  have := hli.fintype_card_le_finrank
  simp at this

/-- [proved-standard; formal-checked] If every colour present is annihilated by `t`, the points
repeat with period `t`. -/
theorem period (p : ZMod m → ℂ) (t : ZMod m) (h : ∀ k, 𝓕 p k ≠ 0 → k * t = 0) (x : ZMod m) :
    p (x + t) = p x := by
  have : 𝓕 (fun x => p (x + t)) = 𝓕 p := by
    funext k
    rw [dft_comp_add]
    by_cases hk : 𝓕 p k = 0
    · rw [hk, mul_zero]
    · rw [mul_comm t k, h k hk, AddChar.map_zero_eq_one, one_mul]
  exact congrFun (dft.injective this) x

/-- [proved-derived; formal-checked] **The modes of a one-plane ring.** If `m ≥ 3` distinct points
of the plane carry `ℤ/m` and the digits `0` and `1` act by real-affine maps, then the colours
present are `0`, `k` and `−k` for one `k ≠ −k`; multiplication by `k` is injective; the inverse
base carries `k` to `±k`; and the two colours have different sizes, so the plane is not
collapsed onto a line. The proof: the digit moves compose into a map `f` on `ℂ²` with
`f (pair j) = ψ(j) • pair j`, so at most two colours are present, and the digit `0` permutes the
present colours by `c`. -/
theorem one_plane_modes (hm : 3 ≤ m) (b : (ZMod m)ˣ) (p : ZMod m → ℂ)
    (hp : Function.Injective p)
    (hA : ∀ e : ZMod m, e = 0 ∨ e = 1 →
      ∃ α β γ : ℂ, ∀ x, p ((b : ZMod m) * x + e) = α * p x + β * conj (p x) + γ) :
    ∃ k : ZMod m, 𝓕 p k ≠ 0 ∧ k ≠ -k ∧ (∀ j, 𝓕 p j ≠ 0 → j = 0 ∨ j = k ∨ j = -k) ∧
      (∀ t, k * t = 0 → t = 0) ∧ (b⁻¹.val * k = k ∨ b⁻¹.val * k = -k) ∧
      ‖𝓕 p k‖ ≠ ‖𝓕 p (-k)‖ := by
  obtain ⟨α0, β0, γ0, h0⟩ := hA 0 (Or.inl rfl)
  obtain ⟨α1, β1, γ1, h1⟩ := hA 1 (Or.inr rfl)
  set c : ZMod m := b⁻¹.val with hc
  have hbc : (b : ZMod m) * c = 1 := b.mul_inv
  have hc0 : ∀ j : ZMod m, j ≠ 0 → c * j ≠ 0 := by
    intro j hj hcj
    apply hj
    have := congrArg (fun y => (b : ZMod m) * y) hcj
    simpa [← mul_assoc, hbc] using this
  have hN0 : ∀ j, j ≠ 0 → lin α0 β0 (pair p j) = pair p (c * j) := by
    intro j hj
    have := lin_pair p b α0 β0 γ0 0 h0 hj
    simpa using this
  have hN1 : ∀ j, j ≠ 0 → lin α1 β1 (pair p j) = stdAddChar (c * j) • pair p (c * j) := by
    intro j hj
    have := lin_pair p b α1 β1 γ1 1 h1 hj
    simpa using this
  have hcpow : ∀ n : ℕ, ∀ j : ZMod m, j ≠ 0 → c ^ n * j ≠ 0 := by
    intro n
    induction n with
    | zero => intro j hj; simpa using hj
    | succ n ih => intro j hj; rw [pow_succ, mul_assoc]; exact ih _ (hc0 j hj)
  have hpow : ∀ n : ℕ, ∀ j, j ≠ 0 → (lin α0 β0 ^ n) (pair p j) = pair p (c ^ n * j) := by
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
  set f := lin α1 β1 * lin α0 β0 ^ (o - 1) with hf_def
  have hf : ∀ j, j ≠ 0 → f (pair p j) = stdAddChar j • pair p j := by
    intro j hj
    rw [hf_def, Module.End.mul_apply, hpow _ j hj, hN1 _ (hcpow _ j hj), ← mul_assoc, ← pow_succ',
      Nat.sub_add_cancel ho, hco, one_mul]
  have hpair : ∀ j, 𝓕 p j ≠ 0 → pair p j ≠ 0 := by
    intro j hj hz
    apply hj
    have := congrFun hz 0
    simpa [pair] using this
  have hpair' : ∀ j, 𝓕 p j ≠ 0 → pair p (-j) ≠ 0 := by
    intro j hj hz
    apply hj
    have := congrFun hz 1
    simpa [pair] using this
  have heig : ∀ j, j ≠ 0 → pair p j ≠ 0 → f.HasEigenvector (stdAddChar j) (pair p j) := by
    intro j hj hne
    exact Module.End.hasEigenvector_iff.mpr ⟨Module.End.mem_eigenspace_iff.mpr (hf j hj), hne⟩
  have three : ∀ i j k : ZMod m, i ≠ 0 → j ≠ 0 → k ≠ 0 → i ≠ j → i ≠ k → j ≠ k →
      pair p i ≠ 0 → pair p j ≠ 0 → pair p k ≠ 0 → False := by
    intro i j k hi hj hk hij hik hjk pi pj pk
    refine no_three_modes f (fun t => stdAddChar (![i, j, k] t)) ?_
      (fun t => pair p (![i, j, k] t)) ?_
    · intro a a' haa
      have := injective_stdAddChar haa
      fin_cases a <;> fin_cases a' <;> simp_all
    · intro t
      fin_cases t
      · exact heig i hi pi
      · exact heig j hj pj
      · exact heig k hk pk
  have h2 : (2 : ZMod m) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod m) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at h'
    have := Nat.le_of_dvd two_pos h'
    omega
  obtain ⟨k, hqk, hk2⟩ : ∃ k, 𝓕 p k ≠ 0 ∧ k * 2 ≠ 0 := by
    by_contra hno
    push Not at hno
    have := hp (period p 2 hno 0)
    simp at this
    exact h2 this
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk2
  have hkk : k ≠ -k := by
    intro h
    apply hk2
    rw [mul_two]
    nth_rewrite 2 [h]
    exact add_neg_cancel k
  have hS : ∀ j, 𝓕 p j ≠ 0 → j = 0 ∨ j = k ∨ j = -k := by
    intro j hj
    by_contra hno
    push Not at hno
    exact three j k (-k) hno.1 hk0 (neg_ne_zero.mpr hk0) hno.2.1 hno.2.2 hkk
      (hpair j hj) (hpair k hqk) (hpair' k hqk)
  have hinj : ∀ t, k * t = 0 → t = 0 := by
    intro t ht
    have hper : ∀ j, 𝓕 p j ≠ 0 → j * t = 0 := by
      intro j hj
      rcases hS j hj with rfl | rfl | rfl
      · simp
      · exact ht
      · rw [neg_mul, ht, neg_zero]
    have := hp (period p t hper 0)
    simpa using this
  have hck : pair p (c * k) ≠ 0 := by
    intro hz
    have hfix : (lin α0 β0 ^ o) (pair p k) = pair p k := by rw [hpow o k hk0, hco, one_mul]
    have hzero : (lin α0 β0 ^ o) (pair p k) = 0 := by
      rw [← Nat.sub_add_cancel ho, pow_succ, Module.End.mul_apply, hN0 k hk0, hz, map_zero]
    exact hpair k hqk (hfix.symm.trans hzero)
  have hck' : c * k = k ∨ c * k = -k := by
    have hor : 𝓕 p (c * k) ≠ 0 ∨ 𝓕 p (-(c * k)) ≠ 0 := by
      by_contra hno
      push Not at hno
      apply hck
      ext i
      fin_cases i <;> simp [pair, hno.1, hno.2]
    rcases hor with h | h
    · rcases hS _ h with h' | h' | h'
      · exact absurd h' (hc0 k hk0)
      · exact Or.inl h'
      · exact Or.inr h'
    · rcases hS _ h with h' | h' | h'
      · exact absurd (neg_eq_zero.mp h') (hc0 k hk0)
      · exact Or.inr (by rw [← neg_neg (c * k), h'])
      · exact Or.inl (neg_inj.mp h')
  have hnorm : ‖𝓕 p k‖ ≠ ‖𝓕 p (-k)‖ := by
    intro hn
    have hli := Module.End.eigenvectors_linearIndependent' f (fun t => stdAddChar (![k, -k] t))
      (by
        intro a a' haa
        have := injective_stdAddChar haa
        fin_cases a <;> fin_cases a'
        · rfl
        · exact absurd this hkk
        · exact absurd this.symm hkk
        · rfl)
      (fun t => pair p (![k, -k] t))
      (by
        intro t
        fin_cases t
        · exact heig k hk0 (hpair k hqk)
        · exact heig (-k) (neg_ne_zero.mpr hk0) (hpair' k hqk))
    have hv : (fun t => pair p (![k, -k] t)) = ![pair p k, pair p (-k)] := by
      ext t; fin_cases t <;> rfl
    rw [hv, LinearIndependent.pair_iff] at hli
    have hz := hli (𝓕 p (-k)) (-(𝓕 p k)) (by
      ext i
      fin_cases i
      · simp [pair]; ring
      · simp only [pair, neg_neg, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Fin.mk_one,
          Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero, Pi.zero_apply]
        rw [Complex.mul_conj, neg_mul, Complex.mul_conj, Complex.normSq_eq_norm_sq,
          Complex.normSq_eq_norm_sq, hn, add_neg_cancel])
    exact hqk (neg_eq_zero.mp hz.2)
  exact ⟨k, hqk, hkk, hS, hinj, hck', hnorm⟩

/-- [proved-derived; formal-checked] **The one-plane theorem** (§7(a)). A ring `m ≥ 3` whose
residues are `m` distinct points of one real plane, with the digits `0` and `1` of the unit base
`b` acting by real-affine maps, has `b ≡ ±1 (mod m)`. The translation by `1` turns the polygon of
`turned_polygon` by `ψ(k)`, and conjugation by the digit move turns it by `ψ(b k)`; a turn is
conjugate only to itself and its inverse. -/
theorem one_plane (hm : 3 ≤ m) (b : (ZMod m)ˣ) (p : ZMod m → ℂ) (hp : Function.Injective p)
    (hA : ∀ e : ZMod m, e = 0 ∨ e = 1 →
      ∃ α β γ : ℂ, ∀ x, p ((b : ZMod m) * x + e) = α * p x + β * conj (p x) + γ) :
    (b : ZMod m) = 1 ∨ (b : ZMod m) = -1 := by
  obtain ⟨k, -, -, -, hinj, hck', -⟩ := one_plane_modes hm b p hp hA
  have hbc : (b : ZMod m) * b⁻¹.val = 1 := b.mul_inv
  rcases hck' with h | h
  · left
    have hc1 : b⁻¹.val = 1 :=
      sub_eq_zero.mp (hinj (b⁻¹.val - 1) (by rw [mul_sub, mul_comm, h, mul_one, sub_self]))
    calc (b : ZMod m) = b * b⁻¹.val := by rw [hc1, mul_one]
      _ = 1 := hbc
  · right
    have hc1 : b⁻¹.val = -1 :=
      eq_neg_of_add_eq_zero_left
        (hinj (b⁻¹.val + 1) (by rw [mul_add, mul_comm, h, mul_one, neg_add_cancel]))
    calc (b : ZMod m) = -(b * b⁻¹.val) := by rw [hc1, mul_neg_one, neg_neg]
      _ = -1 := by rw [hbc]

/-- [proved-derived; formal-checked] **The points are a turned polygon about their barycentre.**
Under the hypotheses of `one_plane`, `p x = (barycentre) + A ψ(k x) + B conj(ψ(k x))` with
multiplication by `k` injective and `‖A‖ ≠ ‖B‖`: the points are the image of the regular `m`-gon
under an invertible real-affine map, and the translation by `1` is the turn by `ψ(k)`, of order
`m`, about the barycentre. -/
theorem turned_polygon (hm : 3 ≤ m) (b : (ZMod m)ˣ) (p : ZMod m → ℂ) (hp : Function.Injective p)
    (hA : ∀ e : ZMod m, e = 0 ∨ e = 1 →
      ∃ α β γ : ℂ, ∀ x, p ((b : ZMod m) * x + e) = α * p x + β * conj (p x) + γ) :
    ∃ k : ZMod m, (∀ t, k * t = 0 → t = 0) ∧ ∃ A B : ℂ, ‖A‖ ≠ ‖B‖ ∧
      ∀ x, p x =
        (m : ℂ)⁻¹ * ∑ y, p y + (A * stdAddChar (k * x) + B * conj (stdAddChar (k * x))) := by
  obtain ⟨k, hqk, hkk, hS, hinj, -, hnorm⟩ := one_plane_modes hm b p hp hA
  have hm0 : (m : ℂ)⁻¹ ≠ 0 := inv_ne_zero (Nat.cast_ne_zero.mpr (NeZero.ne m))
  have hk0 : k ≠ 0 := by
    intro h; apply hkk; rw [h, neg_zero]
  refine ⟨k, hinj, (m : ℂ)⁻¹ * 𝓕 p k, (m : ℂ)⁻¹ * 𝓕 p (-k), ?_, fun x => ?_⟩
  · rw [norm_mul, norm_mul]
    intro h
    exact hnorm (mul_left_cancel₀ (norm_ne_zero_iff.mpr hm0) h)
  · have hinv : p x = (m : ℂ)⁻¹ * ∑ j : ZMod m, stdAddChar (j * x) * 𝓕 p j := by
      have := invDFT_apply (𝓕 p) x
      rw [LinearEquiv.symm_apply_apply] at this
      simpa only [smul_eq_mul] using this
    have hsub : ∑ j ∈ ({0, k, -k} : Finset (ZMod m)), stdAddChar (j * x) * 𝓕 p j =
        ∑ j : ZMod m, stdAddChar (j * x) * 𝓕 p j := by
      refine Finset.sum_subset (Finset.subset_univ _) fun j _ hj => ?_
      by_cases hq : 𝓕 p j = 0
      · rw [hq, mul_zero]
      · exfalso
        apply hj
        rcases hS j hq with rfl | rfl | rfl <;> simp
    have h0k : (0 : ZMod m) ∉ ({k, -k} : Finset (ZMod m)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨Ne.symm hk0, fun h => hk0 (neg_eq_zero.mp h.symm)⟩
    have hkk' : k ∉ ({-k} : Finset (ZMod m)) := by simpa using hkk
    rw [hinv, ← hsub, Finset.sum_insert h0k, Finset.sum_insert hkk', Finset.sum_singleton,
      dft_apply_zero, zero_mul, AddChar.map_zero_eq_one, one_mul, neg_mul,
      AddChar.map_neg_eq_conj]
    ring

/-- [proved-derived; formal-checked] **The phase chart** (§7(d)). When the residue is held as the
turn `ψ(x)`, the move `x ↦ b x + e` is a real-affine map of those points exactly when `b` is `1`
(a turn), `−1` (a mirror) or `0` (a flattening): pair both sides with the character of
frequency `b`. -/
theorem phase_chart_affine_iff (b e : ZMod m) :
    (∃ α β γ : ℂ, ∀ x : ZMod m,
      stdAddChar (b * x + e) = α * stdAddChar x + β * conj (stdAddChar x) + γ) ↔
      b = 1 ∨ b = -1 ∨ b = 0 := by
  constructor
  · rintro ⟨α, β, γ, h⟩
    by_contra hb
    push Not at hb
    have hsum : ∑ x : ZMod m, stdAddChar (-(x * b)) * stdAddChar (b * x + e) =
        ∑ x : ZMod m, stdAddChar (-(x * b)) * (α * stdAddChar x + β * conj (stdAddChar x) + γ) :=
      Finset.sum_congr rfl fun x _ => by rw [h x]
    have hl : ∑ x : ZMod m, stdAddChar (-(x * b)) * stdAddChar (b * x + e) =
        (m : ℂ) * stdAddChar e := by
      rw [Finset.sum_congr rfl fun x _ => show stdAddChar (-(x * b)) * stdAddChar (b * x + e) =
        stdAddChar e by rw [← AddChar.map_add_eq_mul]; congr 1; ring]
      simp
    have hr : ∑ x : ZMod m, stdAddChar (-(x * b)) * (α * stdAddChar x + β * conj (stdAddChar x) + γ)
        = α * ∑ x : ZMod m, stdAddChar (x * (1 - b)) + β * ∑ x : ZMod m, stdAddChar (x * (-1 - b))
          + γ * ∑ x : ZMod m, stdAddChar (x * -b) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [← AddChar.map_neg_eq_conj]
      have e1 : stdAddChar (-(x * b)) * stdAddChar x = stdAddChar (x * (1 - b)) := by
        rw [← AddChar.map_add_eq_mul]; congr 1; ring
      have e2 : stdAddChar (-(x * b)) * stdAddChar (-x) = stdAddChar (x * (-1 - b)) := by
        rw [← AddChar.map_add_eq_mul]; congr 1; ring
      have e3 : stdAddChar (-(x * b)) = stdAddChar (x * -b) := by congr 1; ring
      rw [mul_add, mul_add, mul_left_comm, e1, mul_left_comm, e2, e3]
      ring
    rw [hl, hr, char_sum, char_sum, char_sum] at hsum
    rw [if_neg (sub_ne_zero.mpr (Ne.symm hb.1)),
      if_neg (fun h => hb.2.1 (by linear_combination -h)), if_neg (neg_ne_zero.mpr hb.2.2)] at hsum
    simp only [mul_zero, add_zero] at hsum
    have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
    have hχ : stdAddChar e ≠ (0 : ℂ) := by
      intro h0
      have := congrArg (fun z => z * stdAddChar (-e)) h0
      simp only [zero_mul, ← AddChar.map_add_eq_mul, add_neg_cancel,
        AddChar.map_zero_eq_one] at this
      exact one_ne_zero this
    exact mul_ne_zero hm0 hχ hsum
  · rintro (rfl | rfl | rfl)
    · exact ⟨stdAddChar e, 0, 0, fun x => by rw [AddChar.map_add_eq_mul, one_mul]; ring⟩
    · exact ⟨0, stdAddChar e, 0, fun x => by
        rw [AddChar.map_add_eq_mul, ← AddChar.map_neg_eq_conj, neg_one_mul]; ring⟩
    · exact ⟨0, 0, stdAddChar e, fun x => by simp⟩

/-- [proved-standard; formal-checked] Every real-affine map of the plane `ℂ` is
`z ↦ α z + β z̄ + γ`, with `α = (L 1 − i L i)/2` and `β = (L 1 + i L i)/2` for its linear part
`L`. -/
theorem affine_form (A : ℂ →ᵃ[ℝ] ℂ) : ∃ α β γ : ℂ, ∀ z, A z = α * z + β * conj z + γ := by
  refine ⟨(A.linear 1 - I * A.linear I) / 2, (A.linear 1 + I * A.linear I) / 2, A 0, fun z => ?_⟩
  have h1 : A z = A.linear z + A 0 := by
    have := A.map_vadd 0 z
    simpa using this
  have h2 : A.linear z = (z.re : ℂ) * A.linear 1 + (z.im : ℂ) * A.linear I := by
    have hz : z = z.re • (1 : ℂ) + z.im • I := by simp [Complex.real_smul, Complex.re_add_im]
    conv_lhs => rw [hz]
    rw [map_add, _root_.map_smul, _root_.map_smul, Complex.real_smul, Complex.real_smul]
  rw [h1, h2, Complex.re_eq_add_conj, Complex.im_eq_sub_conj]
  field_simp
  ring_nf
  rw [Complex.I_sq]
  ring

/-- The real-affine map `z ↦ α z + β z̄ + γ`. -/
def affineOfCoeffs (α β γ : ℂ) : ℂ →ᵃ[ℝ] ℂ where
  toFun z := α * z + β * conj z + γ
  linear :=
    { toFun := fun z => α * z + β * conj z
      map_add' := fun z w => by simp only [map_add]; ring
      map_smul' := fun r z => by
        simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, RingHom.id_apply]
        ring }
  map_vadd' z v := by
    simp only [vadd_eq_add, LinearMap.coe_mk, AddHom.coe_mk, map_add]
    ring

@[simp] theorem affineOfCoeffs_apply (α β γ z : ℂ) :
    affineOfCoeffs α β γ z = α * z + β * conj z + γ := rfl

/-- [proved-derived; formal-checked] **The one-plane theorem in base ten.** A ring `m ≥ 3` coprime
to ten can be held in one real plane as `m` distinct points on which every digit acts by a
real-affine map exactly when `m` is 3, 9 or 11. The phase chart realizes those three; this is the
converse of `Holonics.Mathematics.RadixWindowReceiver.cheap_faces`, which owns the digit sum on
the divisors of `9` and the alternating sum on `11`. -/
theorem one_plane_ten_iff (hm : 3 ≤ m) (hcop : Nat.Coprime 10 m) :
    (∃ p : ZMod m → ℂ, Function.Injective p ∧ ∀ d : ℕ, d < 10 →
      ∃ A : ℂ →ᵃ[ℝ] ℂ, ∀ x, p (10 * x + d) = A (p x)) ↔ m = 3 ∨ m = 9 ∨ m = 11 := by
  constructor
  · rintro ⟨p, hp, hA⟩
    let b : (ZMod m)ˣ := ZMod.unitOfCoprime 10 hcop
    have hb : (b : ZMod m) = 10 := by simp [b]
    have hA' : ∀ e : ZMod m, e = 0 ∨ e = 1 →
        ∃ α β γ : ℂ, ∀ x, p ((b : ZMod m) * x + e) = α * p x + β * conj (p x) + γ := by
      rintro e (rfl | rfl)
      · obtain ⟨A, hA0⟩ := hA 0 (by norm_num)
        obtain ⟨α, β, γ, hαβγ⟩ := affine_form A
        exact ⟨α, β, γ, fun x => by rw [hb, ← hαβγ, ← hA0 x]; simp⟩
      · obtain ⟨A, hA1⟩ := hA 1 (by norm_num)
        obtain ⟨α, β, γ, hαβγ⟩ := affine_form A
        exact ⟨α, β, γ, fun x => by rw [hb, ← hαβγ, ← hA1 x]; simp⟩
    rcases one_plane hm b p hp hA' with h | h
    · rw [hb] at h
      have h9 : ((9 : ℕ) : ZMod m) = 0 := by
        rw [show ((9 : ℕ) : ZMod m) = 10 - 1 by norm_num, h, sub_self]
      have hd := (ZMod.natCast_eq_zero_iff 9 m).mp h9
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases m <;> simp_all (config := { decide := true })
    · rw [hb] at h
      have h11 : ((11 : ℕ) : ZMod m) = 0 := by
        rw [show ((11 : ℕ) : ZMod m) = 10 + 1 by norm_num, h, neg_add_cancel]
      have hd := (ZMod.natCast_eq_zero_iff 11 m).mp h11
      have := Nat.le_of_dvd (by norm_num) hd
      interval_cases m <;> simp_all (config := { decide := true })
  · intro hm'
    have hb : (10 : ZMod m) = 1 ∨ (10 : ZMod m) = -1 := by
      rcases hm' with rfl | rfl | rfl <;> decide
    refine ⟨fun x => stdAddChar x, injective_stdAddChar, fun d _ => ?_⟩
    obtain ⟨α, β, γ, h⟩ := (phase_chart_affine_iff (10 : ZMod m) d).mpr
      (hb.elim Or.inl (fun h => Or.inr (Or.inl h)))
    exact ⟨affineOfCoeffs α β γ, fun x => by rw [affineOfCoeffs_apply]; exact h x⟩

/-- [proved-derived; formal-checked] The phase chart in base ten: the move `x ↦ 10 x + d` is a
real-affine map of the turns exactly when `m` divides `9`, `11` or `10` (for `m ≥ 2`: rings 2, 3,
5, 9, 10 and 11). -/
theorem phase_chart_ten_iff (d : ZMod m) :
    (∃ α β γ : ℂ, ∀ x : ZMod m,
      stdAddChar (10 * x + d) = α * stdAddChar x + β * conj (stdAddChar x) + γ) ↔
      m ∣ 9 ∨ m ∣ 11 ∨ m ∣ 10 := by
  rw [phase_chart_affine_iff, ← ZMod.natCast_eq_zero_iff, ← ZMod.natCast_eq_zero_iff,
    ← ZMod.natCast_eq_zero_iff]
  have e9 : ((9 : ℕ) : ZMod m) = 10 - 1 := by norm_num
  have e11 : ((11 : ℕ) : ZMod m) = 10 - -1 := by norm_num
  have e10 : ((10 : ℕ) : ZMod m) = 10 := by norm_num
  rw [e9, e11, e10, sub_eq_zero, sub_eq_zero]

end Plane

end Holonics.Mathematics.OnePlaneRing
