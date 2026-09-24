import ElementaryHolonics.Transport.HolonicInteraction
import ElementaryHolonics.Foundation.ReceiverAtlas
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Tactic

/-!
# One Holonic Interaction chain: source → medium → neck → medium → perspective

[definition] This owner states the laws the Rust module `crates/holonic-engine/src/holonic_chain.rs`
implements. It is the **join** of the two halves already owned: the unit and its media
(`Transport/HolonicInteraction.lean`) and the neck station with its jet staircase
(`Transport/Neck.lean`, `Transport/JetStaircase.lean`). It founds no fifth object. A chain is
**one** interaction whose joint chart splits into an upstream medium and a downstream medium, with
the source incident only on the first and the perspective reading only the second.

## 1. The neck is the rank of the coupling between consecutive media

With the joint chart `Fin n₁ ⊕ Fin n₂`, write `A₂₁` for the generator's downstream–upstream block
(`crossBlock`). From `N X = 1` alone — no Schur complement, no one-directional hypothesis —
the resolvent's own cross block satisfies

```text
   N₂₂ X₂₁ = A₂₁ X₁₁            (cross_block_of_inverse)
```

because that *is* the second block row of `N X = 1`. Consequently, for a source supported on the
upstream block and a perspective reading only the downstream block,

```text
   C X B = (C₂ N₂₂⁻¹ U) · (V X₁₁ B₁)      whenever A₂₁ = U V
```

(`transfer_factors_through_the_neck`), so `rank (C X B) ≤ r` for **every** `s` off the poles
(`transfer_rank_le_neck_rank`), feedback included. `r = 1` is the pinhole
(`pinhole_transfer_rank_le_one`): plural inside each medium, a single channel at the interface's
grain. [agent-inferred] The one-directional product form `C₂(sI−A₂₂)⁻¹U · V(sI−A₁₁)⁻¹B₁` needs
`A₁₂ = 0`, which a port-Hamiltonian coupling never satisfies — the interconnection places `K` and
`−Kᵀ` in the two off-diagonal blocks at once. The statement above is therefore the operative one
and the product form is its special case; this correction is inferred from `portGenerator`'s own
skew structure, not from the contract.

A **closed** neck transmits nothing: `crossBlock A = 0` makes the upstream block invariant, so
every power of `A` has a vanishing cross block (`cross_block_pow_eq_zero_of_closed`) and every
Markov parameter is exactly zero (`markov_eq_zero_of_closed_neck`). That is the `Closed` arm of
`Transport/Neck.lean`'s neck reading with the flux forced to zero rather than assumed.

## 2. The power balance with ports, and continuity across a lossless neck

For `ẋ = A x + B u` with `A = (Ω − M) G` the port-Hamiltonian generator of
`Transport/HolonicInteraction.lean`,

```text
   d/dt (½ ⟨x, G x⟩) = ⟨u, Bᵀ G x⟩ − ⟨G x, M (G x)⟩      (port_power_balance)
```

— injected port power minus dissipated power, with the skew part contributing exactly nothing
(`skew_quad_eq_zero`). `port_power_balance_faces` resolves the dissipated term into the face
population through `quad_contactForm`, so the balance is *per face* and never only a sum.

Across the neck the two blocks exchange `Φ₁ = −⟨G₁x₁, A₁₂ x₂⟩` out of the upstream medium and
`Φ₂ = ⟨G₂x₂, A₂₁ x₁⟩` into the downstream one, and

```text
   Φ₂ − Φ₁ = −2 ⟨G₁ x₁, M_c (G₂ x₂)⟩        (neck_power_jump_is_twice_the_cross_dissipation)
```

with `M_c` the contact form's cross block. **The power current is continuous across a lossless
neck** (`power_current_is_continuous_across_a_lossless_neck`) and its discontinuity is exactly
twice the cross dissipation — which is the sink `σ` that `Transport/Neck.lean`'s station balance
consumes.

## 3. Markov parameters are the jet of the impulse response, and the relative degree of a chain

`markov A B C k = C Aᵏ B` — `Foundation/ReceiverAtlas.lean`'s own
`SeparatingAtlas.markov` at the chain's joint index type, as
`markov_is_the_separating_atlas_parameter` records. The formal sense in which these are the jet of
`C (sI−A)⁻¹ B` at infinity is denominator-free: `resolvent_telescope` is the exact finite identity
`(s I − A) · Σ_{k<N} s^{N−1−k} Aᵏ = s^N I − A^N`, and
`transfer_expansion_with_remainder` turns it into

```text
   s^N · (C X B) = Σ_{k<N} s^{N−1−k} · markov k  +  C X A^N B ,
```

the truncated expansion with its exact remainder retained rather than discarded.

`markov_zero_of_separated_ports` is `C B = 0`: a chain whose source and perspective sit on
different media has **no direct feedthrough**, so its relative degree is at least one
(`relative_degree_of_a_chain_is_at_least_one`). `markov_one_eq_neck_product` says the first
possibly-nonzero parameter is `C₂ A₂₁ B₁`, so whether the relative degree is exactly one is decided
by that product **per instance**. Nothing here asserts a universal increment for inserting a
medium or a neck; the increment is computed, and the Rust owner exhibits two chains whose
increments differ.

## 4. Reversal, and what it does not undo

`adjoint_is_the_reversed_structure` is `((Ω − M) G)ᵀ = G ((−Ω) − M)`: transposing the chain
reverses the *conservative* structure and leaves the *dissipative* one alone. Hence
`reversal_preserves_the_storage_rate` — the rate form of the reversed generator is the same
`−2 G M G` — and `no_direction_undoes_the_dissipation`: the storage still decays when the chain is
run the other way. `reciprocity_of_the_reversed_chain` gives the even half: the reversed chain's
transfer is the transpose of the original's, so `reversal_preserves_the_transfer_rank` and the
neck's rank bound are reversal-symmetric. That pair — rank and poles even, dissipated power odd in
nothing at all — is the exact datum about the oriented chain's entropy direction. It does not by
itself construct the crossing of the time and entropy axes, which remains open.

Truth status: every theorem below is `[proved-derived; formal-checked]` over exact rational
matrices. The block splitting of a chain is `[definition]`; the correction recorded in §1 is
`[agent-inferred]`. No `sorry`.
-/

namespace Soma.Holonics.Transport.HolonicChain

open Matrix
open Soma.Holonics.Transport.HolonicInteraction

/-- [definition] The joint chart of a two-medium chain: the upstream medium's coordinates followed
by the downstream medium's. -/
abbrev Joint (n₁ n₂ : ℕ) := Fin n₁ ⊕ Fin n₂

variable {n n₁ n₂ p q r : ℕ}

/-! ## 1. The chain's blocks -/

/-- [definition] `A₂₁`, the generator's downstream–upstream block. **This is the neck**: the only
route by which what happens in the upstream medium reaches the downstream one. -/
def crossBlock (A : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) : Matrix (Fin n₂) (Fin n₁) ℚ :=
  A.submatrix Sum.inr Sum.inl

/-- [definition] The excitation restricted to the upstream medium's own coordinates. -/
def upstreamPort (B : Matrix (Joint n₁ n₂) (Fin p) ℚ) : Matrix (Fin n₁) (Fin p) ℚ :=
  B.submatrix Sum.inl id

/-- [definition] The aperture restricted to the downstream medium's own coordinates. -/
def downstreamPort (C : Matrix (Fin q) (Joint n₁ n₂) ℚ) : Matrix (Fin q) (Fin n₂) ℚ :=
  C.submatrix id Sum.inr

/-- [definition] `|source⟩` is incident on the upstream medium alone. -/
def OnUpstream (B : Matrix (Joint n₁ n₂) (Fin p) ℚ) : Prop := ∀ i u, B (Sum.inr i) u = 0

/-- [definition] `⟨perspective|` reads the downstream medium alone. -/
def OnDownstream (C : Matrix (Fin q) (Joint n₁ n₂) ℚ) : Prop := ∀ y j, C y (Sum.inl j) = 0

/-- [proved-derived; formal-checked] Anything composed with a source that lives on the upstream
medium only sees that medium's columns. -/
theorem mul_onUpstream {γ : Type*} [Fintype γ] (Y : Matrix γ (Joint n₁ n₂) ℚ)
    {B : Matrix (Joint n₁ n₂) (Fin p) ℚ} (hB : OnUpstream B) :
    Y * B = Y.submatrix id Sum.inl * upstreamPort B := by
  ext g u
  have vanishes : ∀ i : Fin n₂, Y g (Sum.inr i) * B (Sum.inr i) u = 0 := by
    intro i
    rw [hB i u, mul_zero]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, upstreamPort, vanishes]

/-- [proved-derived; formal-checked] A perspective that reads the downstream medium only sees that
medium's rows. -/
theorem onDownstream_mul {γ : Type*} [Fintype γ] {C : Matrix (Fin q) (Joint n₁ n₂) ℚ}
    (hC : OnDownstream C) (X : Matrix (Joint n₁ n₂) γ ℚ) :
    C * X = downstreamPort C * X.submatrix Sum.inr id := by
  ext y g
  have vanishes : ∀ j : Fin n₁, C y (Sum.inl j) * X (Sum.inl j) g = 0 := by
    intro j
    rw [hC y j, zero_mul]
  simp [Matrix.mul_apply, Fintype.sum_sum_type, downstreamPort, vanishes]

/-- [proved-derived; formal-checked] **Whatever a chain's perspective reads of its source passes
through the `(downstream, upstream)` block and nothing else.** -/
theorem port_transfer_is_the_cross_block
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {X : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ}
    {B : Matrix (Joint n₁ n₂) (Fin p) ℚ} (hC : OnDownstream C) (hB : OnUpstream B) :
    C * X * B = downstreamPort C * X.submatrix Sum.inr Sum.inl * upstreamPort B := by
  rw [onDownstream_mul hC X, mul_onUpstream _ hB]
  rfl

/-! ## 2. The neck is the rank of the coupling, and the transfer factors through it -/

/-- [proved-derived; formal-checked] **The cross block of an inverse.** The second block row of
`N X = 1` says exactly `N₂₂ X₂₁ = K X₁₁` when `N`'s own cross block is `−K`. No Schur complement
and no one-directional hypothesis appear: this is the block equation itself. -/
theorem cross_block_of_inverse
    {N X : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ} {K : Matrix (Fin n₂) (Fin n₁) ℚ}
    (hN : N * X = 1) (hcross : N.submatrix Sum.inr Sum.inl = -K) :
    N.submatrix Sum.inr Sum.inr * X.submatrix Sum.inr Sum.inl
      = K * X.submatrix Sum.inl Sum.inl := by
  ext i j
  have h := congrFun (congrFun hN (Sum.inr i)) (Sum.inl j)
  rw [Matrix.one_apply_ne (by simp), Matrix.mul_apply, Fintype.sum_sum_type] at h
  have hleft : ∀ a : Fin n₁, N (Sum.inr i) (Sum.inl a) = -(K i a) := fun a =>
    congrFun (congrFun hcross i) a
  simp only [hleft, neg_mul, Finset.sum_neg_distrib] at h
  simp only [Matrix.mul_apply, Matrix.submatrix_apply]
  linarith [h]

/-- [proved-derived; formal-checked] The resolvent's cross block, from the same identity. -/
theorem resolvent_cross_block {A X : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ} {s : ℚ}
    (hX : (s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A) * X = 1) :
    (s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A).submatrix Sum.inr Sum.inr
        * X.submatrix Sum.inr Sum.inl
      = crossBlock A * X.submatrix Sum.inl Sum.inl := by
  refine cross_block_of_inverse hX ?_
  ext i j
  simp [crossBlock, Matrix.one_apply_ne]

/-- [proved-derived; formal-checked] **The neck factorization.** With `A₂₁ = U V` of inner width
`r`, everything the perspective reads of the source passes through `r` channels — in the feedback
case as much as in the one-directional one, because the Schur complement never had to be formed.
`X₁₁` is the resolvent's upstream block, which already carries the feedback. -/
theorem transfer_factors_through_the_neck
    {A X : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ} {s : ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    {U : Matrix (Fin n₂) (Fin r) ℚ} {V : Matrix (Fin r) (Fin n₁) ℚ}
    {Qinv : Matrix (Fin n₂) (Fin n₂) ℚ}
    (hC : OnDownstream C) (hB : OnUpstream B)
    (hX : (s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A) * X = 1)
    (hQ : Qinv * ((s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A).submatrix Sum.inr Sum.inr)
      = 1)
    (hfactor : crossBlock A = U * V) :
    C * X * B
      = (downstreamPort C * Qinv * U) * (V * X.submatrix Sum.inl Sum.inl * upstreamPort B) := by
  have cross := resolvent_cross_block hX
  have x21 : X.submatrix Sum.inr Sum.inl
      = Qinv * (crossBlock A * X.submatrix Sum.inl Sum.inl) := by
    calc X.submatrix Sum.inr Sum.inl
        = (1 : Matrix (Fin n₂) (Fin n₂) ℚ) * X.submatrix Sum.inr Sum.inl :=
          (Matrix.one_mul _).symm
      _ = Qinv * ((s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A).submatrix Sum.inr Sum.inr
            * X.submatrix Sum.inr Sum.inl) := by rw [← Matrix.mul_assoc, hQ]
      _ = Qinv * (crossBlock A * X.submatrix Sum.inl Sum.inl) := by rw [cross]
  rw [port_transfer_is_the_cross_block hC hB, x21, hfactor]
  simp only [Matrix.mul_assoc]

/-- [proved-derived; formal-checked] **The rank bound at the neck.** Every transfer from a source
on the upstream medium to a perspective on the downstream one has rank at most the rank of the
coupling, at every `s` where the resolvent and the downstream block are invertible. -/
theorem transfer_rank_le_neck_rank
    {A X : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ} {s : ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    {U : Matrix (Fin n₂) (Fin r) ℚ} {V : Matrix (Fin r) (Fin n₁) ℚ}
    {Qinv : Matrix (Fin n₂) (Fin n₂) ℚ}
    (hC : OnDownstream C) (hB : OnUpstream B)
    (hX : (s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A) * X = 1)
    (hQ : Qinv * ((s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A).submatrix Sum.inr Sum.inr)
      = 1)
    (hfactor : crossBlock A = U * V) :
    (C * X * B).rank ≤ r := by
  rw [transfer_factors_through_the_neck hC hB hX hQ hfactor]
  exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_width _)

/-- [proved-derived; formal-checked] **The pinhole.** A rank-one coupling makes the whole chain a
single channel at the interface's grain, however plural each medium is inside. -/
theorem pinhole_transfer_rank_le_one
    {A X : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ} {s : ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    {U : Matrix (Fin n₂) (Fin 1) ℚ} {V : Matrix (Fin 1) (Fin n₁) ℚ}
    {Qinv : Matrix (Fin n₂) (Fin n₂) ℚ}
    (hC : OnDownstream C) (hB : OnUpstream B)
    (hX : (s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A) * X = 1)
    (hQ : Qinv * ((s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A).submatrix Sum.inr Sum.inr)
      = 1)
    (hfactor : crossBlock A = U * V) :
    (C * X * B).rank ≤ 1 :=
  transfer_rank_le_neck_rank hC hB hX hQ hfactor

/-- [proved-derived; formal-checked] **Full-rank ports read the whole neck: the rank is not a
bound but an equality.** `Cl` is a left inverse of the downstream port and `Br` a right inverse of
the upstream one — which over a field is exactly full column rank for `C₂` and full row rank for
`B₁` — so the two ports neither lose nor add a channel and the transfer's rank is the rank of the
resolvent's own cross block.

The **nullity theorem** enters as the single named hypothesis `hnullity`, never as an axiom:
complementary blocks of a nonsingular matrix and of its inverse have equal nullity, so
`rank X_↗ = rank N_↗ = rank A_↗` at every probe off the joint poles with **no hypothesis on
`N₂₂`**. Its own lift is owed and is issue #34 — `[proved-standard]` (R. L. Gustafson, *A note on
matrix inversion*, Linear Algebra Appl. 57 (1984), Theorem 1; M. Fiedler and T. L. Markham,
Linear Algebra Appl. 74 (1986)). Composing the two gives `rank H(s) = rank A_↗ = r` exactly, with
no resolvent inverse taken — which is what `holonic_chain.rs::RankLicence::Determined` returns. -/
theorem full_rank_ports_read_the_whole_neck
    {A X : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    {Cl : Matrix (Fin n₂) (Fin q) ℚ} {Br : Matrix (Fin p) (Fin n₁) ℚ}
    (hC : OnDownstream C) (hB : OnUpstream B)
    (hCl : Cl * downstreamPort C = 1) (hBr : upstreamPort B * Br = 1)
    (hnullity : (X.submatrix Sum.inr Sum.inl).rank = (crossBlock A).rank) :
    (C * X * B).rank = (crossBlock A).rank := by
  rw [port_transfer_is_the_cross_block hC hB, ← hnullity]
  set Y := X.submatrix Sum.inr Sum.inl with hY
  have upper : (downstreamPort C * Y * upstreamPort B).rank ≤ Y.rank :=
    le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
  have recover : Cl * (downstreamPort C * Y * upstreamPort B) * Br = Y := by
    have regroup : Cl * (downstreamPort C * Y * upstreamPort B) * Br
        = Cl * downstreamPort C * (Y * (upstreamPort B * Br)) := by
      simp only [Matrix.mul_assoc]
    rw [regroup, hCl, hBr, Matrix.one_mul, Matrix.mul_one]
  have lower : Y.rank ≤ (downstreamPort C * Y * upstreamPort B).rank := by
    conv_lhs => rw [← recover]
    exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_mul_le_right _ _)
  exact le_antisymm upper lower

/-- [proved-derived; formal-checked] **The pinhole, determined.** With full-rank ports a rank-one
coupling makes the transfer rank exactly one, not at most one: the single channel is carried, not
merely bounded. -/
theorem full_rank_ports_read_a_pinhole_as_one
    {A X : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    {Cl : Matrix (Fin n₂) (Fin q) ℚ} {Br : Matrix (Fin p) (Fin n₁) ℚ}
    (hC : OnDownstream C) (hB : OnUpstream B)
    (hCl : Cl * downstreamPort C = 1) (hBr : upstreamPort B * Br = 1)
    (hnullity : (X.submatrix Sum.inr Sum.inl).rank = (crossBlock A).rank)
    (hpinhole : (crossBlock A).rank = 1) :
    (C * X * B).rank = 1 := by
  rw [full_rank_ports_read_the_whole_neck hC hB hCl hBr hnullity, hpinhole]

/-! ## 3. A closed neck transmits nothing -/

/-- [proved-derived; formal-checked] With a vanishing coupling the upstream block is invariant, so
no power of the generator ever reaches the downstream medium. -/
theorem cross_block_pow_eq_zero_of_closed
    {A : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ} (hclosed : crossBlock A = 0) :
    ∀ k : ℕ, (A ^ k).submatrix Sum.inr Sum.inl = 0 := by
  intro k
  induction k with
  | zero =>
    ext i j
    simp [Matrix.one_apply_ne]
  | succ k ih =>
    ext i j
    have hA : ∀ a : Fin n₁, A (Sum.inr i) (Sum.inl a) = 0 := fun a =>
      congrFun (congrFun hclosed i) a
    have hpow : ∀ b : Fin n₂, (A ^ k) (Sum.inr b) (Sum.inl j) = 0 := fun b =>
      congrFun (congrFun ih b) j
    rw [pow_succ']
    simp [Matrix.mul_apply, Fintype.sum_sum_type, hA, hpow]

/-- [proved-derived; formal-checked] **`Closed`, with the flux forced to zero rather than
assumed.** Every Markov parameter of a chain whose coupling vanishes is exactly the zero matrix. -/
theorem markov_eq_zero_of_closed_neck
    {A : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    (hC : OnDownstream C) (hB : OnUpstream B) (hclosed : crossBlock A = 0) (k : ℕ) :
    C * A ^ k * B = 0 := by
  rw [port_transfer_is_the_cross_block hC hB, cross_block_pow_eq_zero_of_closed hclosed k]
  simp

/-! ## 4. The Markov staircase and the relative degree of a chain -/

/-- [definition] The `k`th Markov parameter: the `k`th derivative at `0` of the impulse response
`h(t) = C e^{At} B`, and the `k`th coefficient of the expansion of `C (sI−A)⁻¹ B` at infinity.

**This is not a second notion.** It is `Foundation/ReceiverAtlas.lean`'s own
`Soma.Holonics.Foundation.Atlas.SeparatingAtlas.markov`, written at the chain's joint index type
`Fin n₁ ⊕ Fin n₂` rather than at `Fin n`; `markov_is_the_separating_atlas_parameter` exhibits the
agreement. -/
def markov (A : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) (B : Matrix (Joint n₁ n₂) (Fin p) ℚ)
    (C : Matrix (Fin q) (Joint n₁ n₂) ℚ) (k : ℕ) : Matrix (Fin q) (Fin p) ℚ :=
  C * A ^ k * B

/-- [proved-derived; formal-checked] The chain's Markov parameter and the separating atlas's are
the same matrix wherever both are defined, so this file founds nothing the receiver atlas already
owns. -/
theorem markov_is_the_separating_atlas_parameter {n m : ℕ}
    (C : Matrix (Fin q) (Fin n) ℚ) (A : Matrix (Fin n) (Fin n) ℚ)
    (B : Matrix (Fin n) (Fin m) ℚ) (k : ℕ) :
    C * A ^ k * B = Soma.Holonics.Foundation.Atlas.SeparatingAtlas.markov C A B k :=
  rfl

/-- [proved-derived; formal-checked] **No direct feedthrough across a neck.** -/
theorem markov_zero_of_separated_ports
    {A : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    (hC : OnDownstream C) (hB : OnUpstream B) :
    markov A B C 0 = 0 := by
  rw [markov, pow_zero, port_transfer_is_the_cross_block hC hB]
  have : ((1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ)).submatrix Sum.inr Sum.inl
      = (0 : Matrix (Fin n₂) (Fin n₁) ℚ) := by
    ext i j
    simp [Matrix.one_apply_ne]
  rw [this]
  simp

/-- [proved-derived; formal-checked] **The relative degree of a chain is at least one**: the
perspective reads nothing of the source before the coupling has acted once. -/
theorem relative_degree_of_a_chain_is_at_least_one
    {A : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    (hC : OnDownstream C) (hB : OnUpstream B) :
    ∀ k : ℕ, markov A B C k ≠ 0 → 1 ≤ k := by
  intro k hk
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · exact absurd (markov_zero_of_separated_ports hC hB) hk
  · exact hpos

/-- [proved-derived; formal-checked] The first possibly-nonzero Markov parameter is the neck
product `C₂ A₂₁ B₁`. Whether the relative degree is exactly one is therefore decided by this
product at each instance; no universal increment is available from the shape of a chain. -/
theorem markov_one_eq_neck_product
    {A : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    (hC : OnDownstream C) (hB : OnUpstream B) :
    markov A B C 1 = downstreamPort C * crossBlock A * upstreamPort B := by
  rw [markov, pow_one, port_transfer_is_the_cross_block hC hB]
  rfl

/-- [proved-derived; formal-checked] The first parameter obeys the same rank bound as the
transfer. -/
theorem markov_one_rank_le_neck_rank
    {A : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    {U : Matrix (Fin n₂) (Fin r) ℚ} {V : Matrix (Fin r) (Fin n₁) ℚ}
    (hC : OnDownstream C) (hB : OnUpstream B) (hfactor : crossBlock A = U * V) :
    (markov A B C 1).rank ≤ r := by
  rw [markov_one_eq_neck_product hC hB, hfactor]
  have : downstreamPort C * (U * V) * upstreamPort B
      = (downstreamPort C * U) * (V * upstreamPort B) := by
    simp only [Matrix.mul_assoc]
  rw [this]
  exact le_trans (Matrix.rank_mul_le_left _ _) (Matrix.rank_le_width _)

/-! ### The expansion at infinity, denominator-free -/

/-- [definition] The exact finite partial sum `Σ_{k<N} s^{N−1−k} Aᵏ`. -/
def partialResolvent {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) (s : ℚ) (N : ℕ) :
    Matrix ι ι ℚ :=
  ∑ k ∈ Finset.range N, s ^ (N - 1 - k) • A ^ k

/-- [proved-derived; formal-checked] Its recurrence. -/
theorem partialResolvent_succ {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) (s : ℚ)
    (N : ℕ) : partialResolvent A s (N + 1) = s ^ N • 1 + partialResolvent A s N * A := by
  rw [partialResolvent, partialResolvent, Finset.sum_range_succ', Finset.sum_mul]
  have step : ∀ k ∈ Finset.range N,
      s ^ (N + 1 - 1 - (k + 1)) • A ^ (k + 1) = (s ^ (N - 1 - k) • A ^ k) * A := by
    intro k _
    have index : N + 1 - 1 - (k + 1) = N - 1 - k := by omega
    rw [index, pow_succ, Matrix.smul_mul]
  rw [Finset.sum_congr rfl step]
  simp only [Nat.add_sub_cancel, Nat.sub_zero, pow_zero]
  rw [add_comm]

/-- [proved-derived; formal-checked] **The telescoping identity.** Exact over `ℚ`, with no
division and no limit: `(sI − A) Σ_{k<N} s^{N−1−k} Aᵏ = s^N I − A^N`. -/
theorem resolvent_telescope {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℚ) (s : ℚ)
    (N : ℕ) :
    (s • (1 : Matrix ι ι ℚ) - A) * partialResolvent A s N
      = s ^ N • (1 : Matrix ι ι ℚ) - A ^ N := by
  induction N with
  | zero => simp [partialResolvent]
  | succ N ih =>
    rw [partialResolvent_succ, Matrix.mul_add, ← Matrix.mul_assoc, ih]
    simp only [Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_one,
      smul_sub, smul_smul, ← pow_succ]
    abel

/-- [proved-derived; formal-checked] The partial sum's port reading is the Markov generating
polynomial. -/
theorem markov_are_the_expansion_coefficients
    {A : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ} (s : ℚ) (N : ℕ) :
    C * partialResolvent A s N * B
      = ∑ k ∈ Finset.range N, s ^ (N - 1 - k) • markov A B C k := by
  rw [partialResolvent, Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [markov, Matrix.mul_smul, Matrix.smul_mul]

/-- [proved-derived; formal-checked] **The jet of the transfer function at infinity, with its
remainder kept.** Nothing is truncated away silently: the `N`th remainder `C X A^N B` is returned
in the identity. -/
theorem transfer_expansion_with_remainder
    {A X : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ} {s : ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    (hXL : X * (s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A) = 1) (N : ℕ) :
    s ^ N • (C * X * B)
      = (∑ k ∈ Finset.range N, s ^ (N - 1 - k) • markov A B C k) + C * X * A ^ N * B := by
  have carrier : X * (s ^ N • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A ^ N)
      = partialResolvent A s N := by
    rw [← resolvent_telescope A s N, ← Matrix.mul_assoc, hXL, Matrix.one_mul]
  have expand : s ^ N • X = partialResolvent A s N + X * A ^ N := by
    have := carrier
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one] at this
    rw [← this]
    abel
  calc s ^ N • (C * X * B)
      = C * (s ^ N • X) * B := by
        rw [Matrix.mul_smul, Matrix.smul_mul]
    _ = C * (partialResolvent A s N + X * A ^ N) * B := by rw [expand]
    _ = C * partialResolvent A s N * B + C * X * A ^ N * B := by
        simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = (∑ k ∈ Finset.range N, s ^ (N - 1 - k) • markov A B C k) + C * X * A ^ N * B := by
        rw [markov_are_the_expansion_coefficients]

/-! ## 5. The power balance with ports -/

/-- [definition] The rate of the storage reading `E_G = ½⟨x, G x⟩` along a declared flow. -/
def storageRate (G : Matrix (Fin n) (Fin n) ℚ) (x xdot : Fin n → ℚ) : ℚ := (G *ᵥ x) ⬝ᵥ xdot

/-- [definition] The power injected through the source's ports. -/
def portPower (Bm : Matrix (Fin n) (Fin p) ℚ) (G : Matrix (Fin n) (Fin n) ℚ) (x : Fin n → ℚ)
    (u : Fin p → ℚ) : ℚ := u ⬝ᵥ (Bmᵀ *ᵥ (G *ᵥ x))

/-- [definition] The declared flow `ẋ = A x + B u`. -/
def flow (A : Matrix (Fin n) (Fin n) ℚ) (Bm : Matrix (Fin n) (Fin p) ℚ) (x : Fin n → ℚ)
    (u : Fin p → ℚ) : Fin n → ℚ := A *ᵥ x + Bm *ᵥ u

/-- [proved-derived; formal-checked] A skew structure reads exactly zero power at every motion:
the conservative part of the generator neither injects nor removes storage. -/
theorem skew_quad_eq_zero (Omega : Matrix (Fin n) (Fin n) ℚ) (hOmega : Omegaᵀ = -Omega)
    (v : Fin n → ℚ) : v ⬝ᵥ (Omega *ᵥ v) = 0 := by
  have mirrored : v ⬝ᵥ (Omega *ᵥ v) = -(v ⬝ᵥ (Omega *ᵥ v)) := by
    calc v ⬝ᵥ (Omega *ᵥ v) = (v ᵥ* Omega) ⬝ᵥ v := by rw [Matrix.dotProduct_mulVec]
      _ = (Omegaᵀ *ᵥ v) ⬝ᵥ v := by rw [← Matrix.mulVec_transpose]
      _ = ((-Omega) *ᵥ v) ⬝ᵥ v := by rw [hOmega]
      _ = -((Omega *ᵥ v) ⬝ᵥ v) := by rw [Matrix.neg_mulVec, neg_dotProduct]
      _ = -(v ⬝ᵥ (Omega *ᵥ v)) := by rw [dotProduct_comm]
  linarith [mirrored]

/-- [proved-derived; formal-checked] **The power balance of one chain with ports.**
`d/dt (½⟨x, G x⟩) = ⟨u, Bᵀ G x⟩ − ⟨G x, M (G x)⟩`: injected port power minus dissipated power,
with the skew structure contributing nothing at all. This is `port_storage_rate` carried to a
system that has an input. -/
theorem port_power_balance (Omega M G : Matrix (Fin n) (Fin n) ℚ)
    (Bm : Matrix (Fin n) (Fin p) ℚ) (hOmega : Omegaᵀ = -Omega) (x : Fin n → ℚ) (u : Fin p → ℚ) :
    storageRate G x (flow (portGenerator Omega M G) Bm x u)
      = portPower Bm G x u - quad M (G *ᵥ x) := by
  have transported : portGenerator Omega M G *ᵥ x = (Omega - M) *ᵥ (G *ᵥ x) := by
    rw [portGenerator, Matrix.mulVec_mulVec]
  have port : (G *ᵥ x) ⬝ᵥ (Bm *ᵥ u) = u ⬝ᵥ (Bmᵀ *ᵥ (G *ᵥ x)) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  rw [storageRate, flow, dotProduct_add, transported, Matrix.sub_mulVec, dotProduct_sub,
    skew_quad_eq_zero Omega hOmega (G *ᵥ x), portPower, quad, port]
  ring

/-- [proved-derived; formal-checked] **The same balance, face by face.** The dissipated term is
resolved into the declared contact population through `quad_contactForm`, so a chain's power
receipt names every face and never only their sum. -/
theorem port_power_balance_faces {m k : ℕ} (Omega G : Matrix (Fin n) (Fin n) ℚ)
    (Bm : Matrix (Fin n) (Fin p) ℚ) (w : Fin m → ℚ) (J : Fin m → Matrix (Fin k) (Fin n) ℚ)
    (D : Fin m → Matrix (Fin k) (Fin k) ℚ) (hOmega : Omegaᵀ = -Omega) (x : Fin n → ℚ)
    (u : Fin p → ℚ) :
    storageRate G x (flow (portGenerator Omega (contactForm w J D) G) Bm x u)
      = portPower Bm G x u
        - ∑ f : Fin m, w f * ((J f *ᵥ (G *ᵥ x)) ⬝ᵥ (D f *ᵥ (J f *ᵥ (G *ᵥ x)))) := by
  rw [port_power_balance Omega (contactForm w J D) G Bm hOmega x u, quad_contactForm]

/-! ## 6. The power current across the neck -/

/-- [proved-derived; formal-checked] **The jump in the power current across the neck is exactly
twice the cross dissipation.** `Φ₁ = −⟨G₁x₁, A₁₂x₂⟩` leaves the upstream medium and
`Φ₂ = ⟨G₂x₂, A₂₁x₁⟩` enters the downstream one, with `A₁₂ = (K − M_c)G₂` and
`A₂₁ = (−Kᵀ − M_cᵀ)G₁` the port-Hamiltonian interconnection's two off-diagonal blocks. -/
theorem neck_power_jump_is_twice_the_cross_dissipation
    (K Mc : Matrix (Fin n₁) (Fin n₂) ℚ) (G₁ : Matrix (Fin n₁) (Fin n₁) ℚ)
    (G₂ : Matrix (Fin n₂) (Fin n₂) ℚ) (x₁ : Fin n₁ → ℚ) (x₂ : Fin n₂ → ℚ) :
    (G₂ *ᵥ x₂) ⬝ᵥ (((-Kᵀ - Mcᵀ) * G₁) *ᵥ x₁) + (G₁ *ᵥ x₁) ⬝ᵥ (((K - Mc) * G₂) *ᵥ x₂)
      = -2 * ((G₁ *ᵥ x₁) ⬝ᵥ (Mc *ᵥ (G₂ *ᵥ x₂))) := by
  have swapK : (G₂ *ᵥ x₂) ⬝ᵥ (Kᵀ *ᵥ (G₁ *ᵥ x₁)) = (G₁ *ᵥ x₁) ⬝ᵥ (K *ᵥ (G₂ *ᵥ x₂)) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  have swapM : (G₂ *ᵥ x₂) ⬝ᵥ (Mcᵀ *ᵥ (G₁ *ᵥ x₁)) = (G₁ *ᵥ x₁) ⬝ᵥ (Mc *ᵥ (G₂ *ᵥ x₂)) := by
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.sub_mulVec, Matrix.sub_mulVec,
    dotProduct_sub, dotProduct_sub, Matrix.neg_mulVec, dotProduct_neg, swapK, swapM]
  ring

/-- [proved-derived; formal-checked] **Continuity across a lossless neck.** With no dissipative
cross block the power that leaves the upstream medium is exactly the power that enters the
downstream one. That is the flux conservation `Transport/Neck.lean`'s sourceless station balance
assumes, derived here rather than declared. -/
theorem power_current_is_continuous_across_a_lossless_neck
    (K : Matrix (Fin n₁) (Fin n₂) ℚ) (G₁ : Matrix (Fin n₁) (Fin n₁) ℚ)
    (G₂ : Matrix (Fin n₂) (Fin n₂) ℚ) (x₁ : Fin n₁ → ℚ) (x₂ : Fin n₂ → ℚ) :
    (G₂ *ᵥ x₂) ⬝ᵥ (((-Kᵀ - (0 : Matrix (Fin n₁) (Fin n₂) ℚ)ᵀ) * G₁) *ᵥ x₁)
      = -((G₁ *ᵥ x₁) ⬝ᵥ (((K - (0 : Matrix (Fin n₁) (Fin n₂) ℚ)) * G₂) *ᵥ x₂)) := by
  have identity :=
    neck_power_jump_is_twice_the_cross_dissipation K 0 G₁ G₂ x₁ x₂
  simp only [Matrix.zero_mulVec, dotProduct_zero, mul_zero] at identity
  linarith [identity]

/-! ## 7. Reversal, and what it does not undo -/

/-- [proved-derived; formal-checked] **Transposing a chain reverses its conservative structure and
leaves its dissipation alone.** No invertibility is used. -/
theorem adjoint_is_the_reversed_structure (Omega M G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G)
    (hOmega : Omegaᵀ = -Omega) (hM : Mᵀ = M) :
    (portGenerator Omega M G)ᵀ = G * ((-Omega) - M) := by
  rw [portGenerator, Matrix.transpose_mul, Matrix.transpose_sub, hOmega, hM, hG]

/-- [proved-derived; formal-checked] **The storage rate is even under reversal.** Running the
chain the other way gives the same `−2 G M G`: the dissipated power does not change sign with the
orientation. -/
theorem reversal_preserves_the_storage_rate (Omega M G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G)
    (hOmega : Omegaᵀ = -Omega) (hM : Mᵀ = M) :
    rateFormQ (portGenerator (-Omega) M G) G = rateFormQ (portGenerator Omega M G) G := by
  have reversed : (-Omega)ᵀ = -(-Omega) := by rw [Matrix.transpose_neg, hOmega, neg_neg]
  rw [port_storage_rate (-Omega) M G hG reversed hM, port_storage_rate Omega M G hG hOmega hM]

/-- [proved-derived; formal-checked] **No direction of the chain undoes its dissipation.** This is
the first exact datum about the oriented chain's entropy direction: the even part of the generator
sets the sign of the storage rate, and reversal acts only on the odd part. -/
theorem no_direction_undoes_the_dissipation (Omega M G : Matrix (Fin n) (Fin n) ℚ) (hG : Gᵀ = G)
    (hOmega : Omegaᵀ = -Omega) (hM : Mᵀ = M) (hMpsd : ∀ s : Fin n → ℚ, 0 ≤ quad M s)
    (v : Fin n → ℚ) :
    quad (rateFormQ (portGenerator (-Omega) M G) G) v ≤ 0 := by
  rw [reversal_preserves_the_storage_rate Omega M G hG hOmega hM]
  exact storage_rate_nonpos Omega M G hG hOmega hM hMpsd v

/-- [proved-derived; formal-checked] **Reciprocity.** The reversed chain — source and perspective
exchanged, the generator transposed — has the transposed transfer, and its resolvent is the
transposed resolvent. -/
theorem reciprocity_of_the_reversed_chain
    {A X : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ} {s : ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ}
    (hX : (s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - A) * X = 1) :
    (C * X * B)ᵀ = Bᵀ * Xᵀ * Cᵀ
      ∧ Xᵀ * (s • (1 : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ) - Aᵀ) = 1 := by
  refine ⟨by rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.mul_assoc], ?_⟩
  have transposed := congrArg Matrix.transpose hX
  simp only [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_smul,
    Matrix.transpose_one] at transposed
  exact transposed

/-- [proved-derived; formal-checked] **The rank bound is reversal-symmetric.** Whatever the neck
admits in one direction it admits in the other; only the dissipated power distinguishes them. -/
theorem reversal_preserves_the_transfer_rank
    {X : Matrix (Joint n₁ n₂) (Joint n₁ n₂) ℚ}
    {C : Matrix (Fin q) (Joint n₁ n₂) ℚ} {B : Matrix (Joint n₁ n₂) (Fin p) ℚ} :
    (Bᵀ * Xᵀ * Cᵀ).rank = (C * X * B).rank := by
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul, Matrix.mul_assoc, Matrix.rank_transpose]

/-! ## Audit

[definition] Every declaration of this file's axiom dependencies, printed by the kernel. Only
`propext`, `Classical.choice` and `Quot.sound` are acceptable; `sorryAx` appears nowhere. -/

namespace Audit

#print axioms mul_onUpstream
#print axioms onDownstream_mul
#print axioms port_transfer_is_the_cross_block
#print axioms cross_block_of_inverse
#print axioms resolvent_cross_block
#print axioms transfer_factors_through_the_neck
#print axioms transfer_rank_le_neck_rank
#print axioms pinhole_transfer_rank_le_one
#print axioms full_rank_ports_read_the_whole_neck
#print axioms full_rank_ports_read_a_pinhole_as_one
#print axioms cross_block_pow_eq_zero_of_closed
#print axioms markov_eq_zero_of_closed_neck
#print axioms markov_is_the_separating_atlas_parameter
#print axioms markov_zero_of_separated_ports
#print axioms relative_degree_of_a_chain_is_at_least_one
#print axioms markov_one_eq_neck_product
#print axioms markov_one_rank_le_neck_rank
#print axioms partialResolvent_succ
#print axioms resolvent_telescope
#print axioms markov_are_the_expansion_coefficients
#print axioms transfer_expansion_with_remainder
#print axioms skew_quad_eq_zero
#print axioms port_power_balance
#print axioms port_power_balance_faces
#print axioms neck_power_jump_is_twice_the_cross_dissipation
#print axioms power_current_is_continuous_across_a_lossless_neck
#print axioms adjoint_is_the_reversed_structure
#print axioms reversal_preserves_the_storage_rate
#print axioms no_direction_undoes_the_dissipation
#print axioms reciprocity_of_the_reversed_chain
#print axioms reversal_preserves_the_transfer_rank

end Audit

end Soma.Holonics.Transport.HolonicChain
