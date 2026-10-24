import Holonics.Geometry.Motion
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Order is torsion: the carry a loop of moves leaves

[proved-derived; formal-checked] October 22
([record](../../../research/records/2026-10-22_ORDER_IS_TORSION_AND_SUBGRAIN_INFORMATION_DISSOLVES_INTO_THE_CARRIED_RESIDUE.md)).
The motion owner (`Geometry/Motion`) states the move `x ↦ M x + b`, its pivot `(1 − M) O = b` and
the composition law. This module reads the failure of two moves to commute as the **carry** they
leave around their loop. That is the teleparallel reading of torsion: a loop of moves fails to
close by a turn (curvature) or by a carry (torsion), and the carry of a pair of turns is the
separation of their pivots.

```text
(k_u, b_u) ∘ (k_v, b_v) − (k_v, b_v) ∘ (k_u, b_u) = b_u (1 − k_v) − b_v (1 − k_u)   (complex_moves_commutator)
                                                  = (1 − k_u)(1 − k_v)(O_u − O_v)     (complex_commutator_pivots)
k_u, k_v ≠ 1:   the two moves commute  ⇔  O_u = O_v               (complex_moves_commute_iff_shared_pivot)
(M, b₁) ∘ (M, b₂) − (M, b₂) ∘ (M, b₁) = (1 − M)(b₁ − b₂)          (move_same_linear_commutator)
(M_b, b_b) ∘ (M_a, b_a) − (M_a, b_a) ∘ (M_b, b_b)
    = (M_b M_a − M_a M_b) x + (M_b − 1) b_a − (M_a − 1) b_b        (move_commutator)
```

What is proved.

1. **Order is torsion** (`complex_moves_commutator`, `complex_commutator_pivots`,
   `complex_moves_commute_iff_shared_pivot`): two turns commute exactly when they share a pivot,
   and the carry of their loop is the product of their two departures from free fall times the
   separation of their pivots.
2. **One linear part** (`move_same_linear_commutator`): moves that share their linear part `M` and
   differ only in what they add leave the carry `(1 − M)(b₁ − b₂)`. For any two moves
   (`move_commutator`) the loop leaves the commutator of the turns on the state, the curvature,
   beside the carry of the additions, the torsion; a receiver reads order only through what its
   face does not annihilate of that difference. A stream of such moves is a sum
   of `M`-transported additions, so its state is a function of how often each addition occurred at
   each lag.
3. **The Burgers vector** (`flat_loop_carry`): a loop of pure translations closes by the sum of
   its carries.
4. **The carry needs its base point** (`move_basepoint`, `translation_basepoint`): read from a base
   point shifted by `t`, a move keeps its turn and its carry gains `(M − 1) t`; the carry is
   independent of the base point only when the turn is trivial.
5. **The fifth torsion is the field** (`fifth_torsion_is_field`): for a frame `e⁵ = dy + A`, an
   exact part never reaches the coboundary, so `d e⁵ = d A`; this is `T⁵ = F` of teleparallel
   Kaluza–Klein, with charge the carry around the fifth circle.
6. **The redshift loop** (`redshift_loop`): on a grid of cells, the coboundary of the time coframe
   `e⁰ = N dt` summed over the cells is the product of the lapse and clock differences across the
   whole grid (Stokes on a grid), so a static lapse difference leaves a carry around every loop
   that spans it.
7. **The squeeze is the ratio's dilation** (`squeeze_dilates_ratio`): `diag(λ, λ⁻¹)` acting on the
   undivided pair `(a, b)` multiplies its ratio by `λ²`. The det-1 squeeze of the turn·boost·shear
   factorization and the ratio dilation `MoveKind::Boost` are one boost read in two charts.
8. **The lag-residue factorization** (`laggedRun_closed`, `laggedRun_lag_residue`,
   `laggedRun_eq_of_counts`): a stream of moves with one linear part `M`, each adding `E (u k)`,
   reaches `Mᵗ x₀ + Σ_k M^(t−1−k) E (u k)`; when `M^N = 1` this is
   `Mᵗ x₀ + Σ_(r < N) Σ_a n(a, r) • M^r E a`, with `n(a, r)` the number of cells `k < t` carrying
   symbol `a` at lag residue `r`. Two streams with the same counts reach the same state, so every
   reading of such a stream is a function of its (symbol, lag residue) counts.
9. **The selected move's forward jet** (`lamJet_is_derivative`, `betaJet_is_derivative`,
   `betaJet_eq_selectedRun`): when the symbol selects the move, `z' = λ_(t, u t) z + β_(t, u t)`,
   the jets `J' = λ_(t, u t) J + [u t = a] z` and `J' = λ_(t, u t) J + [u t = a]` are the exact
   derivatives of the stream with respect to one shift of the turn or the addition of symbol `a`
   at every cell (read in dual numbers), also when the moves change during the passage. The jet
   is the phase-carried moment; its adjoint needs no tape.
10. **The certificate** (`selectedRun_norm_bound`, `lamJet_norm_bound`,
   `selectedRun_norm_le_linear`, `lamJet_norm_le_quadratic`): in any normed ring, with
   `‖λ_(t, s)‖ ≤ ρ ≤ 1` and `‖β_(t, s)‖ ≤ B`, the state satisfies `‖z‖ (1 − ρ) ≤ B` and the turn's
   jet `‖J‖ (1 − ρ)² ≤ B`; at `ρ = 1` the state grows at most as `t B` and the jet as
   `B t (t − 1)/2`. For a scalar mode the per-symbol bound is the joint bound; for a matrix mode
   it is a bound in one metric `G` shared by every symbol (`M_sᵀ G M_s ⪯ ρ² G`), which certifies
   every word.
11. **One plane cannot carry order** (`plane_reflections_compose`, `plane_turns_commute`): two
   plane reflections `z ↦ u z̄` compose to the turn `u v̄`, and such turns commute, so symbol-chosen
   reflections in one plane read parity and a signed phase sum only. Order needs non-commuting
   transports: at least two coupled planes whose reflections do not share a pencil.

No `sorry`, no `axiom`.
-/

open scoped BigOperators

namespace Holonics.Geometry.Motion

/-! ## 1. Order is torsion -/

section ComplexTorsion

variable {K : Type*} [Field K]

/-- [proved-derived; formal-checked] **The carry of a loop of two moves.** -/
theorem complex_moves_commutator (ku bu kv bv z : K) :
    (ku * (kv * z + bv) + bu) - (kv * (ku * z + bu) + bv) = bu * (1 - kv) - bv * (1 - ku) := by
  ring

/-- [proved-derived; formal-checked] **The carry is the separation of the pivots.** -/
theorem complex_commutator_pivots {ku kv bu bv Ou Ov : K}
    (hOu : (1 - ku) * Ou = bu) (hOv : (1 - kv) * Ov = bv) :
    bu * (1 - kv) - bv * (1 - ku) = (1 - ku) * (1 - kv) * (Ou - Ov) := by
  linear_combination (-(1 - kv)) * hOu + (1 - ku) * hOv

/-- [proved-derived; formal-checked] **Two turns commute exactly when they share a pivot.** -/
theorem complex_moves_commute_iff_shared_pivot {ku kv bu bv Ou Ov : K} (hu : ku ≠ 1)
    (hv : kv ≠ 1) (hOu : (1 - ku) * Ou = bu) (hOv : (1 - kv) * Ov = bv) (z : K) :
    ku * (kv * z + bv) + bu = kv * (ku * z + bu) + bv ↔ Ou = Ov := by
  constructor
  · intro h
    have h0 : (1 - ku) * (1 - kv) * (Ou - Ov) = 0 := by
      linear_combination h + (1 - kv) * hOu - (1 - ku) * hOv
    rcases mul_eq_zero.mp h0 with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd (sub_eq_zero.mp h2).symm hu
      · exact absurd (sub_eq_zero.mp h2).symm hv
    · exact sub_eq_zero.mp h1
  · intro h
    linear_combination (-(1 - kv)) * hOu + (1 - ku) * hOv + (1 - ku) * (1 - kv) * h

end ComplexTorsion

/-! ## 2. One linear part, the Burgers vector and the base point -/

section AffineTorsion

variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- [proved-derived; formal-checked] **Moves with one linear part** leave the carry `(1 − M)(b₁ − b₂)`. -/
theorem move_same_linear_commutator (M : Module.End R V) (b₁ b₂ x : V) :
    move M b₁ (move M b₂ x) - move M b₂ (move M b₁ x) = (1 - M) (b₁ - b₂) := by
  simp only [move, map_add, LinearMap.sub_apply, Module.End.one_apply, map_sub]
  abel

/-- [proved-derived] **Curvature and torsion of a loop of two moves:** the loop leaves the
commutator of the turns on the state and the carry of the additions. -/
theorem move_commutator (Ma Mb : Module.End R V) (ba bb x : V) :
    move Mb bb (move Ma ba x) - move Ma ba (move Mb bb x) =
      (Mb * Ma - Ma * Mb) x + ((Mb - 1) ba - (Ma - 1) bb) := by
  simp only [move, map_add, LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply]
  abel

/-- [proved-derived; formal-checked] **The Burgers vector:** a loop of pure translations closes by the sum of
its carries. -/
theorem flat_loop_carry (bs : List V) (x : V) :
    bs.foldr (move (1 : Module.End R V)) x = x + bs.sum := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    rw [List.foldr_cons, ih, move, Module.End.one_apply, List.sum_cons]
    abel

/-- [proved-derived; formal-checked] **The carry needs its base point:** read from a base point shifted by `t`,
a move keeps its turn and its carry gains `M t − t`. -/
theorem move_basepoint (M : Module.End R V) (b t x : V) :
    move M b (x + t) - t = move M (b + (M t - t)) x := by
  rw [move, move, map_add]
  abel

/-- [proved-derived; formal-checked] A pure translation reads the same carry from every base point. -/
theorem translation_basepoint (b t x : V) :
    move (1 : Module.End R V) b (x + t) - t = move (1 : Module.End R V) b x := by
  rw [move_basepoint, Module.End.one_apply, sub_self, add_zero]

end AffineTorsion

/-! ## 2b. The lag-residue factorization -/

section LagResidue

variable {R V α : Type*} [Ring R] [AddCommGroup V] [Module R V]

/-- [definition] **A stream of moves with one linear part:** from `x₀`, each cell `k` applies `M`
and adds `E (u k)`. -/
def laggedRun (M : Module.End R V) (E : α → V) (u : ℕ → α) (x₀ : V) : ℕ → V
  | 0 => x₀
  | t + 1 => M (laggedRun M E u x₀ t) + E (u t)

/-- [proved-derived] **The stream's closed form:** `Mᵗ x₀ + Σ_(k < t) M^(t−1−k) E (u k)`. -/
theorem laggedRun_closed (M : Module.End R V) (E : α → V) (u : ℕ → α) (x₀ : V) (t : ℕ) :
    laggedRun M E u x₀ t = (M ^ t) x₀ + ∑ k ∈ Finset.range t, (M ^ (t - 1 - k)) (E (u k)) := by
  induction t with
  | zero => simp [laggedRun]
  | succ t ih =>
    have hstep : laggedRun M E u x₀ (t + 1) = M (laggedRun M E u x₀ t) + E (u t) := rfl
    have h1 : (M ^ (t + 1)) x₀ = M ((M ^ t) x₀) := by
      rw [pow_succ', Module.End.mul_apply]
    have h2 : ∀ k ∈ Finset.range t,
        M ((M ^ (t - 1 - k)) (E (u k))) = (M ^ (t + 1 - 1 - k)) (E (u k)) := by
      intro k hk
      have hk' : k < t := Finset.mem_range.mp hk
      have he : t + 1 - 1 - k = (t - 1 - k) + 1 := by omega
      rw [he, pow_succ', Module.End.mul_apply]
    have h3 : (M ^ (t + 1 - 1 - t)) (E (u t)) = E (u t) := by
      have he : t + 1 - 1 - t = 0 := by omega
      rw [he, pow_zero, Module.End.one_apply]
    rw [hstep, ih, map_add, map_sum, Finset.sum_range_succ, h1, Finset.sum_congr rfl h2, h3]
    abel

/-- [proved-derived] **The lag-residue factorization:** when `M^N = 1`, the stream's state is
`Mᵗ x₀ + Σ_(r < N) Σ_a n(a, r) • M^r E a`, where `n(a, r)` counts the cells `k < t` at lag residue
`(t − 1 − k) mod N = r` that carry symbol `a`. -/
theorem laggedRun_lag_residue [Fintype α] [DecidableEq α] (M : Module.End R V) (E : α → V)
    (u : ℕ → α) (x₀ : V) {N : ℕ} (hN : 0 < N) (hM : M ^ N = 1) (t : ℕ) :
    laggedRun M E u x₀ t = (M ^ t) x₀ +
      ∑ r ∈ Finset.range N, ∑ a : α,
        ((Finset.range t).filter (fun k => (t - 1 - k) % N = r ∧ u k = a)).card •
          (M ^ r) (E a) := by
  rw [laggedRun_closed]
  congr 1
  have hpow : ∀ k, M ^ (t - 1 - k) = M ^ ((t - 1 - k) % N) := by
    intro k
    conv_lhs => rw [← Nat.div_add_mod (t - 1 - k) N, pow_add, pow_mul, hM, one_pow, one_mul]
  have hsum : ∑ k ∈ Finset.range t, (M ^ (t - 1 - k)) (E (u k)) =
      ∑ k ∈ Finset.range t, (M ^ ((t - 1 - k) % N)) (E (u k)) :=
    Finset.sum_congr rfl (fun k _ => by rw [hpow k])
  have hmaps : ∀ k ∈ Finset.range t, (t - 1 - k) % N ∈ Finset.range N :=
    fun k _ => Finset.mem_range.mpr (Nat.mod_lt _ hN)
  rw [hsum, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [← Finset.sum_fiberwise _ u]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.filter_filter]
  have hc : ∀ k ∈ (Finset.range t).filter (fun k => (t - 1 - k) % N = r ∧ u k = a),
      (M ^ ((t - 1 - k) % N)) (E (u k)) = (M ^ r) (E a) := by
    intro k hk
    obtain ⟨-, h1, h2⟩ := Finset.mem_filter.mp hk
    rw [h1, h2]
  rw [Finset.sum_congr rfl hc, Finset.sum_const]

/-- [proved-derived] **Counts determine the state:** two streams with the same number of cells of
each symbol at each lag residue reach the same state, so every reading of a stream of moves with
one linear part of finite order is a function of its (symbol, lag residue) counts. -/
theorem laggedRun_eq_of_counts [Fintype α] [DecidableEq α] (M : Module.End R V) (E : α → V)
    (u w : ℕ → α) (x₀ : V) {N : ℕ} (hN : 0 < N) (hM : M ^ N = 1) (t : ℕ)
    (hc : ∀ r a, ((Finset.range t).filter (fun k => (t - 1 - k) % N = r ∧ u k = a)).card =
      ((Finset.range t).filter (fun k => (t - 1 - k) % N = r ∧ w k = a)).card) :
    laggedRun M E u x₀ t = laggedRun M E w x₀ t := by
  rw [laggedRun_lag_residue M E u x₀ hN hM, laggedRun_lag_residue M E w x₀ hN hM]
  simp_rw [hc]

end LagResidue

/-! ## 2c. Moves selected by the symbol, and their forward jet

When the symbol selects the linear part, `z' = λ_(t, s) z + β_(t, s)`, the stream is no longer a
function of lag-residue counts. Its derivative with respect to the move of one symbol `a` is carried
forward by the same moves (`lamJet`, `betaJet`): the phase-carried moment, whose adjoint needs no
tape. It is exact even when the moves change during the passage, as a derivative with respect to one
shift of `λ_(·, a)` (or `β_(·, a)`) at every cell, read in dual numbers `ε² = 0`. In any normed
ring the per-symbol bound `‖λ‖ ≤ ρ` bounds the state by `B / (1 − ρ)` and the jet by
`B / (1 − ρ)²`, and on the unit circle by `t B` and `B t (t − 1)/2`. Pairs of plane reflections
compose to turns that commute, so one plane cannot carry order. -/

section SelectedMoves

variable {S α : Type*} [Ring S]

/-- [definition] **A stream of moves selected by the symbol:** from rest, cell `t` applies the move
`z ↦ λ_(t, u t) z + β_(t, u t)` chosen by its symbol. -/
def selectedRun (lam beta : ℕ → α → S) (u : ℕ → α) : ℕ → S
  | 0 => 0
  | t + 1 => lam t (u t) * selectedRun lam beta u t + beta t (u t)

/-- [definition] **The forward jet of the turn of symbol `a`:** `J' = λ_(t, u t) J + [u t = a] z`. -/
def lamJet [DecidableEq α] (lam beta : ℕ → α → S) (u : ℕ → α) (a : α) : ℕ → S
  | 0 => 0
  | t + 1 => lam t (u t) * lamJet lam beta u a t +
      if u t = a then selectedRun lam beta u t else 0

/-- [definition] **The forward jet of the addition of symbol `a`:** `J' = λ_(t, u t) J + [u t = a]`. -/
def betaJet [DecidableEq α] (lam : ℕ → α → S) (u : ℕ → α) (a : α) : ℕ → S
  | 0 => 0
  | t + 1 => lam t (u t) * betaJet lam u a t + if u t = a then 1 else 0

/-- [proved-derived] The addition's jet is itself a selected stream, adding `1` on symbol `a`. -/
theorem betaJet_eq_selectedRun [DecidableEq α] (lam : ℕ → α → S) (u : ℕ → α) (a : α) (t : ℕ) :
    betaJet lam u a t = selectedRun lam (fun _ s => if s = a then 1 else 0) u t := by
  induction t with
  | zero => rfl
  | succ t ih => simp only [betaJet, selectedRun, ih]

end SelectedMoves

section SelectedJets

variable {S α : Type*} [CommRing S]

/-- [proved-derived] **The turn's forward jet is the exact derivative:** shifting the turn of symbol
`a` by `ε` at every cell, with `ε² = 0`, moves the stream by `ε` times the jet, also when the moves
change from cell to cell. -/
theorem lamJet_is_derivative [DecidableEq α] (lam beta : ℕ → α → S) (u : ℕ → α) (a : α) {ε : S}
    (hε : ε * ε = 0) (t : ℕ) :
    selectedRun (fun n s => lam n s + if s = a then ε else 0) beta u t =
      selectedRun lam beta u t + ε * lamJet lam beta u a t := by
  induction t with
  | zero => simp [selectedRun, lamJet]
  | succ t ih =>
    simp only [selectedRun, lamJet, ih]
    split_ifs with h
    · linear_combination lamJet lam beta u a t * hε
    · ring

/-- [proved-derived] **The addition's forward jet is the exact derivative** of the stream with
respect to the addition of symbol `a`; the stream is affine in its additions. -/
theorem betaJet_is_derivative [DecidableEq α] (lam beta : ℕ → α → S) (u : ℕ → α) (a : α) (ε : S)
    (t : ℕ) :
    selectedRun lam (fun n s => beta n s + if s = a then ε else 0) u t =
      selectedRun lam beta u t + ε * betaJet lam u a t := by
  induction t with
  | zero => simp [selectedRun, betaJet]
  | succ t ih =>
    simp only [selectedRun, betaJet, ih]
    split_ifs <;> ring

end SelectedJets

section SelectedBounds

variable {S α : Type*} [NormedRing S]

/-- [proved-derived] **The per-symbol bound certifies a scalar mode:** with `‖λ_(t, s)‖ ≤ ρ ≤ 1`
and `‖β_(t, s)‖ ≤ B` for every cell and symbol, `‖z_t‖ (1 − ρ) ≤ B`. For a scalar mode the
per-symbol bound is the joint bound: a word of the largest turn attains `ρⁿ`. -/
theorem selectedRun_norm_bound {lam beta : ℕ → α → S} (u : ℕ → α) {ρ B : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ1 : ρ ≤ 1) (hB : 0 ≤ B) (hlam : ∀ t s, ‖lam t s‖ ≤ ρ) (hbeta : ∀ t s, ‖beta t s‖ ≤ B)
    (t : ℕ) : ‖selectedRun lam beta u t‖ * (1 - ρ) ≤ B := by
  induction t with
  | zero => simp [selectedRun, hB]
  | succ t ih =>
    have h1 : ‖selectedRun lam beta u (t + 1)‖ ≤ ρ * ‖selectedRun lam beta u t‖ + B := by
      calc ‖selectedRun lam beta u (t + 1)‖
          = ‖lam t (u t) * selectedRun lam beta u t + beta t (u t)‖ := rfl
        _ ≤ ‖lam t (u t)‖ * ‖selectedRun lam beta u t‖ + ‖beta t (u t)‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
        _ ≤ ρ * ‖selectedRun lam beta u t‖ + B :=
            add_le_add (mul_le_mul_of_nonneg_right (hlam t (u t)) (norm_nonneg _))
              (hbeta t (u t))
    have h2 : 0 ≤ 1 - ρ := by linarith
    nlinarith [mul_le_mul_of_nonneg_right h1 h2, mul_le_mul_of_nonneg_left ih hρ0]

/-- [proved-derived] **The turn's jet is bounded by `B / (1 − ρ)²`:** `‖J_t‖ (1 − ρ)² ≤ B`, so the
jet's carrier needs twice the guard bits of the state's. -/
theorem lamJet_norm_bound [DecidableEq α] {lam beta : ℕ → α → S} (u : ℕ → α) (a : α) {ρ B : ℝ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hB : 0 ≤ B) (hlam : ∀ t s, ‖lam t s‖ ≤ ρ)
    (hbeta : ∀ t s, ‖beta t s‖ ≤ B) (t : ℕ) :
    ‖lamJet lam beta u a t‖ * (1 - ρ) ^ 2 ≤ B := by
  induction t with
  | zero => simp [lamJet, hB]
  | succ t ih =>
    have hz := selectedRun_norm_bound u hρ0 hρ1 hB hlam hbeta t
    have hite : ‖(if u t = a then selectedRun lam beta u t else 0)‖ ≤
        ‖selectedRun lam beta u t‖ := by
      split_ifs <;> simp
    have h1 : ‖lamJet lam beta u a (t + 1)‖ ≤
        ρ * ‖lamJet lam beta u a t‖ + ‖selectedRun lam beta u t‖ := by
      calc ‖lamJet lam beta u a (t + 1)‖
          = ‖lam t (u t) * lamJet lam beta u a t +
              (if u t = a then selectedRun lam beta u t else 0)‖ := rfl
        _ ≤ ‖lam t (u t)‖ * ‖lamJet lam beta u a t‖ +
              ‖(if u t = a then selectedRun lam beta u t else 0)‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
        _ ≤ ρ * ‖lamJet lam beta u a t‖ + ‖selectedRun lam beta u t‖ :=
            add_le_add (mul_le_mul_of_nonneg_right (hlam t (u t)) (norm_nonneg _)) hite
    have h2 : 0 ≤ 1 - ρ := by linarith
    have h3 : 0 ≤ (1 - ρ) ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right h1 h3, mul_le_mul_of_nonneg_left ih hρ0,
      mul_le_mul_of_nonneg_right hz h2]

/-- [proved-derived] **On the unit circle the state grows at most linearly:** with
`‖λ_(t, s)‖ ≤ 1` and `‖β_(t, s)‖ ≤ B`, `‖z_t‖ ≤ t B`, so it needs `log₂ t` guard bits. -/
theorem selectedRun_norm_le_linear {lam beta : ℕ → α → S} (u : ℕ → α) {B : ℝ}
    (hlam : ∀ t s, ‖lam t s‖ ≤ 1) (hbeta : ∀ t s, ‖beta t s‖ ≤ B) (t : ℕ) :
    ‖selectedRun lam beta u t‖ ≤ t * B := by
  induction t with
  | zero => simp [selectedRun]
  | succ t ih =>
    calc ‖selectedRun lam beta u (t + 1)‖
        = ‖lam t (u t) * selectedRun lam beta u t + beta t (u t)‖ := rfl
      _ ≤ ‖lam t (u t)‖ * ‖selectedRun lam beta u t‖ + ‖beta t (u t)‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
      _ ≤ 1 * (t * B) + B :=
          add_le_add (mul_le_mul (hlam t (u t)) ih (norm_nonneg _) zero_le_one) (hbeta t (u t))
      _ = ((t + 1 : ℕ) : ℝ) * B := by push_cast; ring

/-- [proved-derived] **On the unit circle the turn's jet grows at most quadratically:**
`2 ‖J_t‖ ≤ t (t − 1) B`, so it needs twice the state's guard bits there too. -/
theorem lamJet_norm_le_quadratic [DecidableEq α] {lam beta : ℕ → α → S} (u : ℕ → α) (a : α)
    {B : ℝ} (hlam : ∀ t s, ‖lam t s‖ ≤ 1) (hbeta : ∀ t s, ‖beta t s‖ ≤ B) (t : ℕ) :
    ‖lamJet lam beta u a t‖ * 2 ≤ (t : ℝ) * ((t : ℝ) - 1) * B := by
  induction t with
  | zero => simp [lamJet]
  | succ t ih =>
    have hz := selectedRun_norm_le_linear u hlam hbeta t
    have hite : ‖(if u t = a then selectedRun lam beta u t else 0)‖ ≤
        ‖selectedRun lam beta u t‖ := by
      split_ifs <;> simp
    have h1 : ‖lamJet lam beta u a (t + 1)‖ ≤
        ‖lamJet lam beta u a t‖ + ‖selectedRun lam beta u t‖ := by
      calc ‖lamJet lam beta u a (t + 1)‖
          = ‖lam t (u t) * lamJet lam beta u a t +
              (if u t = a then selectedRun lam beta u t else 0)‖ := rfl
        _ ≤ ‖lam t (u t)‖ * ‖lamJet lam beta u a t‖ +
              ‖(if u t = a then selectedRun lam beta u t else 0)‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) le_rfl)
        _ ≤ 1 * ‖lamJet lam beta u a t‖ + ‖selectedRun lam beta u t‖ :=
            add_le_add (mul_le_mul_of_nonneg_right (hlam t (u t)) (norm_nonneg _)) hite
        _ = ‖lamJet lam beta u a t‖ + ‖selectedRun lam beta u t‖ := by ring
    push_cast
    nlinarith [h1, hz, ih]

end SelectedBounds

section PlaneReflections

variable {S : Type*} [CommRing S] [StarRing S]

/-- [proved-derived] **Two plane reflections compose to a turn:** with `S_u z = u z̄`,
`S_u (S_v z) = (u v̄) z`. -/
theorem plane_reflections_compose (u v z : S) : u * star (v * star z) = (u * star v) * z := by
  rw [star_mul', star_star]
  ring

/-- [proved-derived] **One plane cannot carry order:** two turns made of pairs of plane reflections
commute, so a word of reflections in one plane reads only its parity and the signed sum of its
phases (the dihedral group), never the order of its letters. -/
theorem plane_turns_commute (u v u' v' z : S) :
    u * star (v * star (u' * star (v' * star z))) =
      u' * star (v' * star (u * star (v * star z))) := by
  simp only [star_mul', star_star]
  ring

end PlaneReflections

/-! ## 3. The fifth torsion, the redshift loop and the squeeze -/

/-- [proved-derived; formal-checked] **The fifth torsion is the field:** with `d₁ ∘ d₀ = 0`, the coboundary of the
frame `e⁵ = d₀ y + A` is the coboundary of `A`. -/
theorem fifth_torsion_is_field {U V W : Type*} [AddCommGroup U] [AddCommGroup V] [AddCommGroup W]
    (d₀ : U →+ V) (d₁ : V →+ W) (hdd : ∀ u, d₁ (d₀ u) = 0) (y : U) (A : V) :
    d₁ (d₀ y + A) = d₁ A := by
  rw [map_add, hdd, zero_add]

/-- [proved-derived; formal-checked] **The redshift loop:** summed over a grid of cells, the coboundary of the
time coframe is the product of the lapse difference and the clock difference across the grid. -/
theorem redshift_loop {A : Type*} [CommRing A] (N T : ℕ → A) (n m : ℕ) :
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range m, (N (i + 1) - N i) * (T (j + 1) - T j) =
      (N n - N 0) * (T m - T 0) := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_range_sub]

/-- [proved-derived; formal-checked] **The squeeze is the ratio's dilation:** `diag(λ, λ⁻¹)` on the undivided pair
`(a, b)` multiplies its ratio by `λ²`. -/
theorem squeeze_dilates_ratio {K : Type*} [Field K] (l a b : K) :
    (l * a) / (l⁻¹ * b) = l ^ 2 * (a / b) := by
  rw [div_eq_mul_inv, mul_inv, inv_inv]
  ring

end Holonics.Geometry.Motion
