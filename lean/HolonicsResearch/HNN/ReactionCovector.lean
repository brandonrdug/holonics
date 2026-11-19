import Mathlib

/-!
# A reader's reaction at its founding: the strength's covector is the adjoint of the stage it adds

[proved-derived; formal-checked] The junction record of November 13
(`research/records/2026-11-13_THE_TICK_HOLDS_THE_JUNCTIONS_ANCHOR_WITHOUT_ITS_RETURN_…`, §13 and §13.8; the reading
G158; atlas `tower.field-reaction-mirror`) founds a reader's reaction on its source at strength zero: after tick `k`
every source place `j` takes `x_j ← x_j − κ ρ_j^k`, `ρ^k` the reaction's route read at the tick's state, and the record
writes the code's derivative as `d(code)/dκ = −Σ_k A^k`, `A^k = Σ_j Re⟨λ_j^(k+1), ρ_j^k⟩`, `λ^(k+1)` the reverse's
covector on the state after tick `k`. #410 owes the adjoint identity by the chain rule, in the record's generality.

The chart. A state lies in a real normed space `E`. Tick `k` is any map `T_k` (the heads' reads, the junction, the
return: every stage of the tick, the other readers' strengths held). The route is any map `R_k` of the state the tick
read, `ρ^k = R_k(x^k)`; a route that also reads the tick's output `T_k(x^k)`, as the record's `O_hᵀ x_i^(k+1)` does, is
`x ↦ R′_k(x, T_k x)`, one such map. The code is any map `Φ` of the last state; a code read at every tick is the last
read of a state that carries its running sum (`agent-inferred`). The forward is `x^(k+1) = T_k(x^k) − κ ρ^k` (`traj`).

What is proved, for `T_k` differentiable and `R_k` continuous along the founding's orbit and `Φ` differentiable at its
end.

1. **Founded at zero the forward is the source's** (`traj_zero`): at `κ = 0` the orbit is the ticks' own (`base`).
2. **The reaction's own term** (`hasDerivAt_smul_self`): `κ ρ(κ)` has derivative `ρ(0)` at `κ = 0` whenever `ρ` is
   continuous there, whatever its own dependence on `κ`.
3. **The orbit's tangent** (`hasDerivAt_traj`, `tangent_eq`): `dx^n/dκ` at the founding obeys `v^0 = 0`,
   `v^(k+1) = DT_k v^k − ρ^k` (`tangent`), and is `−Σ_(k<n) P_(k+1→n) ρ^k`, `P_(m→n) = DT_(n−1) ⋯ DT_m` (`prop`) the
   linearized ticks from `m` to `n`.
4. **The reverse** (`adj`, `adj_last`, `adj_step`): `λ^n = Φ′ ∘ P_(n→N)` is the covector on the state after tick
   `n − 1`, with `λ^N = Φ′` and `λ^n = λ^(n+1) ∘ DT_n` for `n < N`, the sweep the engine's reverse runs.
5. **The strength's covector** (`hasDerivAt_code`): `d(code)/dκ` at the founding is `−Σ_(k<N) λ^(k+1)(ρ^k)`, the
   record's `−Σ_k A^k`. The box's `Σ_k λ^(k+1)(ρ^k)` is the descent covector `−d(code)/dκ` (`hasDerivAt_neg_code`),
   the sign with which a deposit moves `κ`.
6. **By places** (`apply_eq_sum_inner`, `hasDerivAt_code_inner`): on a state of places `ι → V`, `V` a real inner product
   space, `λ^(k+1)(ρ^k) = Σ_j ⟨γ_j^(k+1), ρ_j^k⟩` with `γ_j^(k+1)` the covector's gradient at place `j` (`gradAt`), so
   `d(code)/dκ = −Σ_k Σ_j ⟨γ_j^(k+1), ρ_j^k⟩`. On `ℂ` as a real inner product space `⟨a, b⟩ = Re(conj(a) b)`, the
   record's `Re⟨λ_j^(k+1), ρ_j^k⟩`; a place the reaction does not write has `ρ_j = 0`.

Not claimed. The pair's passivity (`κ m² < 4`), the read's sign as a turn or a boost, the second order in `κ`, and the
realization's releases are not stated here; the Rust owners (`Field::tick_return`'s value route,
`Constitution::mirror_route`) and the line's reading G158 are not tied to these statements.

The computational object is the helical pair interaction: the reaction runs a pair contact's read back from the reader
to its source, and its strength's covector is what the reverse carries through every later tick. Of the winding guide's
six general objects this touches the pair (the reaction's route through the contacts), the tube (the ticks as a clocked
span) and faces and placement (the code's covector on the state); the helix, cell holonomy and tower thread stay
attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.HNN.ReactionCovector

open Filter Topology
open scoped InnerProductSpace

section Forward

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- [definition] The ticks' own orbit. -/
def base (T : ℕ → E → E) (x₀ : E) : ℕ → E
  | 0 => x₀
  | k + 1 => T k (base T x₀ k)

/-- [definition] The forward with the reaction at strength `κ`: `x^(k+1) = T_k(x^k) − κ R_k(x^k)`. -/
def traj (T R : ℕ → E → E) (x₀ : E) (κ : ℝ) : ℕ → E
  | 0 => x₀
  | k + 1 => T k (traj T R x₀ κ k) - κ • R k (traj T R x₀ κ k)

/-- [proved-standard; formal-checked] **Founded at zero the forward is the source's.** -/
theorem traj_zero (T R : ℕ → E → E) (x₀ : E) (n : ℕ) : traj T R x₀ 0 n = base T x₀ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [traj, base, ih]

/-- [definition] The linearized ticks from `m` to `n`, `P_(m→n) = DT_(n−1) ⋯ DT_m` (the identity for `n ≤ m`). -/
def prop (DT : ℕ → E →L[ℝ] E) (m : ℕ) : ℕ → E →L[ℝ] E
  | 0 => ContinuousLinearMap.id ℝ E
  | n + 1 => if m ≤ n then (DT n).comp (prop DT m n) else ContinuousLinearMap.id ℝ E

theorem prop_self (DT : ℕ → E →L[ℝ] E) (m : ℕ) : prop DT m m = ContinuousLinearMap.id ℝ E := by
  cases m with
  | zero => rfl
  | succ m => simp [prop]

theorem prop_succ (DT : ℕ → E →L[ℝ] E) {m n : ℕ} (h : m ≤ n) : prop DT m (n + 1) = (DT n).comp (prop DT m n) := by
  simp [prop, h]

/-- The linearized ticks factor at their first tick. -/
theorem prop_succ_left (DT : ℕ → E →L[ℝ] E) {m n : ℕ} (h : m + 1 ≤ n) :
    prop DT m n = (prop DT (m + 1) n).comp (DT m) := by
  induction n, h using Nat.le_induction with
  | base =>
    rw [prop_succ DT le_rfl, prop_self, prop_self, ContinuousLinearMap.comp_id, ContinuousLinearMap.id_comp]
  | succ n hmn ih =>
    rw [prop_succ DT (by omega), ih, prop_succ DT hmn, ContinuousLinearMap.comp_assoc]

/-- [definition] The orbit's tangent at the founding: `v^0 = 0`, `v^(k+1) = DT_k v^k − ρ^k`. -/
def tangent (T R : ℕ → E → E) (DT : ℕ → E →L[ℝ] E) (x₀ : E) : ℕ → E
  | 0 => 0
  | k + 1 => DT k (tangent T R DT x₀ k) - R k (base T x₀ k)

/-- [proved-standard; formal-checked] **The reaction's own term**: `κ ρ(κ)` has derivative `ρ(0)` at the founding
whenever `ρ` is continuous there. -/
theorem hasDerivAt_smul_self {φ : ℝ → E} (hφ : ContinuousAt φ 0) :
    HasDerivAt (fun κ : ℝ => κ • φ κ) (φ 0) 0 := by
  rw [hasDerivAt_iff_isLittleO]
  have h1 : (fun κ : ℝ => φ κ - φ 0) =o[𝓝 0] (fun _ => (1 : ℝ)) := by
    rw [Asymptotics.isLittleO_one_iff]
    have := hφ.tendsto.sub_const (φ 0)
    rwa [sub_self] at this
  refine ((Asymptotics.isBigO_refl (fun κ : ℝ => κ) (𝓝 0)).smul_isLittleO h1).congr (fun κ => ?_) (fun κ => ?_)
  · simp [smul_sub]
  · simp

/-- [proved-derived; formal-checked] **The orbit's tangent**: `dx^n/dκ` at the founding is `v^n`. -/
theorem hasDerivAt_traj (T R : ℕ → E → E) (DT : ℕ → E →L[ℝ] E) (x₀ : E)
    (hT : ∀ k, HasFDerivAt (T k) (DT k) (base T x₀ k)) (hR : ∀ k, ContinuousAt (R k) (base T x₀ k)) (n : ℕ) :
    HasDerivAt (fun κ => traj T R x₀ κ n) (tangent T R DT x₀ n) 0 := by
  induction n with
  | zero => exact hasDerivAt_const (0 : ℝ) x₀
  | succ n ih =>
    have hTn := hT n
    rw [← traj_zero T R x₀ n] at hTn
    have h1 : HasDerivAt (fun κ => T n (traj T R x₀ κ n)) (DT n (tangent T R DT x₀ n)) 0 :=
      hTn.comp_hasDerivAt (0 : ℝ) ih
    have hc : ContinuousAt (fun κ => R n (traj T R x₀ κ n)) 0 :=
      (hR n).comp_of_eq ih.continuousAt (traj_zero T R x₀ n)
    have h2 := hasDerivAt_smul_self hc
    rw [traj_zero] at h2
    exact h1.sub h2

/-- [proved-derived; formal-checked] **The tangent unrolled**: `v^n = −Σ_(k<n) P_(k+1→n) ρ^k`. -/
theorem tangent_eq (T R : ℕ → E → E) (DT : ℕ → E →L[ℝ] E) (x₀ : E) (n : ℕ) :
    tangent T R DT x₀ n = -∑ k ∈ Finset.range n, prop DT (k + 1) n (R k (base T x₀ k)) := by
  induction n with
  | zero => simp [tangent]
  | succ n ih =>
    rw [tangent, ih, Finset.sum_range_succ, prop_self, map_neg, map_sum]
    have h : ∀ k ∈ Finset.range n, DT n (prop DT (k + 1) n (R k (base T x₀ k)))
        = prop DT (k + 1) (n + 1) (R k (base T x₀ k)) := fun k hk => by
      rw [prop_succ DT (Finset.mem_range.mp hk)]
      rfl
    rw [Finset.sum_congr rfl h, ContinuousLinearMap.id_apply]
    abel

/-- [definition] The reverse's covector on the state after tick `n − 1`, `λ^n = Φ′ ∘ P_(n→N)`. -/
def adj (Φ' : E →L[ℝ] ℝ) (DT : ℕ → E →L[ℝ] E) (N n : ℕ) : E →L[ℝ] ℝ := Φ'.comp (prop DT n N)

/-- The reverse starts at the code's covector, `λ^N = Φ′`. -/
theorem adj_last (Φ' : E →L[ℝ] ℝ) (DT : ℕ → E →L[ℝ] E) (N : ℕ) : adj Φ' DT N N = Φ' := by
  rw [adj, prop_self, ContinuousLinearMap.comp_id]

/-- [proved-standard; formal-checked] **The reverse's step**: `λ^n = λ^(n+1) ∘ DT_n` for `n < N`. -/
theorem adj_step (Φ' : E →L[ℝ] ℝ) (DT : ℕ → E →L[ℝ] E) {N n : ℕ} (h : n < N) :
    adj Φ' DT N n = (adj Φ' DT N (n + 1)).comp (DT n) := by
  rw [adj, adj, prop_succ_left DT h, ContinuousLinearMap.comp_assoc]

/-- [proved-derived; formal-checked] **The strength's covector**: at the founding,
`d(code)/dκ = −Σ_(k<N) λ^(k+1)(ρ^k)`, the record's `−Σ_k A^k`. -/
theorem hasDerivAt_code (T R : ℕ → E → E) (DT : ℕ → E →L[ℝ] E) (x₀ : E) (Φ : E → ℝ) (Φ' : E →L[ℝ] ℝ) (N : ℕ)
    (hT : ∀ k, HasFDerivAt (T k) (DT k) (base T x₀ k)) (hR : ∀ k, ContinuousAt (R k) (base T x₀ k))
    (hΦ : HasFDerivAt Φ Φ' (base T x₀ N)) :
    HasDerivAt (fun κ => Φ (traj T R x₀ κ N))
      (-∑ k ∈ Finset.range N, adj Φ' DT N (k + 1) (R k (base T x₀ k))) 0 := by
  rw [← traj_zero T R x₀ N] at hΦ
  refine (hΦ.comp_hasDerivAt (0 : ℝ) (hasDerivAt_traj T R DT x₀ hT hR N)).congr_deriv ?_
  rw [tangent_eq, map_neg, map_sum]
  rfl

/-- The box's sum is the descent covector: `−d(code)/dκ = Σ_(k<N) λ^(k+1)(ρ^k)`. -/
theorem hasDerivAt_neg_code (T R : ℕ → E → E) (DT : ℕ → E →L[ℝ] E) (x₀ : E) (Φ : E → ℝ) (Φ' : E →L[ℝ] ℝ)
    (N : ℕ) (hT : ∀ k, HasFDerivAt (T k) (DT k) (base T x₀ k)) (hR : ∀ k, ContinuousAt (R k) (base T x₀ k))
    (hΦ : HasFDerivAt Φ Φ' (base T x₀ N)) :
    HasDerivAt (fun κ => -Φ (traj T R x₀ κ N))
      (∑ k ∈ Finset.range N, adj Φ' DT N (k + 1) (R k (base T x₀ k))) 0 :=
  (hasDerivAt_code T R DT x₀ Φ Φ' N hT hR hΦ).neg.congr_deriv (neg_neg _)

end Forward

/-! ## By places -/

section Places

variable {ι V : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]

/-- [definition] A covector's gradient at place `j`: `γ_j` with `L(e_j w) = ⟨γ_j, w⟩`. -/
noncomputable def gradAt (L : (ι → V) →L[ℝ] ℝ) (j : ι) : V :=
  (InnerProductSpace.toDual ℝ V).symm (L.comp (ContinuousLinearMap.single ℝ (fun _ : ι => V) j))

/-- A covector on the places is the sum of its gradients' pairings, `L(d) = Σ_j ⟨γ_j, d_j⟩`. -/
theorem apply_eq_sum_inner (L : (ι → V) →L[ℝ] ℝ) (d : ι → V) : L d = ∑ j, ⟪gradAt L j, d j⟫_ℝ := by
  conv_lhs => rw [← Finset.univ_sum_single d]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [gradAt, InnerProductSpace.toDual_symm_apply]
  rfl

/-- [proved-derived; formal-checked] **The record's form**: `d(code)/dκ = −Σ_k Σ_j ⟨γ_j^(k+1), ρ_j^k⟩`. -/
theorem hasDerivAt_code_inner (T R : ℕ → (ι → V) → ι → V) (DT : ℕ → (ι → V) →L[ℝ] ι → V) (x₀ : ι → V)
    (Φ : (ι → V) → ℝ) (Φ' : (ι → V) →L[ℝ] ℝ) (N : ℕ)
    (hT : ∀ k, HasFDerivAt (T k) (DT k) (base T x₀ k)) (hR : ∀ k, ContinuousAt (R k) (base T x₀ k))
    (hΦ : HasFDerivAt Φ Φ' (base T x₀ N)) :
    HasDerivAt (fun κ => Φ (traj T R x₀ κ N))
      (-∑ k ∈ Finset.range N, ∑ j, ⟪gradAt (adj Φ' DT N (k + 1)) j, R k (base T x₀ k) j⟫_ℝ) 0 :=
  (hasDerivAt_code T R DT x₀ Φ Φ' N hT hR hΦ).congr_deriv
    (congr_arg Neg.neg (Finset.sum_congr rfl fun _ _ => apply_eq_sum_inner _ _))

end Places

end Holonics.HNN.ReactionCovector
