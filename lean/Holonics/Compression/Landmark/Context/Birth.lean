import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.Matrix.Mul

/-!
# Birth: a reached separating covector founds an observable transport representation

[proved-derived] The founding law of `research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_
TERRAIN_DATA_AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md` §14.1 (atlas
`birth.separator-transport-closure`; THE_REBUILD's ring-search row, "residual-founded transport
discovery first"; Rust `receiver::population::birth`). In a finite chart `X` over a field, with the
admitted transports `T_a` known, a reached separating covector `λ_r` founds a representation:

```text
V₀ = V_old ⊔ span{λ_r},     V_(n+1) = V_n ⊔ Σ_a T_a* V_n          the founding ladder
λ_r ∉ V_old opens exactly one dimension                              (opening_finrank)
a strict step raises dim V_n, so at most dim X − dim V₀ of them      (strict_steps_le_chart)
one still step and every later step is still                         (ladder_stable_forever)
the stable rung V is T_a*-invariant and the least such space ⊇ V₀    (founded_invariant, founded_le)
basis φ_i of V, T_a* φ_i = Σ_j U_(a,ij) φ_j  ⇒  E T_a = U_a E,  E x = (φ_i x)_i   (founding_intertwines)
ρ ∈ V, ρ = Σ_j D_j φ_j  ⇒  ρ = D E                                   (encode_reads)
E Tᵗ = Uᵗ E, so ρ(Tᵗ x) = D Uᵗ E x: the founded family reads the chart  (encode_iterate, founded_reads_iterate)
forms silent on a T-closed orbit stay silent; a rational eigenvalue of a
  finite-order T* is ±1                                              (silent_invariant, eigenvalue_of_finite_order)
```

[proved-derived] **The founded dimension against the emission's minimal realization.** For `T` a
permutation of a finite state set, the span of the emission's shifts is the founded forms restricted
to the visited orbit, so its Hankel rank is that restriction's rank; the founded dimension exceeds
it by the forms silent on the orbit, an invariant space (`silent_invariant`) whose rational
eigenvectors are conserved charges or half-turns (`eigenvalue_of_finite_order`). The Hankel-rank
identification is owed (#62).

It constructs an observable transport representation. It does **not** infer an unknown `T_a`
([counterexample] no finite observation determines an unrestricted navigator family,
`Computation/NavigatorObservationScope`; learning an unknown finite-state transport needs
equivalence queries, which passive data does not supply).

The ladder is stated for any family of endomorphisms `S_a` of a vector space `W` (`ladder`,
`closeStep`); the founding reads it at `W = Dual K X`, `S_a = (T_a).dualMap`, since
`T_a* φ = φ ∘ T_a` (`LinearMap.dualMap_apply`). Its annihilator is the observability kernel of the
receiving forms (`Objects/RelativeCompleteness.observabilityKernel`, `Compression/Core/FaceMap`'s
horizon count, whose decreasing blind subspaces this increasing ladder dualizes).

The computational object is the helical pair interaction read at a receiver's birth. Of the winding
guide's six general objects this owner touches the **helix** (the admitted transports' windings,
here closed as maps of the chart), the **tube** (the ladder's rungs are the clocked span over which
the reached covector is transported) and **faces and placement** (the founded faces `φ_i` and the
readout `D`); the pair, the cell holonomy and the tower thread stay attached.
-/

namespace Holonics.Compression.Landmark.Context.Birth

open Module

section Ladder

variable {K W ι : Type*} [Field K] [AddCommGroup W] [Module K W]

/-- One closing step over the admitted maps: `V ↦ V ⊔ Σ_a S_a V`. -/
def closeStep (S : ι → W →ₗ[K] W) (V : Submodule K W) : Submodule K W :=
  V ⊔ ⨆ a, V.map (S a)

/-- The founding ladder `V₀, V₁, …`, each rung one closing step of the last. -/
def ladder (S : ι → W →ₗ[K] W) (V₀ : Submodule K W) : ℕ → Submodule K W
  | 0 => V₀
  | n + 1 => closeStep S (ladder S V₀ n)

variable (S : ι → W →ₗ[K] W) (V₀ : Submodule K W)

theorem le_closeStep (V : Submodule K W) : V ≤ closeStep S V := le_sup_left

theorem map_le_closeStep (V : Submodule K W) (a : ι) : V.map (S a) ≤ closeStep S V :=
  le_sup_of_le_right (le_iSup (fun a => V.map (S a)) a)

theorem ladder_zero : ladder S V₀ 0 = V₀ := rfl

theorem ladder_succ (n : ℕ) : ladder S V₀ (n + 1) = closeStep S (ladder S V₀ n) := rfl

/-- The rungs increase. -/
theorem ladder_mono : Monotone (ladder S V₀) :=
  monotone_nat_of_le_succ fun n => le_closeStep S (ladder S V₀ n)

/-- **A stable rung is invariant** under every admitted map. -/
theorem invariant_of_stable {V : Submodule K W} (h : closeStep S V = V) (a : ι) :
    V.map (S a) ≤ V :=
  (map_le_closeStep S V a).trans h.le

/-- **Once one step changes nothing, no later step does.** -/
theorem ladder_stable_forever {n : ℕ} (h : ladder S V₀ (n + 1) = ladder S V₀ n) :
    ∀ m, n ≤ m → ladder S V₀ m = ladder S V₀ n := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => rw [ladder_succ, ih, ← ladder_succ, h]

/-- **The ladder stays inside every invariant space containing its opening.** -/
theorem ladder_le_of_invariant {p : Submodule K W} (h₀ : V₀ ≤ p)
    (hp : ∀ a, p.map (S a) ≤ p) (n : ℕ) : ladder S V₀ n ≤ p := by
  induction n with
  | zero => exact h₀
  | succ n ih =>
    exact sup_le ih (iSup_le fun a => (Submodule.map_mono ih).trans (hp a))

variable [FiniteDimensional K W]

/-- **A strict step raises the dimension.** -/
theorem finrank_lt_of_strict {n : ℕ} (h : ladder S V₀ n ≠ ladder S V₀ (n + 1)) :
    finrank K (ladder S V₀ n) < finrank K (ladder S V₀ (n + 1)) :=
  Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne (ladder_mono S V₀ n.le_succ) h)

/-- `n` strict steps raise the dimension by at least `n`. -/
theorem finrank_add_le_of_strict {n : ℕ}
    (h : ∀ k < n, ladder S V₀ k ≠ ladder S V₀ (k + 1)) :
    finrank K V₀ + n ≤ finrank K (ladder S V₀ n) := by
  induction n with
  | zero => exact le_of_eq (by rw [Nat.add_zero, ladder_zero])
  | succ n ih =>
    have hlt := finrank_lt_of_strict S V₀ (h n (Nat.lt_succ_self n))
    have hle := ih fun k hk => h k (Nat.lt_succ_of_lt hk)
    omega

/-- **At most `dim W − dim V₀` strict steps.** -/
theorem strict_steps_le {n : ℕ} (h : ∀ k < n, ladder S V₀ k ≠ ladder S V₀ (k + 1)) :
    finrank K V₀ + n ≤ finrank K W :=
  (finrank_add_le_of_strict S V₀ h).trans (Submodule.finrank_le _)

/-- **The ladder stabilizes** at a rung reached after at most `dim W − dim V₀` strict steps: the
first rung that one step leaves unchanged. -/
theorem ladder_stabilizes :
    ∃ n, finrank K V₀ + n ≤ finrank K W ∧ ladder S V₀ (n + 1) = ladder S V₀ n := by
  classical
  have hex : ∃ k, ladder S V₀ k = ladder S V₀ (k + 1) := by
    by_contra hne
    push Not at hne
    have := strict_steps_le S V₀ (n := finrank K W + 1) fun k _ => hne k
    omega
  exact ⟨Nat.find hex, strict_steps_le S V₀ fun k hk => Nat.find_min hex hk,
    (Nat.find_spec hex).symm⟩

/-- **A separating covector opens one dimension**: `λ ∉ V_old` gives
`dim(V_old ⊔ span{λ}) = dim V_old + 1`. -/
theorem opening_finrank {Vold : Submodule K W} {lam : W} (h : lam ∉ Vold) :
    finrank K ↥(Vold ⊔ K ∙ lam) = finrank K Vold + 1 := by
  have hne : lam ≠ 0 := fun h0 => h (h0 ▸ Vold.zero_mem)
  have hdis : Disjoint Vold (K ∙ lam) := (Submodule.disjoint_span_singleton' hne).mpr h
  have := Submodule.finrank_sup_add_finrank_inf_eq Vold (K ∙ lam)
  rw [hdis.eq_bot, finrank_bot, finrank_span_singleton hne] at this
  omega

/-- **The founded forms**: the stable rung of the ladder. -/
noncomputable def founded : Submodule K W :=
  ladder S V₀ (Classical.choose (ladder_stabilizes S V₀))

theorem founded_stable : closeStep S (founded S V₀) = founded S V₀ :=
  (Classical.choose_spec (ladder_stabilizes S V₀)).2

/-- The founded forms are invariant under every admitted map. -/
theorem founded_invariant (a : ι) : (founded S V₀).map (S a) ≤ founded S V₀ :=
  invariant_of_stable S (founded_stable S V₀) a

/-- The founded forms contain the opening. -/
theorem le_founded : V₀ ≤ founded S V₀ :=
  ladder_mono S V₀ (Nat.zero_le _)

/-- **The founded forms are the least invariant space containing the opening.** -/
theorem founded_le {p : Submodule K W} (h₀ : V₀ ≤ p) (hp : ∀ a, p.map (S a) ≤ p) :
    founded S V₀ ≤ p :=
  ladder_le_of_invariant S V₀ h₀ hp _

/-- Every rung lies in the founded forms. -/
theorem ladder_le_founded (n : ℕ) : ladder S V₀ n ≤ founded S V₀ :=
  ladder_le_of_invariant S V₀ (le_founded S V₀) (founded_invariant S V₀) n

end Ladder

section Encoding

variable {K X ι r : Type*} [Field K] [AddCommGroup X] [Module K X] [Fintype r]

/-- **The founded encoding** `E x = (φ_i x)_i`. -/
def encode (φ : r → Dual K X) (x : X) : r → K := fun i => φ i x

/-- **The consumer equation**: `T_a* φ_i = Σ_j U_(a,ij) φ_j` gives `E T_a = U_a E`. -/
theorem encode_intertwines (T : ι → X →ₗ[K] X) (φ : r → Dual K X) (U : ι → Matrix r r K)
    (hU : ∀ a i, (T a).dualMap (φ i) = ∑ j, U a i j • φ j) (a : ι) (x : X) :
    encode φ (T a x) = (U a).mulVec (encode φ x) := by
  funext i
  have h := congrArg (fun f : Dual K X => f x) (hU a i)
  simp only [LinearMap.dualMap_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul] at h
  simp only [encode, Matrix.mulVec, dotProduct]
  exact h

/-- **The readout factors through the encoding**: a form `ρ = Σ_j D_j φ_j` reads `ρ = D E`. -/
theorem encode_reads (φ : r → Dual K X) (ρ : Dual K X) (D : r → K)
    (hD : ρ = ∑ j, D j • φ j) (x : X) : ρ x = ∑ j, D j * encode φ x j := by
  subst hD
  simp [encode]

/-- **The encoding carries every tick**: `E T = U E` gives `E Tᵗ = Uᵗ E`. -/
theorem encode_iterate [DecidableEq r] (T : X →ₗ[K] X) (φ : r → Dual K X) (U : Matrix r r K)
    (hU : ∀ x, encode φ (T x) = U.mulVec (encode φ x)) (t : ℕ) (x : X) :
    encode φ (T^[t] x) = (U ^ t).mulVec (encode φ x) := by
  induction t generalizing x with
  | zero => simp
  | succ t ih =>
    rw [Function.iterate_succ_apply, ih, hU, pow_succ, ← Matrix.mulVec_mulVec]

/-- **The founded family reads the transported state**: with `E T = U E` and `ρ = D E`, the reading
after `t` ticks is `ρ(Tᵗ x) = D Uᵗ E x`, so a family carried in the founded chart emits exactly the
chart's readings. -/
theorem founded_reads_iterate [DecidableEq r] (T : X →ₗ[K] X) (φ : r → Dual K X)
    (U : Matrix r r K)
    (hU : ∀ x, encode φ (T x) = U.mulVec (encode φ x)) (ρ : Dual K X) (D : r → K)
    (hD : ρ = ∑ j, D j • φ j) (t : ℕ) (x : X) :
    ρ (T^[t] x) = ∑ j, D j * (U ^ t).mulVec (encode φ x) j := by
  rw [encode_reads φ ρ D hD, encode_iterate T φ U hU t x]

/-- **A form silent on a visited orbit stays silent**: when `T` carries the set `O` into itself,
`T*` carries a form vanishing on `O` to a form vanishing on `O`. So the founded forms silent on the
visited orbit are an invariant space, and the founded dimension exceeds the emission's
minimal realization exactly by it. -/
theorem silent_invariant (T : X →ₗ[K] X) {O : Set X} (hO : ∀ x ∈ O, T x ∈ O)
    {v : Dual K X} (hv : ∀ x ∈ O, v x = 0) : ∀ x ∈ O, T.dualMap v x = 0 := fun x hx => by
  rw [LinearMap.dualMap_apply]
  exact hv _ (hO x hx)

/-- **A rational eigenvalue of a finite-order transport is `±1`**: a silent form `T* v = μ v`
under `Tᴸ = 1` is a conserved charge (`μ = 1`) or a half-turn on each orbit (`μ = −1`, `L` even). -/
theorem eigenvalue_of_finite_order {μ : ℚ} {L : ℕ} (hL : 0 < L) (h : μ ^ L = 1) :
    μ = 1 ∨ (μ = -1 ∧ Even L) := by
  rcases pow_eq_one_iff_cases.mp h with h0 | h1 | h2
  · omega
  · exact Or.inl h1
  · exact Or.inr h2

/-- **The transport matrices exist** on any basis of an invariant space of forms. -/
theorem exists_transport_matrices (T : ι → X →ₗ[K] X) {V : Submodule K (Dual K X)}
    (hV : ∀ a, V.map (T a).dualMap ≤ V) (b : Basis r K V) :
    ∃ U : ι → Matrix r r K,
      ∀ a i, (T a).dualMap (b i) = ∑ j, U a i j • (b j : Dual K X) := by
  have hmem : ∀ a i, (T a).dualMap (b i) ∈ V := fun a i =>
    hV a (Submodule.mem_map_of_mem (b i).2)
  refine ⟨fun a i j => b.repr ⟨(T a).dualMap (b i), hmem a i⟩ j, fun a i => ?_⟩
  have h := congrArg Subtype.val (b.sum_repr ⟨(T a).dualMap (b i), hmem a i⟩)
  simp only [Submodule.coe_sum, Submodule.coe_smul] at h
  exact h.symm

/-- **The founding law.** Close `V_old ⊔ span{λ_r}` under the transports' adjoints; on any basis
of the founded forms there are matrices `U_a` with `E T_a = U_a E`. -/
theorem founding_intertwines [FiniteDimensional K X] (T : ι → X →ₗ[K] X)
    (Vold : Submodule K (Dual K X)) (lam : Dual K X)
    (b : Basis r K (founded (fun a => (T a).dualMap) (Vold ⊔ K ∙ lam))) :
    ∃ U : ι → Matrix r r K, ∀ a x,
      encode (fun i => (b i : Dual K X)) (T a x) =
        (U a).mulVec (encode (fun i => (b i : Dual K X)) x) := by
  obtain ⟨U, hU⟩ := exists_transport_matrices T
    (founded_invariant (fun a => (T a).dualMap) (Vold ⊔ K ∙ lam)) b
  exact ⟨U, fun a x => encode_intertwines T _ U hU a x⟩

/-- **At most `dim X` strict steps**: the dual chart has the chart's dimension. -/
theorem strict_steps_le_chart [FiniteDimensional K X] (T : ι → X →ₗ[K] X)
    (V₀ : Submodule K (Dual K X)) {n : ℕ}
    (h : ∀ k < n, ladder (fun a => (T a).dualMap) V₀ k ≠
      ladder (fun a => (T a).dualMap) V₀ (k + 1)) :
    finrank K V₀ + n ≤ finrank K X := by
  have := strict_steps_le (fun a => (T a).dualMap) V₀ h
  rwa [Subspace.dual_finrank_eq] at this

/-- The reached covector lies in the founded forms, and so does every old form. -/
theorem separator_mem_founded (T : ι → X →ₗ[K] X) (Vold : Submodule K (Dual K X))
    (lam : Dual K X) [FiniteDimensional K X] :
    lam ∈ founded (fun a => (T a).dualMap) (Vold ⊔ K ∙ lam) ∧
      Vold ≤ founded (fun a => (T a).dualMap) (Vold ⊔ K ∙ lam) :=
  ⟨le_founded _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self lam)),
    le_sup_left.trans (le_founded _ _)⟩

end Encoding

end Holonics.Compression.Landmark.Context.Birth
