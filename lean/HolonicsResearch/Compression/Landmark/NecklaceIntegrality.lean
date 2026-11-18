import Holonics.Compression.Landmark.PrimitiveCycle
import Mathlib

/-!
# Necklace integrality: the primitive cycles of a general return map are the primitive cycles of rotation

[proved-derived] The source is #410's box "Necklace integrality and the infinite Euler product for a general nonnegative
integer return map", left by `Holonics/Compression/Landmark/PrimitiveCycle` (its closing `[open]` paragraph), which owns
the case of a map of a finite set of occurrences (atlas `landmark.primitive-cycle-count`, `landmark.euler-product`).

A general return map is a square matrix `M` of natural numbers: `M a b` parallel edges from `a` to `b` (`Edge`). A
closed aeon of `n` epochs is a closed walk of `n` edges, held here as a cyclic word `ℤ/n → edges` whose every edge ends
where the next begins (`Loop`). Rotation by one place is a map of that finite set (`rot`). The whole of this module is
that the general case is the owner's case read on rotation: the owner's counting identity (`periodic_count`), its count
of the occurrences a cycle carries (`card_minimalPeriod_eq`) and its logarithmic derivatives are applied to `rot`, and
nothing of them is proved again.

What is proved.

1. **The trace of a power is a sum over cyclic words** over any commutative semiring: an open form with free ends
   (`sum_path_weight`) and the closed form `tr(A^(k+1)) = Σ_v ∏_i A (v i) (v (i+1))` (`trace_pow_succ_eq_sum_cyclic`).
2. **The closed walks of `n` edges number `tr(Mⁿ)`** (`card_between`, `card_cyclic_words`, `card_loop`).
3. **A closed walk fixed by a rotation of `d` places is a closed walk of `d` edges repeated** (`rep`,
   `exists_rep_of_periodic`), repetition keeps the least period under rotation (`minimalPeriod_rep`), and so the walks
   of `n` edges of least period `d` are as many as the walks of `d` edges of least period `d`
   (`card_minimalPeriod_rep`).
4. **The counting identity**: `tr(Mⁿ) = Σ_(d ∣ n) d · p_d` for every `n ≥ 1`, with `p_d` the number of rotation orbits
   of least period `d` among the closed walks of `d` edges (`necklaceCount`, `necklaceCount_eq_card_orbits`,
   `card_primitive_loops`, `trace_pow_eq_sum_necklace`).
5. **Necklace integrality**: `Σ_(d ∣ n) μ(n/d) · tr(M^d) = n · p_n` (`necklace_integrality`, with the antidiagonal form
   `necklace_moebius`), so `n` divides the Möbius sum (`necklace_dvd`), the sum is nonnegative (`necklace_nonneg`) and
   `p_n` is its quotient (`necklaceCount_eq_div`). For an integer matrix with nonnegative entries the same holds
   (`necklace_dvd_of_nonneg`).
6. **The Euler product, coefficient by coefficient**: every coefficient of the transfer determinant `det(1 − T·M)` of
   order at most `N` is the coefficient of `∏_(d = 1)^N (1 − T^d)^(p_d)` (`euler_product_coeff`), by a uniqueness of
   power series from their logarithmic derivatives below an order (`coeff_eq_of_logDeriv_agree`). The product over every
   length is the limit this names: each coefficient is reached at `N` equal to its order and stays.
7. **The owner's case is the restriction to a map**: on the `0/1` matrix of a map of occurrences the count is the
   owner's count of periodic orbits (`mapMatrixNat`, `mapMatrixNat_cast`, `necklaceCount_mapMatrixNat`).
8. **Rulers.** One place with two loops, `[[2]]`, has `p_1, …, p_6 = 2, 1, 2, 3, 6, 9`, the counts of primitive binary
   necklaces (`ruler_two_loops`); the golden-mean shift `[[1, 1], [1, 0]]` has `1, 1, 1, 1, 2, 2`
   (`ruler_golden_mean`).

Limits. The product with infinitely many factors is stated through its coefficients, statement 6; it is not built as
one power series (a limit in the topology of coefficients, or the join to `Aeon/Production/Zeta.zeta_eq_exp` as
`exp(Σ_n N_n Tⁿ/n) · ∏_d (1 − T^d)^(p_d) = 1`), and that object is still to be written. Divisibility by `n` holds for
every integer matrix, signed ones included (the literature's Gauss congruence for traces); only the nonnegative case is
proved here, and for a signed matrix the quotient is no count (`PrimitiveCycle.signed_map_has_no_primitive_cycles`).

The computational object is the helical pair interaction: an edge is a pair contact, a closed walk a closed chain of
contacts, and rotation the helix's advance by one place along it. Of the winding guide's six general objects this
touches the helix (rotation and its least period), cell holonomy (a closed walk) and the tower thread (a walk of `d`
edges read at every multiple of `d`); the pair, faces and placement and the tube stay attached.

Consumers: #410's box on necklace integrality; atlas `landmark.primitive-cycle-count` and `landmark.euler-product`,
whose scope this widens from a map's matrix to every matrix of natural numbers.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Compression.Landmark.NecklaceIntegrality

open Finset Function
open Holonics.Compression.Landmark.PrimitiveCycle

/-! ## 1. The trace of a power is a sum over cyclic words -/

section Trace

variable {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommSemiring R]

omit [Fintype V] [DecidableEq V] in
private theorem snoc_zero_eq {k : ℕ} (u : Fin (k + 1) → V) (c : V) :
    (Fin.snoc (α := fun _ : Fin (k + 2) => V) u c) 0 = u 0 := by
  have h : (0 : Fin (k + 2)) = Fin.castSucc (0 : Fin (k + 1)) := rfl
  rw [h, Fin.snoc_castSucc]

/-- [proved-standard] **A power's entries weigh the open words between them**: for every reading `F` of a word's two
ends, the words `v₀, …, v_k` weighted by `∏ A (v_i) (v_(i+1))` sum to `Σ_(a, b) (A^k) a b · F a b`. -/
theorem sum_path_weight (A : Matrix V V R) (k : ℕ) (F : V → V → R) :
    ∑ v : Fin (k + 1) → V, (∏ i : Fin k, A (v i.castSucc) (v i.succ)) * F (v 0) (v (Fin.last k)) =
      ∑ a, ∑ b, (A ^ k) a b * F a b := by
  induction k generalizing F with
  | zero =>
    have h1 : ∀ v : Fin 1 → V,
        (∏ i : Fin 0, A (v i.castSucc) (v i.succ)) * F (v 0) (v (Fin.last 0)) = F (v 0) (v 0) := by
      intro v
      simp
    simp_rw [h1, pow_zero, Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true]
    exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) V) _ _ (fun v => by simp)
  | succ k ih =>
    rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (k + 2) => V)), Fintype.sum_prod_type, Finset.sum_comm]
    have hterm : ∀ (u : Fin (k + 1) → V) (c : V),
        (∏ i : Fin (k + 1), A ((Fin.snocEquiv (fun _ : Fin (k + 2) => V)) (c, u) i.castSucc)
            ((Fin.snocEquiv (fun _ : Fin (k + 2) => V)) (c, u) i.succ)) *
          F ((Fin.snocEquiv (fun _ : Fin (k + 2) => V)) (c, u) 0)
            ((Fin.snocEquiv (fun _ : Fin (k + 2) => V)) (c, u) (Fin.last (k + 1))) =
        (∏ i : Fin k, A (u i.castSucc) (u i.succ)) * (A (u (Fin.last k)) c * F (u 0) c) := by
      intro u c
      have hs : (Fin.snocEquiv (fun _ : Fin (k + 2) => V)) (c, u) =
          Fin.snoc (α := fun _ : Fin (k + 2) => V) u c := rfl
      rw [hs, Fin.prod_univ_castSucc, snoc_zero_eq, Fin.snoc_last, Fin.succ_last, Fin.snoc_last,
        Fin.snoc_castSucc]
      simp only [Fin.succ_castSucc, Fin.snoc_castSucc]
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    rw [ih fun a b => ∑ c, A b c * F a c]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp_rw [pow_succ, Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => ?_
    ring

/-- [proved-standard] **The trace of a power is a sum over cyclic words**:
`tr(A^(k+1)) = Σ_v ∏_i A (v i) (v (i+1))`, the index read on the circle of `k + 1` places. -/
theorem trace_pow_succ_eq_sum_cyclic (A : Matrix V V R) (k : ℕ) :
    (A ^ (k + 1)).trace = ∑ v : Fin (k + 1) → V, ∏ i : Fin (k + 1), A (v i) (v (i + 1)) := by
  have htr : (A ^ (k + 1)).trace = ∑ a, ∑ b, (A ^ k) a b * A b a := by
    simp [Matrix.trace, pow_succ, Matrix.mul_apply]
  rw [htr, ← sum_path_weight A k fun a b => A b a]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Fin.prod_univ_castSucc]
  simp [Fin.coeSucc_eq_succ]

end Trace

/-! ## 2. Closed walks as cyclic words -/

section Walks

variable {V : Type*}

/-- An edge of the return map's multigraph: one of the `M src tgt` parallel edges from `src` to `tgt`. -/
structure Edge (M : Matrix V V ℕ) where
  /-- The place the edge leaves. -/
  src : V
  /-- The place the edge reaches. -/
  tgt : V
  /-- Which of the `M src tgt` parallel edges it is. -/
  idx : Fin (M src tgt)

/-- The edges in their sigma chart. -/
def Edge.equivSigma (M : Matrix V V ℕ) : Edge M ≃ Σ a : V, Σ b : V, Fin (M a b) where
  toFun e := ⟨e.src, e.tgt, e.idx⟩
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {M : Matrix V V ℕ}

/-- A closed walk of `n` edges: a cyclic word of edges, each ending where the next begins. -/
abbrev Loop (M : Matrix V V ℕ) (n : ℕ) : Type _ := {w : ZMod n → Edge M // ∀ i, (w i).tgt = (w (i + 1)).src}

/-- Rotation of a closed walk by one place. -/
def rot {n : ℕ} (w : Loop M n) : Loop M n := ⟨fun i => w.1 (i + 1), fun i => w.2 (i + 1)⟩

/-- [proved-standard] `k` rotations read the walk `k` places on. -/
theorem rot_iterate {n : ℕ} (k : ℕ) (w : Loop M n) (i : ZMod n) : (rot^[k] w).1 i = w.1 (i + k) := by
  induction k generalizing w with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    show w.1 (i + k + 1) = w.1 (i + ((k + 1 : ℕ) : ZMod n))
    push_cast
    rw [add_assoc]

/-- [proved-standard] `n` rotations return a closed walk of `n` edges. -/
theorem rot_iterate_self {n : ℕ} (w : Loop M n) : rot^[n] w = w :=
  Subtype.ext (funext fun i => by rw [rot_iterate, ZMod.natCast_self, add_zero])

/-- A closed walk of `d` edges repeated to `n` edges, `d ∣ n`. -/
def rep {d n : ℕ} (h : d ∣ n) (w : Loop M d) : Loop M n :=
  ⟨fun i => w.1 (ZMod.castHom h (ZMod d) i), fun i => by
    show (w.1 (ZMod.castHom h (ZMod d) i)).tgt = (w.1 (ZMod.castHom h (ZMod d) (i + 1))).src
    rw [map_add, map_one]
    exact w.2 _⟩

/-- [proved-standard] Repetition commutes with rotation. -/
theorem rep_rot {d n : ℕ} (h : d ∣ n) (w : Loop M d) : rep h (rot w) = rot (rep h w) :=
  Subtype.ext (funext fun i => by
    show w.1 (ZMod.castHom h (ZMod d) i + 1) = w.1 (ZMod.castHom h (ZMod d) (i + 1))
    rw [map_add, map_one])

/-- [proved-standard] Repetition loses nothing. -/
theorem rep_injective {d n : ℕ} (h : d ∣ n) : Function.Injective (rep (M := M) h) := by
  intro w w' hww
  apply Subtype.ext
  funext j
  obtain ⟨i, rfl⟩ := ZMod.castHom_surjective h j
  exact congrArg (fun x : Loop M n => x.1 i) hww

/-- [proved-standard] **Repetition keeps the least period under rotation.** -/
theorem minimalPeriod_rep {d n : ℕ} (h : d ∣ n) (w : Loop M d) :
    minimalPeriod rot (rep h w) = minimalPeriod rot w := by
  refine Function.minimalPeriod_eq_minimalPeriod_iff.mpr fun k => ?_
  have hsemi : rep h (rot^[k] w) = rot^[k] (rep h w) :=
    (Function.Semiconj.iterate_right (f := rep h) (ga := rot) (gb := rot) (rep_rot h) k).eq w
  unfold Function.IsPeriodicPt Function.IsFixedPt
  rw [← hsemi]
  exact (rep_injective h).eq_iff

/-- [proved-derived] **A closed walk fixed by `d` rotations is a closed walk of `d` edges repeated.** -/
theorem exists_rep_of_periodic {d n : ℕ} [NeZero d] [NeZero n] (h : d ∣ n) (w : Loop M n)
    (hw : rot^[d] w = w) : ∃ u : Loop M d, rep h u = w := by
  have hper : ∀ i : ZMod n, w.1 (i + d) = w.1 i := fun i => by
    rw [← rot_iterate, hw]
  have hnat : ∀ r q : ℕ, w.1 ((r + d * q : ℕ) : ZMod n) = w.1 (r : ZMod n) := by
    intro r q
    induction q with
    | zero => simp
    | succ q ih =>
      have hcast : ((r + d * (q + 1) : ℕ) : ZMod n) = ((r + d * q : ℕ) : ZMod n) + (d : ZMod n) := by
        push_cast
        ring
      rw [hcast, hper, ih]
  have key : ∀ i : ZMod n, w.1 (((ZMod.castHom h (ZMod d) i).val : ℕ) : ZMod n) = w.1 i := by
    intro i
    have hi : ZMod.castHom h (ZMod d) i = ((i.val : ℕ) : ZMod d) := by
      have h1 := map_natCast (ZMod.castHom h (ZMod d)) i.val
      rwa [ZMod.natCast_zmod_val] at h1
    have h2 : w.1 i = w.1 ((i.val % d : ℕ) : ZMod n) := by
      have h3 := hnat (i.val % d) (i.val / d)
      rw [Nat.mod_add_div, ZMod.natCast_zmod_val] at h3
      exact h3
    rw [hi, ZMod.val_natCast, h2]
  refine ⟨⟨fun j => w.1 ((j.val : ℕ) : ZMod n), fun j => ?_⟩, Subtype.ext (funext key)⟩
  obtain ⟨i, rfl⟩ := ZMod.castHom_surjective h j
  show (w.1 (((ZMod.castHom h (ZMod d) i).val : ℕ) : ZMod n)).tgt =
    (w.1 (((ZMod.castHom h (ZMod d) i + 1).val : ℕ) : ZMod n)).src
  rw [← map_one (ZMod.castHom h (ZMod d)), ← map_add, key, key]
  exact w.2 i

variable [Fintype V] [DecidableEq V]

instance (M : Matrix V V ℕ) : Fintype (Edge M) := by
  have hsig : ∀ f : V → V → ℕ, Fintype (Σ a : V, Σ b : V, Fin (f a b)) := fun _ => inferInstance
  haveI : Fintype (Σ a : V, Σ b : V, Fin (M a b)) := hsig M
  exact Fintype.ofEquiv _ (Edge.equivSigma M).symm

instance (M : Matrix V V ℕ) : DecidableEq (Edge M) := by
  have hsig : ∀ f : V → V → ℕ, DecidableEq (Σ a : V, Σ b : V, Fin (f a b)) := fun _ => inferInstance
  haveI : DecidableEq (Σ a : V, Σ b : V, Fin (M a b)) := hsig M
  exact (Edge.equivSigma M).injective.decidableEq

variable (M) in
/-- [proved-standard] The edges from `a` to `b` number `M a b`. -/
theorem card_between (a b : V) : (univ.filter fun e : Edge M => e.src = a ∧ e.tgt = b).card = M a b := by
  have h : (univ.filter fun e : Edge M => e.src = a ∧ e.tgt = b) =
      (univ : Finset (Fin (M a b))).map
        ⟨fun k => (⟨a, b, k⟩ : Edge M), fun k k' hk => by cases hk; rfl⟩ := by
    ext ⟨a', b', k⟩
    simp only [mem_filter, mem_univ, true_and, mem_map]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨k, rfl⟩
    · rintro ⟨k', hk⟩
      cases hk
      exact ⟨rfl, rfl⟩
  rw [h, Finset.card_map, Finset.card_univ, Fintype.card_fin]

variable (M) in
/-- [proved-derived] **The cyclic words of `k + 1` edges, each ending where the next begins, number `tr(M^(k+1))`.** -/
theorem card_cyclic_words (k : ℕ) :
    (univ.filter fun w : Fin (k + 1) → Edge M => ∀ i, (w i).tgt = (w (i + 1)).src).card =
      (M ^ (k + 1)).trace := by
  rw [trace_pow_succ_eq_sum_cyclic,
    Finset.card_eq_sum_card_fiberwise (f := fun (w : Fin (k + 1) → Edge M) (i : Fin (k + 1)) => (w i).src)
      (t := univ) (fun _ _ => Finset.mem_coe.mpr (mem_univ _))]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hfib : ((univ.filter fun w : Fin (k + 1) → Edge M => ∀ i, (w i).tgt = (w (i + 1)).src).filter
      fun w => (fun i => (w i).src) = v) =
      Fintype.piFinset fun i => univ.filter fun e : Edge M => e.src = v i ∧ e.tgt = v (i + 1) := by
    ext w
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
    constructor
    · rintro ⟨hc, rfl⟩ i
      exact ⟨rfl, hc i⟩
    · intro h
      exact ⟨fun i => (h i).2.trans (h (i + 1)).1.symm, funext fun i => (h i).1⟩
  rw [hfib, Fintype.card_piFinset]
  exact Finset.prod_congr rfl fun i _ => card_between M (v i) (v (i + 1))

variable (M) in
/-- [proved-derived] **The closed walks of `n` edges number `tr(Mⁿ)`.** -/
theorem card_loop (n : ℕ) [NeZero n] : Fintype.card (Loop M n) = (M ^ n).trace := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [← card_cyclic_words M k]
  let e : Fin (k + 1) ≃+* ZMod (k + 1) := ZMod.finEquiv (k + 1)
  refine (Fintype.card_congr (Equiv.subtypeEquiv
    ⟨fun w j => w (e j), fun u i => u (e.symm i), fun w => by funext i; simp, fun u => by funext j; simp⟩
    ?_)).trans (Fintype.card_subtype _)
  intro w
  constructor
  · intro hw j
    show (w (e j)).tgt = (w (e (j + 1))).src
    rw [map_add, map_one]
    exact hw (e j)
  · intro hw i
    have h1 : (w (e (e.symm i))).tgt = (w (e (e.symm i + 1))).src := hw (e.symm i)
    rwa [map_add, map_one, RingEquiv.apply_symm_apply] at h1

/-- [proved-derived] **The walks of `n` edges of least period `d` are as many as the walks of `d` edges of least
period `d`**, for `d ∣ n`. -/
theorem card_minimalPeriod_rep {d n : ℕ} [NeZero d] [NeZero n] (h : d ∣ n) :
    (univ.filter fun w : Loop M n => minimalPeriod rot w = d).card =
      (univ.filter fun w : Loop M d => minimalPeriod rot w = d).card := by
  rw [← Finset.card_image_of_injective _ (rep_injective h)]
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_image]
  constructor
  · intro hw
    have hfix : rot^[d] w = w := by
      have hp := Function.isPeriodicPt_minimalPeriod rot w
      rw [hw] at hp
      exact hp
    obtain ⟨u, rfl⟩ := exists_rep_of_periodic h w hfix
    exact ⟨u, by rw [← minimalPeriod_rep h u]; exact hw, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    rw [minimalPeriod_rep, hu]

/-! ## 3. The counting identity and necklace integrality -/

variable (M) in
/-- The number `p_n` of primitive closed walks of `n` edges up to rotation: the rotation orbits of least period `n`
among the closed walks of `n` edges. -/
noncomputable def necklaceCount (n : ℕ) : ℕ :=
  if h : n = 0 then 0
  else
    haveI : NeZero n := ⟨h⟩
    primitiveCount (rot : Loop M n → Loop M n) n

variable (M) in
/-- [proved-standard] The count at a positive length is the owner's count of primitive cycles of rotation. -/
theorem necklaceCount_eq (n : ℕ) [NeZero n] :
    necklaceCount M n = primitiveCount (rot : Loop M n → Loop M n) n := by
  unfold necklaceCount
  rw [dif_neg (NeZero.ne n)]

variable (M) in
/-- [proved-standard] The count is the number of rotation orbits of least period `n` among the closed walks of `n`
edges, the owner's primitive cycles of rotation. -/
theorem necklaceCount_eq_card_orbits (n : ℕ) [NeZero n] :
    necklaceCount M n = (primitiveCycles (rot : Loop M n → Loop M n) n).card :=
  necklaceCount_eq M n

variable (M) in
/-- [proved-derived] **A primitive closed walk of `n` edges has `n` rotations**: the closed walks of `n` edges of least
period `n` number `n · p_n`. -/
theorem card_primitive_loops (n : ℕ) [NeZero n] :
    (univ.filter fun w : Loop M n => minimalPeriod rot w = n).card = n * necklaceCount M n := by
  rw [necklaceCount_eq, card_minimalPeriod_eq (rot : Loop M n → Loop M n) n (NeZero.pos n)]

variable (M) in
/-- [proved-derived] **The counting identity of a general return map**, the Euler product's coefficient form:
`tr(Mⁿ) = Σ_(d ∣ n) d · p_d` for every `n ≥ 1`. -/
theorem trace_pow_eq_sum_necklace (n : ℕ) (hn : 0 < n) :
    (M ^ n).trace = ∑ d ∈ n.divisors, d * necklaceCount M d := by
  have : NeZero n := ⟨hn.ne'⟩
  have hall : Fintype.card (Loop M n) = (univ.filter fun w : Loop M n => rot^[n] w = w).card := by
    rw [Finset.filter_true_of_mem fun w _ => rot_iterate_self w, Finset.card_univ]
  rw [← card_loop M n, hall, periodic_count (rot : Loop M n → Loop M n) n hn]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have : NeZero d := ⟨hdpos.ne'⟩
  rw [← card_minimalPeriod_eq (rot : Loop M n → Loop M n) d hdpos, card_minimalPeriod_rep hdn,
    card_primitive_loops]

variable (M) in
/-- [proved-derived] **Möbius inversion of the counting identity**, the antidiagonal form:
`Σ_(ab = n) μ(a) · tr(M^b) = n · p_n`. -/
theorem necklace_moebius (n : ℕ) (hn : 0 < n) :
    ∑ x ∈ n.divisorsAntidiagonal, (ArithmeticFunction.moebius x.1 : ℤ) * ((M ^ x.2).trace : ℤ) =
      ((n * necklaceCount M n : ℕ) : ℤ) :=
  (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
    (f := fun i => ((i * necklaceCount M i : ℕ) : ℤ)) (g := fun k => ((M ^ k).trace : ℤ))).mp
    (fun k hk => by rw [trace_pow_eq_sum_necklace M k hk, Nat.cast_sum]) n hn

variable (M) in
/-- [proved-derived] **Necklace integrality**: `Σ_(d ∣ n) μ(n/d) · tr(M^d) = n · p_n` for every `n ≥ 1`. -/
theorem necklace_integrality (n : ℕ) (hn : 0 < n) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * ((M ^ d).trace : ℤ) =
      (n : ℤ) * (necklaceCount M n : ℤ) := by
  rw [← Nat.sum_divisorsAntidiagonal'
    (f := fun a b => (ArithmeticFunction.moebius a : ℤ) * ((M ^ b).trace : ℤ)), necklace_moebius M n hn]
  push_cast
  rfl

variable (M) in
/-- [proved-derived] `n` divides the Möbius sum of the traces. -/
theorem necklace_dvd (n : ℕ) (hn : 0 < n) :
    (n : ℤ) ∣ ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * ((M ^ d).trace : ℤ) :=
  ⟨necklaceCount M n, necklace_integrality M n hn⟩

variable (M) in
/-- [proved-derived] The Möbius sum of the traces is nonnegative. -/
theorem necklace_nonneg (n : ℕ) (hn : 0 < n) :
    0 ≤ ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * ((M ^ d).trace : ℤ) := by
  rw [necklace_integrality M n hn]
  positivity

variable (M) in
/-- [proved-derived] The count of primitive closed walks up to rotation is the Möbius sum over `n`. -/
theorem necklaceCount_eq_div (n : ℕ) (hn : 0 < n) :
    (necklaceCount M n : ℤ) =
      (∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * ((M ^ d).trace : ℤ)) / n := by
  rw [necklace_integrality M n hn, Int.mul_ediv_cancel_left _ (by exact_mod_cast hn.ne')]

/-- [proved-derived] **Necklace integrality for an integer matrix with nonnegative entries**: `n` divides the Möbius sum
of its traces, and the sum is nonnegative. -/
theorem necklace_dvd_of_nonneg (A : Matrix V V ℤ) (hA : ∀ a b, 0 ≤ A a b) (n : ℕ) (hn : 0 < n) :
    (n : ℤ) ∣ ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * (A ^ d).trace ∧
      0 ≤ ∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n / d) : ℤ) * (A ^ d).trace := by
  have hmap : A = (Nat.castRingHom ℤ).mapMatrix (A.map Int.toNat) := by
    ext a b
    simp [Int.toNat_of_nonneg (hA a b)]
  have htr : ∀ d : ℕ, (A ^ d).trace = (((A.map Int.toNat) ^ d).trace : ℤ) := by
    intro d
    conv_lhs => rw [hmap, ← map_pow]
    simp [Matrix.trace, Matrix.map_apply]
  simp_rw [htr]
  exact ⟨necklace_dvd _ n hn, necklace_nonneg _ n hn⟩

end Walks

/-! ## 4. The Euler product, coefficient by coefficient -/

section Euler

open PowerSeries

/-- [proved-standard] **Two power series whose logarithmic derivatives agree below order `N`, with one constant term,
agree up to order `N`.** The owner's `HasLogDeriv.unique` is the case of every order. -/
theorem coeff_eq_of_logDeriv_agree {F G A B : PowerSeries ℚ} (hF : HasLogDeriv F A) (hG : HasLogDeriv G B)
    (h0 : constantCoeff F = constantCoeff G) (N : ℕ) (hAB : ∀ k < N, coeff k A = coeff k B) :
    ∀ k ≤ N, coeff k F = coeff k G := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    cases k with
    | zero => rw [coeff_zero_eq_constantCoeff_apply, coeff_zero_eq_constantCoeff_apply, h0]
    | succ k =>
      have hFk : coeff k (derivative ℚ F) = coeff k (F * A) := congrArg (coeff k) hF
      have hGk : coeff k (derivative ℚ G) = coeff k (G * B) := congrArg (coeff k) hG
      rw [coeff_derivative, coeff_mul] at hFk hGk
      have hsum : ∑ p ∈ antidiagonal k, coeff p.1 F * coeff p.2 A =
          ∑ p ∈ antidiagonal k, coeff p.1 G * coeff p.2 B := by
        refine Finset.sum_congr rfl fun p hp => ?_
        have h12 : p.1 + p.2 = k := mem_antidiagonal.mp hp
        rw [ih p.1 (by omega) (by omega), hAB p.2 (by omega)]
      have hk1 : ((k : ℚ) + 1) ≠ 0 := by positivity
      have hmul : coeff (k + 1) F * ((k : ℚ) + 1) = coeff (k + 1) G * ((k : ℚ) + 1) := by
        rw [hFk, hGk, hsum]
      exact mul_right_cancel₀ hk1 hmul

variable {V : Type*} [Fintype V] [DecidableEq V] (M : Matrix V V ℕ)

/-- [proved-standard] The traces of the return map read over `ℚ` are its traces. -/
theorem trace_map_cast_pow (n : ℕ) : ((M.map (Nat.cast : ℕ → ℚ)) ^ n).trace = ((M ^ n).trace : ℚ) := by
  have h : M.map (Nat.cast : ℕ → ℚ) = (Nat.castRingHom ℚ).mapMatrix M := rfl
  rw [h, ← map_pow]
  simp [Matrix.trace, Matrix.map_apply]

/-- [proved-derived] **The Euler product of a general return map, coefficient by coefficient**: every coefficient of
the transfer determinant `det(1 − T·M)` of order at most `N` is the coefficient of the product
`∏_(d = 1)^N (1 − T^d)^(p_d)` over the primitive closed walks of at most `N` edges. The product over every length is
the limit this names: each coefficient is reached at `N` equal to its order and never moves after. -/
theorem euler_product_coeff (N k : ℕ) (hk : k ≤ N) :
    coeff k ((M.map (Nat.cast : ℕ → ℚ)).charpolyRev : PowerSeries ℚ) =
      coeff k (∏ d ∈ Icc 1 N, (1 - X ^ d) ^ necklaceCount M d : PowerSeries ℚ) := by
  have hF : HasLogDeriv ((M.map (Nat.cast : ℕ → ℚ)).charpolyRev : PowerSeries ℚ)
      (-PowerSeries.mk fun j => Matrix.trace ((M.map (Nat.cast : ℕ → ℚ)) ^ (j + 1))) := by
    unfold HasLogDeriv
    rw [Holonics.Aeon.Production.Zeta.transferDet_derivative]
    ring
  have hG := HasLogDeriv.prod (Icc 1 N) (fun d => (1 - X ^ d) ^ necklaceCount M d)
    (fun d => C (necklaceCount M d : ℚ) * (-cycleCurrent d))
    (fun d hd => (cycleFactor_logDeriv d (by simp at hd; omega)).pow _)
  have h1 : constantCoeff ((M.map (Nat.cast : ℕ → ℚ)).charpolyRev : PowerSeries ℚ) = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe,
      Polynomial.coeff_zero_eq_eval_zero, Matrix.eval_charpolyRev]
  have h2 : constantCoeff (∏ d ∈ Icc 1 N, (1 - X ^ d) ^ necklaceCount M d : PowerSeries ℚ) = 1 := by
    rw [map_prod]
    apply prod_eq_one
    intro x hx
    have hx1 : x ≠ 0 := by
      simp only [mem_Icc] at hx
      omega
    simp [zero_pow hx1]
  refine coeff_eq_of_logDeriv_agree hF hG (h1.trans h2.symm) N (fun j hj => ?_) k hk
  simp only [map_neg, coeff_mk, map_sum, coeff_C_mul, cycleCurrent, mul_neg, sum_neg_distrib, neg_inj]
  rw [trace_map_cast_pow, trace_pow_eq_sum_necklace M (j + 1) (Nat.succ_pos j)]
  push_cast
  have hfilter : ∑ x ∈ Icc 1 N, (necklaceCount M x : ℚ) * (if x ∣ j + 1 then (x : ℚ) else 0) =
      ∑ x ∈ (Icc 1 N).filter (· ∣ j + 1), (x : ℚ) * necklaceCount M x := by
    rw [sum_filter]
    refine sum_congr rfl fun x _ => ?_
    split_ifs <;> ring
  rw [hfilter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext x
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hx, _⟩
    have hle : x ≤ j + 1 := Nat.le_of_dvd (Nat.succ_pos j) hx
    exact ⟨⟨Nat.pos_of_dvd_of_pos hx (Nat.succ_pos j), by omega⟩, hx⟩
  · rintro ⟨_, hx⟩
    exact ⟨hx, Nat.succ_ne_zero j⟩

end Euler

/-! ## 5. The owner's case is the restriction to a map -/

section Restriction

open Holonics.Aeon.Production.Zeta

private theorem eq_of_divisor_sums_eq (a b : ℕ → ℕ)
    (h : ∀ n, 0 < n → ∑ d ∈ n.divisors, d * a d = ∑ d ∈ n.divisors, d * b d) : ∀ n, 0 < n → a n = b n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have hs := h n hn
    rw [← Nat.cons_self_properDivisors hn.ne', Finset.sum_cons, Finset.sum_cons] at hs
    have hp : ∑ d ∈ n.properDivisors, d * a d = ∑ d ∈ n.properDivisors, d * b d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' := Nat.mem_properDivisors.mp hd
      rw [ih d hd'.2 (Nat.pos_of_dvd_of_pos hd'.1 hn)]
    rw [hp] at hs
    exact Nat.eq_of_mul_eq_mul_left hn (Nat.add_right_cancel hs)

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `0/1` matrix of a map of occurrences, over the natural numbers: the owner's `mapMatrix` before its reading
over `ℚ`. -/
def mapMatrixNat (f : α → α) : Matrix α α ℕ := fun x y => if f x = y then 1 else 0

omit [Fintype α] in
/-- [proved-standard] Read over `ℚ`, it is the owner's matrix of the map. -/
theorem mapMatrixNat_cast (f : α → α) : (mapMatrixNat f).map (Nat.cast : ℕ → ℚ) = mapMatrix f := by
  ext x y
  simp only [mapMatrixNat, mapMatrix, Matrix.map_apply]
  split_ifs <;> simp

/-- [proved-derived] **On a map of occurrences the general count is the owner's**: the primitive closed walks of `n`
edges up to rotation in the map's graph are its periodic orbits of least period `n`. -/
theorem necklaceCount_mapMatrixNat (f : α → α) (n : ℕ) (hn : 0 < n) :
    necklaceCount (mapMatrixNat f) n = primitiveCount f n := by
  refine eq_of_divisor_sums_eq _ _ (fun m hm => ?_) n hn
  rw [← trace_pow_eq_sum_necklace (mapMatrixNat f) m hm, ← periodic_count f m hm]
  have hq : (((mapMatrixNat f) ^ m).trace : ℚ) = ((univ.filter fun x => f^[m] x = x).card : ℚ) := by
    rw [← trace_map_cast_pow, mapMatrixNat_cast, trace_pow_mapMatrix]
  exact_mod_cast hq

end Restriction

/-! ## 6. Rulers -/

private theorem trace_two_loops (n : ℕ) : ((!![2] : Matrix (Fin 1) (Fin 1) ℕ) ^ n).trace = 2 ^ n := by
  have h : (!![2] : Matrix (Fin 1) (Fin 1) ℕ) = Matrix.diagonal fun _ => 2 := by
    ext i j
    fin_cases i
    fin_cases j
    simp
  rw [h, Matrix.diagonal_pow, Matrix.trace_diagonal]
  simp

/-- [proved-derived] **One place with two loops**: the primitive closed walks of `1, …, 6` edges up to rotation number
`2, 1, 2, 3, 6, 9`, the primitive binary necklaces. -/
theorem ruler_two_loops :
    necklaceCount (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 1 = 2 ∧ necklaceCount (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 2 = 1 ∧
      necklaceCount (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 3 = 2 ∧
      necklaceCount (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 4 = 3 ∧
      necklaceCount (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 5 = 6 ∧
      necklaceCount (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 6 = 9 := by
  have h1 := trace_pow_eq_sum_necklace (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 1 (by norm_num)
  have h2 := trace_pow_eq_sum_necklace (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 2 (by norm_num)
  have h3 := trace_pow_eq_sum_necklace (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 3 (by norm_num)
  have h4 := trace_pow_eq_sum_necklace (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 4 (by norm_num)
  have h5 := trace_pow_eq_sum_necklace (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 5 (by norm_num)
  have h6 := trace_pow_eq_sum_necklace (!![2] : Matrix (Fin 1) (Fin 1) ℕ) 6 (by norm_num)
  rw [trace_two_loops, show Nat.divisors 1 = {1} by decide] at h1
  rw [trace_two_loops, show Nat.divisors 2 = {1, 2} by decide] at h2
  rw [trace_two_loops, show Nat.divisors 3 = {1, 3} by decide] at h3
  rw [trace_two_loops, show Nat.divisors 4 = {1, 2, 4} by decide] at h4
  rw [trace_two_loops, show Nat.divisors 5 = {1, 5} by decide] at h5
  rw [trace_two_loops, show Nat.divisors 6 = {1, 2, 3, 6} by decide] at h6
  simp at h1 h2 h3 h4 h5 h6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

private theorem trace_golden_mean :
    ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) ^ 1).trace = 1 ∧
      ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) ^ 2).trace = 3 ∧
      ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) ^ 3).trace = 4 ∧
      ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) ^ 4).trace = 7 ∧
      ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) ^ 5).trace = 11 ∧
      ((!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) ^ 6).trace = 18 := by
  decide

/-- [proved-derived] **The golden-mean shift** `[[1, 1], [1, 0]]`: the primitive closed walks of `1, …, 6` edges up to
rotation number `1, 1, 1, 1, 2, 2`. -/
theorem ruler_golden_mean :
    necklaceCount (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 1 = 1 ∧
      necklaceCount (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 2 = 1 ∧
      necklaceCount (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 3 = 1 ∧
      necklaceCount (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 4 = 1 ∧
      necklaceCount (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 5 = 2 ∧
      necklaceCount (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 6 = 2 := by
  obtain ⟨t1, t2, t3, t4, t5, t6⟩ := trace_golden_mean
  have h1 := trace_pow_eq_sum_necklace (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 1 (by norm_num)
  have h2 := trace_pow_eq_sum_necklace (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 2 (by norm_num)
  have h3 := trace_pow_eq_sum_necklace (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 3 (by norm_num)
  have h4 := trace_pow_eq_sum_necklace (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 4 (by norm_num)
  have h5 := trace_pow_eq_sum_necklace (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 5 (by norm_num)
  have h6 := trace_pow_eq_sum_necklace (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) ℕ) 6 (by norm_num)
  rw [t1, show Nat.divisors 1 = {1} by decide] at h1
  rw [t2, show Nat.divisors 2 = {1, 2} by decide] at h2
  rw [t3, show Nat.divisors 3 = {1, 3} by decide] at h3
  rw [t4, show Nat.divisors 4 = {1, 2, 4} by decide] at h4
  rw [t5, show Nat.divisors 5 = {1, 5} by decide] at h5
  rw [t6, show Nat.divisors 6 = {1, 2, 3, 6} by decide] at h6
  simp at h1 h2 h3 h4 h5 h6
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end Holonics.Compression.Landmark.NecklaceIntegrality
