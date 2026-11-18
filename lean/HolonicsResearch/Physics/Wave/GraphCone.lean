import Mathlib
import Holonics.Physics.Wave.Telegrapher

/-!
# The causal cone on a general graph: a change moves at most one contact per tick

[definition] Source: the owed-statements issue (#410, "Fluid and heat"): the light cone on a general
graph, where `Physics/Wave/Telegrapher` proves the chain. Atlas `wave.lattice-cone` (the chain) and
`contact.pass-reach-gap` (its first clause: `t` passes reach `t` hops).

The cells are any type `V`, joined by a relation `adj` (the contacts). `Near adj k i j` says that
`j` is reached from `i` by at most `k` contacts. A **tick** is any map `F` of states whose reading at
a cell depends only on the readings at that cell and at the cells it touches (`LocalStep`); nothing
is asked of the values, of linearity or of a material.

[proved-standard; formal-checked] What is proved.

1. **Walks of at most `k` contacts** (`Near`): reflexive, monotone in `k`, extended at either end
   (`near_snoc`), composed by adding lengths (`near_trans`), symmetric when the contacts are
   (`near_symm`). On a `SimpleGraph` it is the existence of a walk of length at most `k`
   (`near_iff_exists_walk`), which is reachability with `dist i j ≤ k` (`near_iff_dist_le`).
2. **The cone** (`cone`): under any schedule of local ticks, two states that read the same at every
   cell within `k` contacts of `i` read the same at `i` after `k` ticks. So a change confined to a
   set `S` is confined to the `k`-neighbourhood of `S` after `k` ticks
   (`change_moves_one_contact_per_tick`, `neighbourhood`), and a state that rests outside `S` rests
   outside that neighbourhood when the rest state is kept by the ticks (`rest_outside_cone`). The
   same for one tick iterated (`iterate_cone`).
3. **Matrices.** A matrix over a semiring whose entry `M i j` vanishes unless `i = j` or `i` touches
   `j` (`Local`) has `(M ^ k) i j ≠ 0` only within `k` contacts (`near_of_pow_ne_zero`), its action
   on a datum is a local tick (`mulVec_local`), and a datum supported on `S` is supported in the
   `k`-neighbourhood of `S` after `k` steps (`pow_mulVec_support`). The graph Laplacian is local
   (`lapMatrix_local`).
4. **Second-order schemes.** The two-step scheme
   `x_(t+2) = a·x_(t+1) + b·x_t + K x_(t+1)` with cellwise coefficients `a`, `b` and a local `K` is
   a local tick on the pair (present, previous) (`twoStep_local`), so from data supported on `S` at
   `t = 0` and `t = 1` the reading at `t + 1` and at `t` vanishes outside the `t`-neighbourhood of
   `S` (`seq_cone`), hence at `t` outside the `t`-neighbourhood (`seq_cone'`). The wave scheme
   `x_(t+1) = 2x_t − x_(t−1) + c² L x_t` is the case `a = 2`, `b = −1`, `K = c² L` (`wave`,
   `wave_succ_succ`, `wave_cone`); a damped (telegrapher) scheme is another choice of `a`, `b`, `K`
   and has the same cone, whatever the damping.
5. **The edge is reached.** With nonnegative entries, positive on the diagonal and on every contact,
   `0 < (M ^ k) i j` exactly within `k` contacts (`pow_pos_iff_near`; `pow_apply_nonneg`,
   `pow_pos_of_near`). For a graph's lazy adjacency matrix, `0 < ((1 + A) ^ k) i j` exactly when `j`
   is reachable from `i` with `dist i j ≤ k` (`lazy_adjMatrix_pow_pos_iff`).
6. **The chain is the case of a path.** On `ℤ` with each cell touching its two neighbours
   (`pathAdj`), `Near pathAdj k i j ↔ |i − j| ≤ k` (`near_path_iff`); the tick of
   `Physics/Wave/Telegrapher` is local for the reading (voltage at `i`, current of the junction to
   its right) (`telegrapher_step_local`), so two states that agree outside `[lo, hi]` agree outside
   `[lo − n, hi + n]` after `n` ticks under one source schedule (`chain_cone`), and the nodes'
   statement of `Telegrapher.change_moves_one_cell_per_tick` follows (`chain_nodes_cone`).

Limits. The continuum limit of the scheme is not here: it wants the scheme's consistency (the
difference quotient of the tick tends to the field law on smooth data) and its stability (the
staggered energy of `Physics/Wave/Energy` under the Courant bound) on a refining family of grids,
which together give convergence, and then the lattice cone at one contact per tick is read against
the characteristic cone as the spacing over the tick. Item 6 reads a junction's current at the
cell to its left, so its cone for currents is one junction wider at the right edge than
`Telegrapher.Supported` states; the voltages' cone is the same. Item 5 is stated for a first-order
matrix step; the attained front of the two-step scheme is in `Telegrapher` for the chain only.

Computational object: the helical pair interaction, read at its incidence: which contacts a tick
reads (pair; faces and placement, the cells a reading reaches). The helix, cell holonomy, tube and
tower thread stay attached and are not touched.

Consumers: `Holonics.Physics.Wave.Telegrapher` (its chain cone, recovered by `chain_cone`); atlas
`wave.lattice-cone`, `contact.pass-reach-gap`.

No `sorry`, no `axiom`, no `native_decide`.
-/

namespace Holonics.Physics.Wave.GraphCone

/-! ## 1. Walks of at most `k` contacts -/

section Near

variable {V : Type*}

/-- [definition] **Within `k` contacts**: `j` is reached from `i` by a walk of at most `k`
contacts (a step may stay at its cell). -/
def Near (adj : V → V → Prop) : ℕ → V → V → Prop
  | 0, i, j => i = j
  | k + 1, i, j => ∃ l, (i = l ∨ adj i l) ∧ Near adj k l j

variable {adj : V → V → Prop}

theorem near_zero {i j : V} : Near adj 0 i j ↔ i = j := Iff.rfl

theorem near_succ {k : ℕ} {i j : V} :
    Near adj (k + 1) i j ↔ ∃ l, (i = l ∨ adj i l) ∧ Near adj k l j := Iff.rfl

/-- [proved-standard] A cell is within any number of contacts of itself. -/
theorem near_refl (adj : V → V → Prop) (k : ℕ) (i : V) : Near adj k i i := by
  induction k with
  | zero => exact near_zero.mpr rfl
  | succ k ih => exact ⟨i, Or.inl rfl, ih⟩

/-- [proved-standard] More contacts reach at least as far. -/
theorem near_mono {k m : ℕ} (hkm : k ≤ m) {i j : V} (h : Near adj k i j) : Near adj m i j := by
  induction hkm with
  | refl => exact h
  | step _ ih => exact ⟨i, Or.inl rfl, ih⟩

/-- [proved-standard] A contact is one step. -/
theorem near_of_adj {i j : V} (h : adj i j) : Near adj 1 i j :=
  ⟨j, Or.inr h, near_zero.mpr rfl⟩

/-- [proved-standard] A walk is extended at its far end. -/
theorem near_snoc {k : ℕ} {i l j : V} (h : Near adj k i l) (hlj : l = j ∨ adj l j) :
    Near adj (k + 1) i j := by
  induction k generalizing i with
  | zero =>
    obtain rfl := near_zero.mp h
    exact ⟨j, hlj, near_zero.mpr rfl⟩
  | succ k ih =>
    obtain ⟨m, him, hm⟩ := h
    exact ⟨m, him, ih hm⟩

/-- [proved-standard] Walks compose, and their lengths add. -/
theorem near_trans {a b : ℕ} {i l j : V} (h1 : Near adj a i l) (h2 : Near adj b l j) :
    Near adj (a + b) i j := by
  induction a generalizing i with
  | zero =>
    obtain rfl := near_zero.mp h1
    simpa using h2
  | succ a ih =>
    obtain ⟨m, him, hm⟩ := h1
    rw [show a + 1 + b = (a + b) + 1 by omega]
    exact ⟨m, him, ih hm⟩

/-- [proved-standard] With symmetric contacts, a walk is walked back. -/
theorem near_symm (hs : ∀ i j, adj i j → adj j i) {k : ℕ} {i j : V} (h : Near adj k i j) :
    Near adj k j i := by
  induction k generalizing i with
  | zero => exact near_zero.mpr (near_zero.mp h).symm
  | succ k ih =>
    obtain ⟨l, hil, hl⟩ := h
    exact near_snoc (ih hl) (hil.elim (fun e => Or.inl e.symm) fun e => Or.inr (hs _ _ e))

/-- [proved-standard] On a graph, within `k` contacts is a walk of length at most `k`. -/
theorem near_iff_exists_walk (G : SimpleGraph V) {k : ℕ} {i j : V} :
    Near G.Adj k i j ↔ ∃ p : G.Walk i j, p.length ≤ k := by
  induction k generalizing i with
  | zero =>
    constructor
    · intro h
      obtain rfl := near_zero.mp h
      exact ⟨SimpleGraph.Walk.nil, le_rfl⟩
    · rintro ⟨p, hp⟩
      exact near_zero.mpr (SimpleGraph.Walk.eq_of_length_eq_zero (Nat.le_zero.mp hp))
  | succ k ih =>
    constructor
    · rintro ⟨l, hil | hil, hl⟩
      · subst hil
        obtain ⟨p, hp⟩ := ih.mp hl
        exact ⟨p, Nat.le_succ_of_le hp⟩
      · obtain ⟨p, hp⟩ := ih.mp hl
        exact ⟨SimpleGraph.Walk.cons hil p, by rw [SimpleGraph.Walk.length_cons]; omega⟩
    · rintro ⟨p, hp⟩
      cases p with
      | nil => exact near_refl _ _ _
      | cons h q =>
        rw [SimpleGraph.Walk.length_cons] at hp
        exact ⟨_, Or.inr h, ih.mpr ⟨q, by omega⟩⟩

/-- [proved-standard] On a graph, within `k` contacts is reachability with distance at most `k`. -/
theorem near_iff_dist_le (G : SimpleGraph V) {k : ℕ} {i j : V} :
    Near G.Adj k i j ↔ G.Reachable i j ∧ G.dist i j ≤ k := by
  rw [near_iff_exists_walk]
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨⟨p⟩, (SimpleGraph.dist_le p).trans hp⟩
  · rintro ⟨hr, hd⟩
    obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_dist
    exact ⟨p, hp ▸ hd⟩

/-- [definition] **The `k`-neighbourhood of a set**: the cells from which the set is reached within
`k` contacts. -/
def neighbourhood (adj : V → V → Prop) (k : ℕ) (S : Set V) : Set V :=
  {i | ∃ j ∈ S, Near adj k i j}

theorem neighbourhood_zero (S : Set V) : neighbourhood adj 0 S = S := by
  ext i
  constructor
  · rintro ⟨j, hj, h⟩
    exact (near_zero.mp h) ▸ hj
  · intro hi
    exact ⟨i, hi, near_zero.mpr rfl⟩

theorem neighbourhood_mono {k m : ℕ} (hkm : k ≤ m) (S : Set V) :
    neighbourhood adj k S ⊆ neighbourhood adj m S :=
  fun _ ⟨j, hj, h⟩ => ⟨j, hj, near_mono hkm h⟩

end Near

/-! ## 2. The cone of a schedule of local ticks -/

section Cone

variable {V : Type*} {σ : Type*} {α : Type*}

/-- [definition] **A local tick**: the reading at a cell after the tick depends only on the readings
at that cell and at the cells it touches before it. -/
def LocalStep (adj : V → V → Prop) (read : σ → V → α) (F : σ → σ) : Prop :=
  ∀ x y i, (∀ l, (i = l ∨ adj i l) → read x l = read y l) → read (F x) i = read (F y) i

/-- [definition] **Propagation** under a schedule of ticks: `n` ticks from `x`. -/
def run (F : ℕ → σ → σ) : ℕ → σ → σ
  | 0, x => x
  | n + 1, x => F n (run F n x)

@[simp] theorem run_zero (F : ℕ → σ → σ) (x : σ) : run F 0 x = x := rfl

@[simp] theorem run_succ (F : ℕ → σ → σ) (n : ℕ) (x : σ) :
    run F (n + 1) x = F n (run F n x) := rfl

theorem run_const (F : σ → σ) (n : ℕ) (x : σ) : run (fun _ => F) n x = F^[n] x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, ih, Function.iterate_succ_apply']

variable {adj : V → V → Prop} {read : σ → V → α}

/-- [proved-standard] **The cone.** Under any schedule of local ticks, two states that read the same
at every cell within `n` contacts of `i` read the same at `i` after `n` ticks. No hypothesis on the
values, on linearity or on a material. -/
theorem cone {F : ℕ → σ → σ} (hF : ∀ t, LocalStep adj read (F t)) (n : ℕ) {x y : σ} {i : V}
    (h : ∀ j, Near adj n i j → read x j = read y j) :
    read (run F n x) i = read (run F n y) i := by
  induction n generalizing i with
  | zero => exact h i (near_zero.mpr rfl)
  | succ n ih =>
    rw [run_succ, run_succ]
    exact hF n _ _ i fun l hl => ih fun j hj => h j ⟨l, hl, hj⟩

/-- [proved-standard] The cone of one local tick iterated. -/
theorem iterate_cone {F : σ → σ} (hF : LocalStep adj read F) (n : ℕ) {x y : σ} {i : V}
    (h : ∀ j, Near adj n i j → read x j = read y j) :
    read (F^[n] x) i = read (F^[n] y) i := by
  rw [← run_const, ← run_const]
  exact cone (fun _ => hF) n h

/-- [proved-standard] **A change moves at most one contact per tick.** Two states that read the
same outside `S` read the same outside the `n`-neighbourhood of `S` after `n` ticks of one
schedule. -/
theorem change_moves_one_contact_per_tick {F : ℕ → σ → σ} (hF : ∀ t, LocalStep adj read (F t))
    {S : Set V} {x y : σ} (hxy : ∀ j, j ∉ S → read x j = read y j) (n : ℕ) {i : V}
    (hi : i ∉ neighbourhood adj n S) : read (run F n x) i = read (run F n y) i :=
  cone hF n fun j hj => hxy j fun hjS => hi ⟨j, hjS, hj⟩

/-- [proved-standard] **Rest outside the cone.** When the ticks keep a rest state `z`, a state that
reads as `z` outside `S` reads as `z` outside the `n`-neighbourhood of `S` after `n` ticks. -/
theorem rest_outside_cone {F : ℕ → σ → σ} (hF : ∀ t, LocalStep adj read (F t)) {z : σ}
    (hz : ∀ t, F t z = z) {S : Set V} {x : σ} (hx : ∀ j, j ∉ S → read x j = read z j) (n : ℕ)
    {i : V} (hi : i ∉ neighbourhood adj n S) : read (run F n x) i = read z i := by
  have hrun : run F n z = z := by
    induction n with
    | zero => rfl
    | succ n ih => rw [run_succ, ih (fun h => hi (neighbourhood_mono (Nat.le_succ n) S h)), hz]
  rw [change_moves_one_contact_per_tick hF hx n hi, hrun]

end Cone

/-! ## 3. Matrices whose entries follow the contacts -/

section Matrices

variable {V : Type*} [Fintype V] [DecidableEq V] {R : Type*} [Semiring R]
variable {adj : V → V → Prop}

/-- [definition] **A local matrix**: the entry `M i j` vanishes unless `i = j` or `i` touches
`j`. -/
def Local (adj : V → V → Prop) (M : Matrix V V R) : Prop :=
  ∀ i j, M i j ≠ 0 → i = j ∨ adj i j

/-- [proved-standard] **`k` passes reach at most `k` contacts**: a nonzero entry of `M ^ k` joins
cells within `k` contacts. -/
theorem near_of_pow_ne_zero {M : Matrix V V R} (hM : Local adj M) (k : ℕ) {i j : V}
    (h : (M ^ k) i j ≠ 0) : Near adj k i j := by
  induction k generalizing i with
  | zero =>
    rw [pow_zero] at h
    by_contra hij
    exact h (Matrix.one_apply_ne fun e => hij (near_zero.mpr e))
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply] at h
    obtain ⟨l, -, hl⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨l, hM i l (left_ne_zero_of_mul hl), ih (right_ne_zero_of_mul hl)⟩

omit [DecidableEq V] in
/-- [proved-standard] The action of a local matrix on a datum is a local tick. -/
theorem mulVec_local {M : Matrix V V R} (hM : Local adj M) :
    LocalStep adj (fun x : V → R => x) M.mulVec := by
  intro x y i h
  show ∑ j, M i j * x j = ∑ j, M i j * y j
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : M i j = 0
  · rw [hj, zero_mul, zero_mul]
  · have hj' : x j = y j := h j (hM i j hj)
    rw [hj']

/-- [proved-standard] **A datum supported on `S` is supported in the `k`-neighbourhood of `S` after
`k` steps.** -/
theorem pow_mulVec_support {M : Matrix V V R} (hM : Local adj M) (k : ℕ) {S : Set V}
    {x : V → R} (hx : ∀ j, j ∉ S → x j = 0) {i : V} (hi : i ∉ neighbourhood adj k S) :
    (M ^ k).mulVec x i = 0 := by
  show ∑ j, (M ^ k) i j * x j = 0
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : j ∈ S
  · have h0 : (M ^ k) i j = 0 := by
      by_contra hne
      exact hi ⟨j, hj, near_of_pow_ne_zero hM k hne⟩
    rw [h0, zero_mul]
  · rw [hx j hj, mul_zero]

end Matrices

/-- [proved-standard] The graph Laplacian is a local matrix. -/
theorem lapMatrix_local {V : Type*} [Fintype V] [DecidableEq V] (R : Type*) [Ring R]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Local G.Adj (G.lapMatrix R) := by
  intro i j h
  by_contra hc
  push Not at hc
  apply h
  simp [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, hc.1, hc.2]

/-! ## 4. Second-order schemes -/

section TwoStep

variable {V : Type*} [Fintype V] {R : Type*} [CommRing R]
variable {adj : V → V → Prop}

/-- [definition] **One tick of a two-step scheme** on the pair (present, previous):
`x⁺ = a·x + b·x⁻ + K x`, with cellwise coefficients `a`, `b`. -/
def twoStep (a b : V → R) (K : Matrix V V R) (s : (V → R) × (V → R)) : (V → R) × (V → R) :=
  (fun i => a i * s.1 i + b i * s.2 i + ∑ j, K i j * s.1 j, s.1)

/-- [definition] The reading of a pair at a cell: the present and the previous value. -/
def readPair (s : (V → R) × (V → R)) (i : V) : R × R := (s.1 i, s.2 i)

/-- [proved-standard] **A two-step scheme with a local operator is a local tick** on the pair. -/
theorem twoStep_local (a b : V → R) {K : Matrix V V R} (hK : Local adj K) :
    LocalStep adj readPair (twoStep a b K) := by
  intro x y i h
  have hi := h i (Or.inl rfl)
  have h1 : x.1 i = y.1 i := congrArg Prod.fst hi
  have h2 : x.2 i = y.2 i := congrArg Prod.snd hi
  have hs : ∑ j, K i j * x.1 j = ∑ j, K i j * y.1 j := by
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : K i j = 0
    · rw [hj, zero_mul, zero_mul]
    · have hj1 : x.1 j = y.1 j := congrArg Prod.fst (h j (hK i j hj))
      rw [hj1]
  show (a i * x.1 i + b i * x.2 i + ∑ j, K i j * x.1 j, x.1 i) =
    (a i * y.1 i + b i * y.2 i + ∑ j, K i j * y.1 j, y.1 i)
  rw [h1, h2, hs]

/-- [proved-standard] The pair at rest is kept. -/
theorem twoStep_zero (a b : V → R) (K : Matrix V V R) : twoStep a b K (0, 0) = (0, 0) := by
  refine Prod.ext (funext fun i => ?_) rfl
  simp [twoStep]

/-- [definition] **The sequence of a two-step scheme** from the data `x0` at `t = 0` and `x1` at
`t = 1`. -/
def seq (a b : V → R) (K : Matrix V V R) (x0 x1 : V → R) (t : ℕ) : V → R :=
  ((twoStep a b K)^[t] (x1, x0)).2

variable {a b : V → R} {K : Matrix V V R} {x0 x1 : V → R}

@[simp] theorem seq_zero : seq a b K x0 x1 0 = x0 := rfl

@[simp] theorem seq_one : seq a b K x0 x1 1 = x1 := rfl

theorem seq_succ_eq_fst (t : ℕ) :
    seq a b K x0 x1 (t + 1) = ((twoStep a b K)^[t] (x1, x0)).1 := by
  unfold seq
  rw [Function.iterate_succ_apply']
  rfl

/-- [proved-standard] **The scheme's recurrence**:
`x_(t+2) = a·x_(t+1) + b·x_t + K x_(t+1)`. -/
theorem seq_succ_succ (t : ℕ) (i : V) :
    seq a b K x0 x1 (t + 2) i =
      a i * seq a b K x0 x1 (t + 1) i + b i * seq a b K x0 x1 t i +
        ∑ j, K i j * seq a b K x0 x1 (t + 1) j := by
  rw [seq_succ_eq_fst (t + 1), Function.iterate_succ_apply', seq_succ_eq_fst t]
  rfl

/-- [proved-standard] **The cone of a two-step scheme.** From data supported on `S` at `t = 0` and
`t = 1`, the readings at `t + 1` and at `t` vanish outside the `t`-neighbourhood of `S`. -/
theorem seq_cone (hK : Local adj K) {S : Set V} (h0 : ∀ j, j ∉ S → x0 j = 0)
    (h1 : ∀ j, j ∉ S → x1 j = 0) (t : ℕ) {i : V} (hi : i ∉ neighbourhood adj t S) :
    seq a b K x0 x1 (t + 1) i = 0 ∧ seq a b K x0 x1 t i = 0 := by
  have key : readPair ((twoStep a b K)^[t] (x1, x0)) i =
      readPair ((twoStep a b K)^[t] ((0, 0) : (V → R) × (V → R))) i := by
    refine iterate_cone (twoStep_local a b hK) t fun j hj => ?_
    have hjS : j ∉ S := fun hjS => hi ⟨j, hjS, hj⟩
    show (x1 j, x0 j) = ((0 : V → R) j, (0 : V → R) j)
    rw [h1 j hjS, h0 j hjS]
    rfl
  rw [Function.iterate_fixed (twoStep_zero a b K)] at key
  refine ⟨?_, ?_⟩
  · rw [seq_succ_eq_fst]
    exact congrArg Prod.fst key
  · exact congrArg Prod.snd key

/-- [proved-standard] The reading at `t` vanishes outside the `t`-neighbourhood of the data's
support. -/
theorem seq_cone' (hK : Local adj K) {S : Set V} (h0 : ∀ j, j ∉ S → x0 j = 0)
    (h1 : ∀ j, j ∉ S → x1 j = 0) (t : ℕ) {i : V} (hi : i ∉ neighbourhood adj t S) :
    seq a b K x0 x1 t i = 0 :=
  (seq_cone hK h0 h1 t hi).2

/-- [definition] **The wave scheme** `x_(t+1) = 2x_t − x_(t−1) + c² L x_t`. -/
def wave (L : Matrix V V R) (c : R) (x0 x1 : V → R) (t : ℕ) : V → R :=
  seq (fun _ => 2) (fun _ => -1) (c ^ 2 • L) x0 x1 t

/-- [proved-standard] The wave scheme's recurrence. -/
theorem wave_succ_succ (L : Matrix V V R) (c : R) (x0 x1 : V → R) (t : ℕ) (i : V) :
    wave L c x0 x1 (t + 2) i =
      2 * wave L c x0 x1 (t + 1) i - wave L c x0 x1 t i +
        c ^ 2 * ∑ j, L i j * wave L c x0 x1 (t + 1) j := by
  unfold wave
  rw [seq_succ_succ, Finset.mul_sum]
  have hs : ∑ j, (c ^ 2 • L) i j * seq (fun _ => 2) (fun _ => -1) (c ^ 2 • L) x0 x1 (t + 1) j =
      ∑ j, c ^ 2 * (L i j * seq (fun _ => 2) (fun _ => -1) (c ^ 2 • L) x0 x1 (t + 1) j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Matrix.smul_apply, smul_eq_mul, mul_assoc]
  rw [hs]
  ring

omit [Fintype V] in
/-- [proved-standard] A multiple of a local matrix is local. -/
theorem smul_local {L : Matrix V V R} (hL : Local adj L) (r : R) : Local adj (r • L) := by
  intro i j h
  refine hL i j fun h0 => h ?_
  rw [Matrix.smul_apply, h0, smul_zero]

/-- [proved-standard] **The wave scheme's cone**: from data supported on `S` at `t = 0` and `t = 1`,
the reading at `t` vanishes outside the `t`-neighbourhood of `S`, for every speed `c` and every
local `L`. -/
theorem wave_cone {L : Matrix V V R} (hL : Local adj L) (c : R) {S : Set V} {x0 x1 : V → R}
    (h0 : ∀ j, j ∉ S → x0 j = 0) (h1 : ∀ j, j ∉ S → x1 j = 0) (t : ℕ) {i : V}
    (hi : i ∉ neighbourhood adj t S) : wave L c x0 x1 t i = 0 :=
  seq_cone' (smul_local hL (c ^ 2)) h0 h1 t hi

end TwoStep

/-! ## 5. The edge is reached -/

section Reach

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {R : Type*} [Semiring R] [LinearOrder R] [IsStrictOrderedRing R]
variable {adj : V → V → Prop} {M : Matrix V V R}

/-- [proved-standard] Powers of a matrix of nonnegative entries have nonnegative entries. -/
theorem pow_apply_nonneg (hM : ∀ i j, 0 ≤ M i j) (k : ℕ) (i j : V) : 0 ≤ (M ^ k) i j := by
  induction k generalizing i with
  | zero =>
    rw [pow_zero, Matrix.one_apply]
    split_ifs
    · exact zero_le_one
    · exact le_rfl
  | succ k ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun l _ => mul_nonneg (hM i l) (ih l)

/-- [proved-standard] With positive entries on the diagonal and on every contact, the power is
positive within `k` contacts. -/
theorem pow_pos_of_near (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i, 0 < M i i)
    (ha : ∀ i j, adj i j → 0 < M i j) {k : ℕ} {i j : V} (h : Near adj k i j) :
    0 < (M ^ k) i j := by
  induction k generalizing i with
  | zero =>
    obtain rfl := near_zero.mp h
    rw [pow_zero, Matrix.one_apply_eq]
    exact zero_lt_one
  | succ k ih =>
    obtain ⟨l, hil, hl⟩ := h
    rw [pow_succ', Matrix.mul_apply]
    have hMil : 0 < M i l := by
      rcases hil with rfl | hil
      · exact hd i
      · exact ha i l hil
    exact lt_of_lt_of_le (mul_pos hMil (ih hl))
      (Finset.single_le_sum (f := fun l => M i l * (M ^ k) l j)
        (fun m _ => mul_nonneg (hM i m) (pow_apply_nonneg hM k m j)) (Finset.mem_univ l))

/-- [proved-standard] **The cone is attained**: for a local matrix of nonnegative entries, positive
on the diagonal and on every contact, `0 < (M ^ k) i j` exactly within `k` contacts. -/
theorem pow_pos_iff_near (hloc : Local adj M) (hM : ∀ i j, 0 ≤ M i j) (hd : ∀ i, 0 < M i i)
    (ha : ∀ i j, adj i j → 0 < M i j) {k : ℕ} {i j : V} :
    0 < (M ^ k) i j ↔ Near adj k i j :=
  ⟨fun h => near_of_pow_ne_zero hloc k h.ne', pow_pos_of_near hM hd ha⟩

end Reach

/-- [proved-standard] **A graph's lazy adjacency matrix reaches exactly the ball**:
`0 < ((1 + A) ^ k) i j` exactly when `j` is reachable from `i` with `dist i j ≤ k`. -/
theorem lazy_adjMatrix_pow_pos_iff {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (i j : V) :
    0 < ((1 + G.adjMatrix ℕ) ^ k) i j ↔ G.Reachable i j ∧ G.dist i j ≤ k := by
  rw [← near_iff_dist_le]
  refine pow_pos_iff_near ?_ (fun _ _ => Nat.zero_le _) ?_ ?_
  · intro a b h
    by_contra hc
    push Not at hc
    apply h
    simp [Matrix.add_apply, SimpleGraph.adjMatrix_apply, hc.1, hc.2]
  · intro a
    simp [Matrix.add_apply, SimpleGraph.adjMatrix_apply]
  · intro a b hab
    simp [Matrix.add_apply, Matrix.one_apply, SimpleGraph.adjMatrix_apply, hab]

/-! ## 6. The chain is the case of a path -/

section Chain

open Holonics.Physics.Wave

/-- [definition] **The path on `ℤ`**: each cell touches its two neighbours. -/
def pathAdj (i j : ℤ) : Prop := j = i + 1 ∨ j = i - 1

/-- [proved-standard] Within `k` contacts on the path is at most `k` cells away. -/
theorem near_path_le {k : ℕ} {i j : ℤ} (h : Near pathAdj k i j) : |i - j| ≤ k := by
  induction k generalizing i with
  | zero =>
    obtain rfl := near_zero.mp h
    simp
  | succ k ih =>
    obtain ⟨l, hil, hl⟩ := h
    have hk := ih hl
    rw [abs_le] at hk ⊢
    rcases hil with rfl | rfl | rfl <;> omega

/-- [proved-standard] At most `k` cells away on the path is within `k` contacts. -/
theorem near_path_of_le {k : ℕ} {i j : ℤ} (h : |i - j| ≤ k) : Near pathAdj k i j := by
  induction k generalizing i with
  | zero =>
    rw [abs_le] at h
    exact near_zero.mpr (by omega)
  | succ k ih =>
    rw [abs_le] at h
    rcases lt_trichotomy i j with hij | hij | hij
    · exact ⟨i + 1, Or.inr (Or.inl rfl), ih (by rw [abs_le]; omega)⟩
    · exact hij ▸ near_refl _ _ _
    · exact ⟨i - 1, Or.inr (Or.inr rfl), ih (by rw [abs_le]; omega)⟩

/-- [proved-standard] **The path's ball is the interval**: `Near pathAdj k i j ↔ |i − j| ≤ k`. -/
theorem near_path_iff {k : ℕ} {i j : ℤ} : Near pathAdj k i j ↔ |i - j| ≤ k :=
  ⟨near_path_le, near_path_of_le⟩

/-- [definition] The reading of a chain state at a cell: the node's voltage and the current of the
junction to its right. -/
def readChain (x : Telegrapher.State) (i : ℤ) : ℚ × ℚ := (x.V i, x.I i)

/-- [proved-standard] **The telegrapher's tick is a local tick of the path**, for every material,
tick length and source. -/
theorem telegrapher_step_local (m : Telegrapher.Material) (h s : ℚ) :
    LocalStep pathAdj readChain (Telegrapher.step m h s) := by
  intro x y i hxy
  have h0 := hxy i (Or.inl rfl)
  have hp := hxy (i + 1) (Or.inr (Or.inl rfl))
  have hm := hxy (i - 1) (Or.inr (Or.inr rfl))
  have hV0 : x.V i = y.V i := congrArg Prod.fst h0
  have hI0 : x.I i = y.I i := congrArg Prod.snd h0
  have hVp : x.V (i + 1) = y.V (i + 1) := congrArg Prod.fst hp
  have hVm : x.V (i - 1) = y.V (i - 1) := congrArg Prod.fst hm
  have hIm : x.I (i - 1) = y.I (i - 1) := congrArg Prod.snd hm
  show ((Telegrapher.step m h s x).V i, (Telegrapher.step m h s x).I i) =
    ((Telegrapher.step m h s y).V i, (Telegrapher.step m h s y).I i)
  simp only [Telegrapher.step, Telegrapher.currentStep, sub_add_cancel]
  rw [hV0, hI0, hVp, hVm, hIm]

/-- [proved-standard] The chain's propagation is the run of its ticks. -/
theorem telegrapher_run_eq (m : Telegrapher.Material) (h : ℚ) (src : ℕ → ℚ)
    (x : Telegrapher.State) (n : ℕ) :
    Telegrapher.run m h src x n = run (fun t => Telegrapher.step m h (src t)) n x := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Telegrapher.run_succ, run_succ, ih]

/-- [proved-standard] **The chain's cone, from the path.** Two chain states that agree outside
`[lo, hi]` (voltages and the currents to the right of those cells) agree outside
`[lo − n, hi + n]` after `n` ticks under one source schedule, whatever the material. -/
theorem chain_cone (m : Telegrapher.Material) (h : ℚ) (src : ℕ → ℚ) {lo hi : ℤ}
    {x y : Telegrapher.State} (hxy : ∀ j, (j < lo ∨ hi < j) → x.V j = y.V j ∧ x.I j = y.I j)
    (n : ℕ) {i : ℤ} (hi' : i < lo - n ∨ hi + n < i) :
    (Telegrapher.run m h src x n).V i = (Telegrapher.run m h src y n).V i ∧
      (Telegrapher.run m h src x n).I i = (Telegrapher.run m h src y n).I i := by
  have key : readChain (run (fun t => Telegrapher.step m h (src t)) n x) i =
      readChain (run (fun t => Telegrapher.step m h (src t)) n y) i := by
    refine cone (fun t => telegrapher_step_local m h (src t)) n fun j hj => ?_
    have hk := near_path_le hj
    rw [abs_le] at hk
    obtain ⟨hv, hI⟩ := hxy j (by omega)
    exact Prod.ext hv hI
  rw [← telegrapher_run_eq, ← telegrapher_run_eq] at key
  exact ⟨congrArg Prod.fst key, congrArg Prod.snd key⟩

/-- [proved-standard] **The nodes' statement of the chain** (`Telegrapher`'s
`change_moves_one_cell_per_tick`, at the voltages): two states whose difference is supported in
`[lo, hi]` have equal voltages outside `[lo − n, hi + n]` after `n` ticks. -/
theorem chain_nodes_cone (m : Telegrapher.Material) (h : ℚ) (src : ℕ → ℚ) {lo hi : ℤ}
    {x y : Telegrapher.State} (hxy : Telegrapher.Supported lo hi (x - y)) (n : ℕ) {i : ℤ}
    (hi' : i < lo - n ∨ hi + n < i) :
    (Telegrapher.run m h src x n).V i = (Telegrapher.run m h src y n).V i := by
  refine (chain_cone m h src (fun j hj => ⟨?_, ?_⟩) n hi').1
  · have hV := hxy.1 j hj
    rw [Telegrapher.sub_V, Pi.sub_apply] at hV
    exact sub_eq_zero.mp hV
  · have hI := hxy.2 j (hj.elim Or.inl fun hlt => Or.inr hlt.le)
    rw [Telegrapher.sub_I, Pi.sub_apply] at hI
    exact sub_eq_zero.mp hI

end Chain

end Holonics.Physics.Wave.GraphCone
