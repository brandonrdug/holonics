import Mathlib.Tactic

/-!
# The device launch law: coverage, guard, and per-thread exclusive write regions

This is the Lean owner paired with `crates/holonic-mount/src/launch_law.rs`.  Every structure here
has an executable equivalent in that module and every theorem here appears there as an invariant
or a test.  The Rust side cites these declaration names; this file cites the Rust items.

Two laws are formalized.

**D1 — the launch is a passage and owes a receipt.**  A launch shape is a grid of blocks.  It
*covers* a declared element extent when `grid * block ≥ extent`, and the kernel carries an in-range
`guard` so that every thread at or beyond the extent is a no-op.  `LaunchShape.cover` is the
ceiling-division shape; it covers, and its guarded tail is strictly narrower than one block
(`LaunchShape.cover_tail`), which is the overflow-free bound the Rust checked arithmetic enforces.
`foldl_guarded_cover` is the exactness statement: launching a covering guarded shape over
`range (grid * block)` produces *exactly* the unguarded effect over `range extent`.

The one-thread-per-element correspondence is stated at two strengths, and the difference matters.
`exists_unique_thread` is the **weak** form: it says a declared element is named by exactly one
*flat* index below the thread population, which is near tautological, since `Fin s.threads` is by
construction `[0, s.threads)`.  The **content-carrying** forms quantify over the launch's own
two-level indexing `blockIdx * blockDim + threadIdx` (`LaunchShape.linearIndex`):
`linear_thread_bijective` proves that map is a bijection onto `[0, n)` under an exact cover, and
`linear_thread_injective_guarded` proves it is injective under a guarded cover, that every declared
element is still named exactly once, and that the in-range guard turns off *exactly* `threads - n`
threads.  The Rust receipt's `CoverageExact` and `CoverageGuarded` clauses are the second pair.

**D2 — exclusive access is a type.**  A `DisjointPartition` carries, as proof fields, that the
per-thread write regions are pairwise disjoint and contained in the span.  Two constructors are
provided and are the only two the Rust owner exposes: a uniform stride/width form
(`DisjointPartition.uniform`) and an explicit monotone offsets table (`DisjointPartition.ofOffsets`).
Race freedom is likewise stated at two strengths, and the docstrings say which is which.

* **The coarse statement.**  `write_right_comm` proves that per-thread updates commute when each
  thread performs *one atomic write over its whole region*, and `raceFree` concludes that any
  **permutation of the threads** yields the same final device state.  `foldl_write_mem` and
  `foldl_write_notMem` pin down what that state is, so it is exactness and not merely agreement.
  It does not model a thread as issuing several stores.
* **The fine statement.**  A `Store` is one single-address write; a thread's program is a *list* of
  them, all addressed inside its own region (`Programmed`); an **interleaving** is any merge of the
  threads' lists that preserves each thread's internal order (`Interleaves`, stated as: filtering
  the merged list by thread recovers that thread's list).  `raceFreeInterleaved` proves any two
  interleavings leave the same final state, and `shuffleWrites_eq_sequential` proves that state is
  the one the **sequential** schedule leaves.  `foldl_store_apply` pins it down exactly: at every
  address the final value is what the last store to that address wrote.  This is the statement the
  Rust `PartitionedWrite::scope` carries.

The D3 seam is stated here rather than assumed: a scatter through an *injective* index map is
order-independent (`scatter_perm`), a scatter through a colliding index map is order-dependent
(`scatter_order_dependent`, an explicit counterexample), and a scatter through an
associative-commutative accumulation is order-independent regardless of collisions
(`scatterAdd_perm`).
-/

namespace Soma.Holonics.Foundation.DeviceLaunchLaw

universe u v

/-! ## D1 — the launch shape and its coverage -/

/-- [definition] One flattened launch shape: a grid of blocks, each of `block` threads.  The Rust
equivalent is `launch_law::LaunchShape`, whose `Dim3` grid and block are flattened by checked
multiplication before they are compared with this model. -/
structure LaunchShape where
  /-- The number of blocks. -/
  grid : ℕ
  /-- The number of threads in one block. -/
  block : ℕ
deriving DecidableEq, Repr

namespace LaunchShape

/-- [definition] The total thread population of a launch. -/
def threads (s : LaunchShape) : ℕ := s.grid * s.block

/-- [definition] The ceiling-division shape covering `n` elements at a declared block extent.
The Rust equivalent is `LaunchRequirement::cover_with`, which derives exactly this shape from the
device census and then submits it to the same proof obligation any caller-authored shape faces. -/
def cover (n block : ℕ) : LaunchShape := ⟨(n + block - 1) / block, block⟩

@[simp] theorem cover_block (n b : ℕ) : (cover n b).block = b := rfl

/-- [proved-derived; formal-checked] The ceiling-division shape covers its declared extent. -/
theorem cover_covers (n b : ℕ) (hb : 0 < b) : n ≤ (cover n b).threads := by
  have hdm : b * ((n + b - 1) / b) + (n + b - 1) % b = n + b - 1 := Nat.div_add_mod _ _
  have hmod : (n + b - 1) % b < b := Nat.mod_lt _ hb
  have hcomm : (n + b - 1) / b * b = b * ((n + b - 1) / b) := Nat.mul_comm _ _
  show n ≤ (n + b - 1) / b * b
  rw [hcomm]
  generalize (b * ((n + b - 1) / b)) = A at hdm ⊢
  omega

/-- [proved-derived; formal-checked] The guarded tail of the ceiling-division shape is strictly
narrower than one block.  This is the bound that makes the launch overflow-free under the stated
extent: the thread population never exceeds `n + block`, so a caller holding `n < N` and
`block ≤ B` knows the product stays below `N + B` without evaluating it. -/
theorem cover_tail (n b : ℕ) (hn : 0 < n) : (cover n b).threads < n + b := by
  have hle : (n + b - 1) / b * b ≤ n + b - 1 := Nat.div_mul_le_self _ _
  show (n + b - 1) / b * b < n + b
  omega

/-- [proved-derived; formal-checked] Overflow-freedom under declared bounds: a shape whose grid and
block are separately bounded has a thread population bounded by the product of the bounds.  The
Rust owner performs this comparison in `u64` with `checked_mul`, refusing rather than wrapping. -/
theorem threads_lt_wire {s : LaunchShape} {G B W : ℕ} (hg : s.grid ≤ G) (hb : s.block ≤ B)
    (h : G * B < W) : s.threads < W :=
  lt_of_le_of_lt (Nat.mul_le_mul hg hb) h

end LaunchShape

/-- [definition] A launch covers an extent when its thread population reaches it. -/
def Covers (s : LaunchShape) (n : ℕ) : Prop := n ≤ s.threads

/-- [proved-derived; formal-checked] **The weak form**, retained because the Rust receipt cites it:
under coverage, a declared element `i < n` is named by exactly one *flat* thread index below the
thread population.  It says nothing about the launch's own two-level indexing and is near
tautological — `Fin s.threads` is by definition `[0, s.threads)`.  The statement that carries
content is `linear_thread_bijective` / `linear_thread_injective_guarded` below, which quantify over
the actual `blockIdx * blockDim + threadIdx` linearization. -/
theorem exists_unique_thread {s : LaunchShape} {n : ℕ} (h : Covers s n) {i : ℕ} (hi : i < n) :
    ∃! t : Fin s.threads, (t : ℕ) = i := by
  refine ⟨⟨i, lt_of_lt_of_le hi h⟩, rfl, ?_⟩
  intro t ht
  exact Fin.ext ht

/-! ### The launch's own thread linearization

The device does not hand a kernel a flat thread index: it hands it `blockIdx` and `threadIdx`, and
the kernel computes `blockIdx * blockDim + threadIdx` itself.  Everything below is stated about
*that* map, so the exactness claim is about the indexing the kernel actually performs. -/

/-- [definition] The launch's own thread linearization, `blockIdx * blockDim + threadIdx`.  The
Rust equivalent is the `x_stride` wire on `LaunchReceipt`, which is `grid.x * block.x`, and the
`i = blockIdx.x * blockDim.x + threadIdx.x` every migrated kernel computes. -/
def LaunchShape.linearIndex (s : LaunchShape) (p : Fin s.grid × Fin s.block) : ℕ :=
  p.1.val * s.block + p.2.val

namespace LaunchShape

/-- [proved-derived; formal-checked] Every thread of the launch addresses an element below the
thread population. -/
theorem linearIndex_lt (s : LaunchShape) (p : Fin s.grid × Fin s.block) :
    s.linearIndex p < s.threads := by
  obtain ⟨b, t⟩ := p
  have ht : t.val < s.block := t.isLt
  have hb : b.val + 1 ≤ s.grid := b.isLt
  have hstep : b.val * s.block + t.val < (b.val + 1) * s.block := by
    have : (b.val + 1) * s.block = b.val * s.block + s.block := by ring
    omega
  have hgrid : (b.val + 1) * s.block ≤ s.grid * s.block := Nat.mul_le_mul_right _ hb
  simpa [linearIndex, threads] using lt_of_lt_of_le hstep hgrid

/-- [proved-derived; formal-checked] **No two threads address the same element.**  This is the
division-with-remainder uniqueness behind `blockIdx * blockDim + threadIdx`, and it is what makes a
per-thread exclusive span meaningful in the first place. -/
theorem linearIndex_injective (s : LaunchShape) : Function.Injective s.linearIndex := by
  rintro ⟨b₁, t₁⟩ ⟨b₂, t₂⟩ h
  simp only [linearIndex] at h
  have hB : 0 < s.block := lt_of_le_of_lt (Nat.zero_le _) t₁.isLt
  have hb : b₁.val = b₂.val := by
    have e1 : (b₁.val * s.block + t₁.val) / s.block = b₁.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt t₁.isLt, Nat.add_zero]
    have e2 : (b₂.val * s.block + t₂.val) / s.block = b₂.val := by
      rw [Nat.mul_comm, Nat.mul_add_div hB, Nat.div_eq_of_lt t₂.isLt, Nat.add_zero]
    rw [← e1, ← e2, h]
  have ht : t₁.val = t₂.val := by
    rw [hb] at h
    exact Nat.add_left_cancel h
  exact Prod.ext (Fin.ext hb) (Fin.ext ht)

/-- [proved-derived; formal-checked] Every element below the thread population is addressed. -/
theorem linearIndex_surjective (s : LaunchShape) {i : ℕ} (hi : i < s.threads) :
    ∃ p : Fin s.grid × Fin s.block, s.linearIndex p = i := by
  have hB : 0 < s.block := by
    rcases Nat.eq_zero_or_pos s.block with h | h
    · simp [threads, h] at hi
    · exact h
  have hblock : i % s.block < s.block := Nat.mod_lt _ hB
  have hgrid : i / s.block < s.grid := by
    rw [Nat.div_lt_iff_lt_mul hB]
    simpa [threads, Nat.mul_comm] using hi
  refine ⟨⟨⟨i / s.block, hgrid⟩, ⟨i % s.block, hblock⟩⟩, ?_⟩
  simpa [linearIndex, Nat.mul_comm] using Nat.div_add_mod i s.block

/-- [proved-derived; formal-checked] **The exact-cover statement.**  When the thread population
equals the declared extent, `blockIdx * blockDim + threadIdx` is a *bijection* onto `[0, n)`: it is
injective, and an element is declared exactly when some thread addresses it.  This is what
`LaunchClause::CoverageExact` asserts, and it is strictly stronger than `exists_unique_thread`,
which only re-states that `Fin s.threads` enumerates `[0, s.threads)`. -/
theorem linear_thread_bijective {s : LaunchShape} {n : ℕ} (hexact : s.threads = n) :
    Function.Injective s.linearIndex ∧
      ∀ i : ℕ, i < n ↔ ∃ p : Fin s.grid × Fin s.block, s.linearIndex p = i := by
  refine ⟨linearIndex_injective s, fun i => ⟨fun hi => ?_, ?_⟩⟩
  · exact linearIndex_surjective s (by omega)
  · rintro ⟨p, rfl⟩
    have := linearIndex_lt s p
    omega

/-- [proved-derived; formal-checked] **The guarded-cover statement.**  When the thread population
merely covers the declared extent, `blockIdx * blockDim + threadIdx` is still injective, every
declared element is addressed by exactly one thread, and the in-range guard turns off *exactly*
`threads - n` threads — the tail is accounted for rather than assumed small.  The Rust owner
records that number as `LaunchReceipt.guard_threads` and refuses a shape whose tail reaches one
whole block. -/
theorem linear_thread_injective_guarded {s : LaunchShape} {n : ℕ} (h : Covers s n) :
    Function.Injective s.linearIndex ∧
      (∀ i : ℕ, i < n → ∃! p : Fin s.grid × Fin s.block, s.linearIndex p = i) ∧
      (Finset.univ.filter fun p : Fin s.grid × Fin s.block => ¬ s.linearIndex p < n).card
        = s.threads - n := by
  have hinj := linearIndex_injective s
  refine ⟨hinj, fun i hi => ?_, ?_⟩
  · obtain ⟨p, hp⟩ := linearIndex_surjective s (lt_of_lt_of_le hi h)
    exact ⟨p, hp, fun q hq => hinj (hq.trans hp.symm)⟩
  · -- The addressed threads are in bijection with `[0, n)`, so the guarded ones are the rest.
    have hcard : Fintype.card (Fin s.grid × Fin s.block) = s.threads := by
      simp [threads]
    have hbij :
        (Finset.univ.filter fun p : Fin s.grid × Fin s.block => s.linearIndex p < n).card
          = (Finset.range n).card := by
      refine Finset.card_bij (fun p _ => s.linearIndex p) ?_ ?_ ?_
      · intro p hp
        exact Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
      · intro p _ q _ hpq
        exact hinj hpq
      · intro i hi
        have hlt : i < n := Finset.mem_range.mp hi
        obtain ⟨p, hp⟩ := linearIndex_surjective s (lt_of_lt_of_le hlt h)
        exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [hp]; exact hlt⟩, hp⟩
    have hin :
        (Finset.univ.filter fun p : Fin s.grid × Fin s.block => s.linearIndex p < n).card = n := by
      simpa using hbij
    have hsplit :
        (Finset.univ.filter fun p : Fin s.grid × Fin s.block => s.linearIndex p < n).card
          + (Finset.univ.filter fun p : Fin s.grid × Fin s.block => ¬ s.linearIndex p < n).card
          = (Finset.univ : Finset (Fin s.grid × Fin s.block)).card :=
      Finset.card_filter_add_card_filter_not _
    rw [hin, Finset.card_univ, hcard] at hsplit
    omega

end LaunchShape

/-! ### The in-range guard makes the surplus threads no-ops -/

/-- [definition] The in-range guard a covering kernel carries: thread `t` acts only when it
addresses a declared element. -/
def guarded {S : Type u} (n : ℕ) (step : ℕ → S → S) (t : ℕ) (σ : S) : S :=
  if t < n then step t σ else σ

/-- [proved-derived; formal-checked] Every thread at or beyond the declared extent is a no-op. -/
theorem guarded_of_le {S : Type u} {n t : ℕ} (h : n ≤ t) (step : ℕ → S → S) (σ : S) :
    guarded n step t σ = σ := by
  simp [guarded, Nat.not_lt.mpr h]

/-- [proved-derived; formal-checked] Inside the declared extent the guard is transparent. -/
theorem foldl_guarded_of_lt {S : Type u} (n : ℕ) (step : ℕ → S → S) :
    ∀ (l : List ℕ), (∀ t ∈ l, t < n) → ∀ σ : S,
      l.foldl (fun σ t => guarded n step t σ) σ = l.foldl (fun σ t => step t σ) σ := by
  intro l
  induction l with
  | nil => intro _ σ; rfl
  | cons x rest ih =>
    intro hlt σ
    have hx : x < n := hlt x (List.mem_cons_self ..)
    have hrest : ∀ t ∈ rest, t < n := fun t ht => hlt t (List.mem_cons_of_mem _ ht)
    simp only [List.foldl_cons, guarded, if_pos hx]
    exact ih hrest _

/-- [proved-derived; formal-checked] Surplus threads past the declared extent change nothing. -/
theorem foldl_guarded_extra {S : Type u} (n : ℕ) (step : ℕ → S → S) :
    ∀ (k : ℕ) (σ : S),
      (List.range (n + k)).foldl (fun σ t => guarded n step t σ) σ
        = (List.range n).foldl (fun σ t => guarded n step t σ) σ := by
  intro k
  induction k with
  | zero => intro σ; simp
  | succ k ih =>
    intro σ
    have hstep : n + (k + 1) = (n + k) + 1 := by omega
    rw [hstep, List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [guarded_of_le (by omega) step _]
    exact ih σ

/-- [proved-derived; formal-checked] **The D1 exactness theorem.**  A guarded launch whose thread
population covers the declared extent produces exactly the result of the extent's own threads, no
more and no less.  A launch shape is therefore a contract provable at the call site: coverage plus
the guard is equivalent to running the declared work. -/
theorem foldl_guarded_cover {S : Type u} {s : LaunchShape} {n : ℕ} (h : Covers s n)
    (step : ℕ → S → S) (σ : S) :
    (List.range s.threads).foldl (fun σ t => guarded n step t σ) σ
      = (List.range n).foldl (fun σ t => step t σ) σ := by
  have hcov : n ≤ s.threads := h
  obtain ⟨k, hk⟩ : ∃ k, s.threads = n + k := ⟨s.threads - n, by omega⟩
  rw [hk, foldl_guarded_extra n step k σ]
  exact foldl_guarded_of_lt n step (List.range n) (fun t ht => List.mem_range.mp ht) σ

/-! ## D2 — exclusive access is a type -/

/-- [definition] A partition of `[0, span)` into `regions` pairwise disjoint write regions.  The
separation field is stated in the ordered form `i < j → hi i ≤ lo j`, which both admissible
constructors satisfy directly and from which symmetric disjointness follows.  The Rust equivalent
is `launch_law::DisjointPartition`, whose only constructors are the two below. -/
structure DisjointPartition (span regions : ℕ) where
  /-- The first address of region `i`. -/
  lo : ℕ → ℕ
  /-- The address one past the end of region `i`. -/
  hi : ℕ → ℕ
  /-- Every region is well formed. -/
  lo_le_hi : ∀ i, i < regions → lo i ≤ hi i
  /-- Every region stays inside the span. -/
  hi_le_span : ∀ i, i < regions → hi i ≤ span
  /-- Regions are separated in address order. -/
  separated : ∀ i j, i < regions → j < regions → i < j → hi i ≤ lo j

namespace DisjointPartition

variable {span regions : ℕ}

/-- [definition] The address set thread `i` may write. -/
def region (P : DisjointPartition span regions) (i : ℕ) : Finset ℕ :=
  Finset.Ico (P.lo i) (P.hi i)

@[simp] theorem mem_region (P : DisjointPartition span regions) (i a : ℕ) :
    a ∈ P.region i ↔ P.lo i ≤ a ∧ a < P.hi i := Finset.mem_Ico

/-- [proved-derived; formal-checked] Distinct threads write disjoint regions:
`region i ∩ region j = ∅` for `i ≠ j`.  This is the Rust owner's
`DisjointPartition::verify_pairwise_disjoint` receipt. -/
theorem region_disjoint (P : DisjointPartition span regions) {i j : ℕ}
    (hi : i < regions) (hj : j < regions) (hne : i ≠ j) :
    Disjoint (P.region i) (P.region j) := by
  rw [Finset.disjoint_left]
  intro a hai haj
  rw [mem_region] at hai haj
  rcases Nat.lt_or_ge i j with hlt | hge
  · have := P.separated i j hi hj hlt
    omega
  · have hlt : j < i := by omega
    have := P.separated j i hj hi hlt
    omega

/-- [proved-derived; formal-checked] The union of the regions stays inside the span. -/
theorem region_subset (P : DisjointPartition span regions) {i : ℕ} (h : i < regions) :
    P.region i ⊆ Finset.range span := by
  intro a ha
  rw [mem_region] at ha
  rw [Finset.mem_range]
  exact lt_of_lt_of_le ha.2 (P.hi_le_span i h)

/-- [definition] The uniform stride form: region `i` is `[i * stride, i * stride + width)`.  This
is the proof-carrying description the Rust `DisjointPartition::uniform` validates with checked
arithmetic; `width ≤ stride` and `regions * stride ≤ span` are the two declared clauses. -/
def uniform (span regions stride width : ℕ) (hw : width ≤ stride)
    (hcover : regions * stride ≤ span) : DisjointPartition span regions where
  lo i := i * stride
  hi i := i * stride + width
  lo_le_hi := by intro i _; exact Nat.le_add_right _ _
  hi_le_span := by
    intro i hi
    calc i * stride + width ≤ i * stride + stride := Nat.add_le_add_left hw _
      _ = (i + 1) * stride := by ring
      _ ≤ regions * stride := Nat.mul_le_mul (by omega) (le_refl stride)
      _ ≤ span := hcover
  separated := by
    intro i j _ _ hij
    calc i * stride + width ≤ i * stride + stride := Nat.add_le_add_left hw _
      _ = (i + 1) * stride := by ring
      _ ≤ j * stride := Nat.mul_le_mul (by omega) (le_refl stride)

/-- [proved-derived; formal-checked] A monotone offsets table is monotone between any two of its
in-range indices.  The Rust owner validates monotonicity one adjacent pair at a time; this is the
proof that adjacent validation is sufficient. -/
theorem offsets_mono {off : ℕ → ℕ} {regions : ℕ}
    (mono : ∀ i, i < regions → off i ≤ off (i + 1)) :
    ∀ a b, a ≤ b → b ≤ regions → off a ≤ off b := by
  intro a b
  induction b with
  | zero => intro hab _; have : a = 0 := Nat.le_zero.mp hab; subst this; exact le_refl _
  | succ k ih =>
    intro hab hb
    rcases Nat.lt_or_ge a (k + 1) with h | h
    · exact le_trans (ih (by omega) (by omega)) (mono k (by omega))
    · have : a = k + 1 := by omega
      subst this
      exact le_refl _

/-- [definition] The explicit offsets form: region `i` is `[off i, off (i+1))`, admitted only from
a table validated exactly as monotone and in bounds.  Empty regions are lawful and vacuously
disjoint.  The Rust equivalent is `DisjointPartition::from_offsets`. -/
def ofOffsets (span regions : ℕ) (off : ℕ → ℕ)
    (mono : ∀ i, i < regions → off i ≤ off (i + 1)) (bound : off regions ≤ span) :
    DisjointPartition span regions where
  lo := off
  hi i := off (i + 1)
  lo_le_hi := by intro i hi; exact mono i hi
  hi_le_span := by
    intro i hi
    exact le_trans (offsets_mono mono (i + 1) regions (by omega) (le_refl _)) bound
  separated := by
    intro i j _ hj hij
    exact offsets_mono mono (i + 1) j (by omega) (by omega)

/-! ### Race-freedom of a partitioned kernel -/

/-- [definition] The device state: a total map from address to value. -/
abbrev State (V : Type v) := ℕ → V

/-- [definition] Thread `t` writes `w t a` at every address of its own region and touches nothing
else.  Threads are indexed by `Fin regions`, which is the Lean reading of the Rust owner's rule
that a `PartitionedWrite` hands out one write handle per region and no more. -/
def write {V : Type v} (P : DisjointPartition span regions) (w : ℕ → ℕ → V)
    (σ : State V) (t : Fin regions) : State V :=
  fun a => if a ∈ P.region t.val then w t.val a else σ a

/-- [proved-derived; formal-checked] Per-thread updates under a disjoint partition commute. -/
theorem write_right_comm {V : Type v} (P : DisjointPartition span regions) (w : ℕ → ℕ → V)
    (σ : State V) (t u : Fin regions) :
    write P w (write P w σ t) u = write P w (write P w σ u) t := by
  rcases eq_or_ne t u with rfl | hne
  · rfl
  have hdisj : Disjoint (P.region t.val) (P.region u.val) :=
    P.region_disjoint t.isLt u.isLt (fun h => hne (Fin.ext h))
  funext a
  by_cases ht : a ∈ P.region t.val <;> by_cases hu : a ∈ P.region u.val
  · exact absurd hu (Finset.disjoint_left.mp hdisj ht)
  all_goals simp [write, ht, hu]

/-- [proved-derived; formal-checked] A fold is invariant under permutation of its list whenever the
folded operation is right-commutative.  Proved here rather than imported so the race-freedom
theorem depends on nothing but this file. -/
theorem foldl_perm {α : Type u} {S : Type v} {f : S → α → S}
    (h : ∀ s a b, f (f s a) b = f (f s b) a) {l₁ l₂ : List α} (p : l₁.Perm l₂) :
    ∀ s : S, l₁.foldl f s = l₂.foldl f s := by
  induction p with
  | nil => intro s; rfl
  | cons a _ ih => intro s; simpa using ih (f s a)
  | swap a b l => intro s; simp only [List.foldl_cons]; rw [h]
  | trans _ _ ih₁ ih₂ => intro s; exact (ih₁ s).trans (ih₂ s)

/-- [proved-derived; formal-checked] **The D2 race-freedom theorem.**  A kernel whose thread `t`
writes only inside `region t` of a `DisjointPartition` is race-free: every interleaving of the
threads yields the same final device state.  This is the law the Rust `PartitionedWrite` type
carries; the borrow checker enforces the hypothesis, this theorem supplies the conclusion. -/
theorem raceFree {V : Type v} (P : DisjointPartition span regions) (w : ℕ → ℕ → V)
    (σ : State V) {l₁ l₂ : List (Fin regions)} (p : l₁.Perm l₂) :
    l₁.foldl (write P w) σ = l₂.foldl (write P w) σ :=
  foldl_perm (write_right_comm P w) p σ

/-- [proved-derived; formal-checked] Threads absent from the schedule leave the region untouched. -/
theorem foldl_write_notMem {V : Type v} (P : DisjointPartition span regions) (w : ℕ → ℕ → V)
    (t : Fin regions) {a : ℕ} (ha : a ∈ P.region t.val) :
    ∀ (l : List (Fin regions)), t ∉ l → ∀ σ : State V, (l.foldl (write P w) σ) a = σ a := by
  intro l
  induction l with
  | nil => intro _ σ; rfl
  | cons x rest ih =>
    intro hnot σ
    have hx : x ≠ t := fun h => hnot (h ▸ List.mem_cons_self ..)
    have hnotx : a ∉ P.region x.val := by
      have hdisj : Disjoint (P.region x.val) (P.region t.val) :=
        P.region_disjoint x.isLt t.isLt (fun h => hx (Fin.ext h))
      exact fun hax => (Finset.disjoint_left.mp hdisj hax) ha
    have hstep : (write P w σ x) a = σ a := by simp [write, hnotx]
    have := ih (fun h => hnot (List.mem_cons_of_mem _ h)) (write P w σ x)
    simpa [hstep] using this

/-- [proved-derived; formal-checked] The final state is exactly the per-region write: the
race-freedom theorem is exactness, not merely agreement between orders. -/
theorem foldl_write_mem {V : Type v} (P : DisjointPartition span regions) (w : ℕ → ℕ → V)
    (t : Fin regions) {a : ℕ} (ha : a ∈ P.region t.val) :
    ∀ (l : List (Fin regions)), t ∈ l → ∀ σ : State V,
      (l.foldl (write P w) σ) a = w t.val a := by
  intro l
  induction l with
  | nil => intro hmem; simp at hmem
  | cons x rest ih =>
    intro hmem σ
    by_cases hrest : t ∈ rest
    · exact ih hrest _
    · have hxt : x = t := by
        rcases List.mem_cons.mp hmem with h | h
        · exact h.symm
        · exact absurd h hrest
      subst hxt
      rw [List.foldl_cons, foldl_write_notMem P w x ha rest hrest]
      simp [write, ha]

/-! ### The finer race-freedom statement: interleaved single-address stores

`raceFree` above models a thread as **one atomic write over its whole region** and an interleaving
as a **permutation of the threads**.  That is a real statement, and it is not what a kernel does: a
thread issues a *sequence* of single-address stores, and the hardware may interleave those
sequences arbitrarily, constrained only by each thread's own program order.  The statements below
model exactly that — a thread is a *list* of single-address stores all addressed inside its own
region, an interleaving is any merge of those lists that preserves each thread's internal order,
and `shuffleWrites_eq_sequential` proves the final device state equals the one the sequential
schedule leaves.  Both statements are kept, and the docstrings say which is which. -/

/-- [definition] One single-address store: thread `thread` writes `val` at address `addr`. -/
structure Store (V : Type v) where
  /-- Which thread issued the store. -/
  thread : ℕ
  /-- The single address it writes. -/
  addr : ℕ
  /-- What it writes there. -/
  val : V

/-- [definition] Performing one store. -/
def store {V : Type v} (σ : State V) (w : Store V) : State V :=
  Function.update σ w.addr w.val

/-- [definition] The value the *last* store to `a` in a run leaves at `a`, if any store did. -/
def lastWrite {V : Type v} : List (Store V) → ℕ → Option V
  | [], _ => none
  | w :: rest, a =>
      match lastWrite rest a with
      | some v => some v
      | none => if w.addr = a then some w.val else none

/-- [proved-derived; formal-checked] A run of stores leaves at each address exactly what the last
store to that address wrote, and the initial value at every address nothing wrote. -/
theorem foldl_store_apply {V : Type v} :
    ∀ (l : List (Store V)) (σ : State V) (a : ℕ),
      (l.foldl store σ) a = (lastWrite l a).getD (σ a) := by
  intro l
  induction l with
  | nil => intro σ a; rfl
  | cons w rest ih =>
    intro σ a
    rw [List.foldl_cons, ih]
    cases hrest : lastWrite rest a with
    | some v => simp [lastWrite, hrest]
    | none =>
      by_cases hw : w.addr = a
      · subst hw
        simp [lastWrite, hrest, store]
      · have hne : a ≠ w.addr := fun h => hw h.symm
        simp [lastWrite, hrest, store, Function.update_of_ne hne, if_neg hw]

/-- [proved-derived; formal-checked] The last write to `a` depends only on the stores addressed at
`a`: everything else in the run is invisible there. -/
theorem lastWrite_filter {V : Type v} :
    ∀ (l : List (Store V)) (a : ℕ),
      lastWrite (l.filter fun w => decide (w.addr = a)) a = lastWrite l a := by
  intro l
  induction l with
  | nil => intro a; rfl
  | cons w rest ih =>
    intro a
    by_cases hw : w.addr = a
    · simp [hw, lastWrite, ih a]
    · rw [List.filter_cons_of_neg (by simp [hw]), ih a]
      cases hrest : lastWrite rest a <;> simp [lastWrite, hrest, hw]

/-- [proved-derived; formal-checked] Two runs that address every individual address in the same
order leave the same final state, whatever else they interleave. -/
theorem foldl_store_congr {V : Type v} (l₁ l₂ : List (Store V)) (σ : State V)
    (h : ∀ a : ℕ,
      (l₁.filter fun w => decide (w.addr = a)) = (l₂.filter fun w => decide (w.addr = a))) :
    l₁.foldl store σ = l₂.foldl store σ := by
  funext a
  rw [foldl_store_apply, foldl_store_apply, ← lastWrite_filter l₁ a, ← lastWrite_filter l₂ a, h a]

/-- [definition] `prog t` is thread `t`'s own program: a list of single-address stores, each
stamped with `t` and addressed **inside `t`'s own region** of the partition.  This is the Lean
reading of the Rust rule that a `PartitionedWrite` hands out one write handle per region. -/
def Programmed {V : Type v} (P : DisjointPartition span regions)
    (prog : Fin regions → List (Store V)) : Prop :=
  ∀ t : Fin regions, ∀ w ∈ prog t, w.thread = t.val ∧ w.addr ∈ P.region t.val

/-- [definition] `l` is an **interleaving** of `prog`: every store in it was issued by one of the
threads, and filtering `l` by thread recovers that thread's program *in order*.  That second
condition is precisely "any merge of the threads' lists preserving each thread's internal order". -/
def Interleaves {V : Type v} (prog : Fin regions → List (Store V)) (l : List (Store V)) : Prop :=
  (∀ w ∈ l, ∃ t : Fin regions, w.thread = t.val) ∧
    ∀ t : Fin regions, (l.filter fun w => decide (w.thread = t.val)) = prog t

/-- Every store of an interleaving is issued by a thread whose region contains its address. -/
theorem region_of_mem_interleaving {V : Type v} {P : DisjointPartition span regions}
    {prog : Fin regions → List (Store V)} (hprog : P.Programmed prog)
    {l : List (Store V)} (hl : Interleaves prog l) {w : Store V} (hw : w ∈ l) :
    ∃ t : Fin regions, w.thread = t.val ∧ w.addr ∈ P.region t.val := by
  obtain ⟨t, ht⟩ := hl.1 w hw
  have hmem : w ∈ prog t := by
    rw [← hl.2 t]
    exact List.mem_filter.mpr ⟨hw, by simp [ht]⟩
  exact ⟨t, hprog t w hmem⟩

/-- The stores of an interleaving addressed at `a` are exactly the stores of the owning thread's
own program addressed at `a` — because the regions are disjoint, no other thread can reach `a`. -/
theorem filter_addr_eq_of_interleaving {V : Type v} {P : DisjointPartition span regions}
    {prog : Fin regions → List (Store V)} (hprog : P.Programmed prog)
    {l : List (Store V)} (hl : Interleaves prog l) {a : ℕ} {t : Fin regions}
    (ha : a ∈ P.region t.val) :
    (l.filter fun w => decide (w.addr = a))
      = ((prog t).filter fun w => decide (w.addr = a)) := by
  have hstep :
      (l.filter fun w => decide (w.addr = a))
        = (l.filter fun w => decide (w.addr = a) && decide (w.thread = t.val)) := by
    refine List.filter_congr ?_
    intro w hw
    by_cases hwa : w.addr = a
    · obtain ⟨u, hu, hau⟩ := region_of_mem_interleaving hprog hl hw
      have hut : u = t := by
        by_contra hne
        have hdisj : Disjoint (P.region u.val) (P.region t.val) :=
          P.region_disjoint u.isLt t.isLt (fun h => hne (Fin.ext h))
        exact (Finset.disjoint_left.mp hdisj (hwa ▸ hau)) ha
      subst hut
      simp [hwa, hu]
    · simp [hwa]
  rw [hstep, ← List.filter_filter, hl.2 t]

/-- [proved-derived; formal-checked] **The interleaved race-freedom theorem.**  Under a disjoint
partition, *any* merge of the threads' store sequences that preserves each thread's internal order
leaves the same final device state.  Unlike `raceFree`, a thread here is a list of single-address
stores rather than one atomic whole-region write, and an interleaving is a shuffle of those lists
rather than a permutation of the threads. -/
theorem raceFreeInterleaved {V : Type v} {P : DisjointPartition span regions}
    {prog : Fin regions → List (Store V)} (hprog : P.Programmed prog)
    {l₁ l₂ : List (Store V)} (h₁ : Interleaves prog l₁) (h₂ : Interleaves prog l₂)
    (σ : State V) :
    l₁.foldl store σ = l₂.foldl store σ := by
  refine foldl_store_congr l₁ l₂ σ (fun a => ?_)
  by_cases hsome : ∃ t : Fin regions, a ∈ P.region t.val
  · obtain ⟨t, ht⟩ := hsome
    rw [filter_addr_eq_of_interleaving hprog h₁ ht,
      filter_addr_eq_of_interleaving hprog h₂ ht]
  · simp only [not_exists] at hsome
    have hnone : ∀ (l : List (Store V)), Interleaves prog l →
        (l.filter fun w => decide (w.addr = a)) = [] := by
      intro l hl
      refine List.filter_eq_nil_iff.mpr ?_
      intro w hw hwa
      obtain ⟨u, _, hau⟩ := region_of_mem_interleaving hprog hl hw
      have hwa' : w.addr = a := of_decide_eq_true hwa
      exact hsome u (hwa' ▸ hau)
    rw [hnone l₁ h₁, hnone l₂ h₂]

/-- [definition] The **sequential** schedule over a list of threads: each named thread's whole
program in turn, one thread at a time and no interleaving at all. -/
def schedule {V : Type v} (prog : Fin regions → List (Store V)) :
    List (Fin regions) → List (Store V)
  | [] => []
  | t :: rest => prog t ++ schedule prog rest

/-- [proved-derived; formal-checked] Filtering a sequential schedule by thread recovers exactly
that thread's program when it is scheduled once, and nothing when it is not. -/
theorem filter_schedule {V : Type v} {P : DisjointPartition span regions}
    {prog : Fin regions → List (Store V)} (hprog : P.Programmed prog) (t : Fin regions) :
    ∀ (ts : List (Fin regions)), ts.Nodup →
      ((schedule prog ts).filter fun w => decide (w.thread = t.val))
        = if t ∈ ts then prog t else [] := by
  intro ts
  induction ts with
  | nil => intro _; simp [schedule]
  | cons u rest ih =>
    intro hnodup
    have hunotin : u ∉ rest := (List.nodup_cons.mp hnodup).1
    have hrest := ih (List.nodup_cons.mp hnodup).2
    rw [schedule, List.filter_append, hrest]
    by_cases hut : u = t
    · subst hut
      have hself : ((prog u).filter fun w => decide (w.thread = u.val)) = prog u :=
        List.filter_eq_self.mpr (fun w hw => by simp [(hprog u w hw).1])
      simp [hself, hunotin]
    · have hother : ((prog u).filter fun w => decide (w.thread = t.val)) = [] := by
        refine List.filter_eq_nil_iff.mpr ?_
        intro w hw hcontra
        have hwt : w.thread = t.val := of_decide_eq_true hcontra
        have hwu : w.thread = u.val := (hprog u w hw).1
        exact hut (Fin.ext (hwu.symm.trans hwt))
      have htu : ¬ t = u := fun h => hut h.symm
      simp [hother, htu]

/-- [proved-derived; formal-checked] The sequential schedule over every thread, once, is itself an
interleaving of the programs. -/
theorem interleaves_schedule {V : Type v} {P : DisjointPartition span regions}
    {prog : Fin regions → List (Store V)} (hprog : P.Programmed prog) :
    Interleaves prog (schedule prog (List.finRange regions)) := by
  constructor
  · intro w hw
    have hmem : ∀ (ts : List (Fin regions)), w ∈ schedule prog ts →
        ∃ t : Fin regions, w ∈ prog t := by
      intro ts
      induction ts with
      | nil => intro h; simp [schedule] at h
      | cons u rest ih =>
        intro h
        rw [schedule, List.mem_append] at h
        rcases h with h | h
        · exact ⟨u, h⟩
        · exact ih h
    obtain ⟨t, ht⟩ := hmem _ hw
    exact ⟨t, (hprog t w ht).1⟩
  · intro t
    rw [filter_schedule hprog t (List.finRange regions) (List.nodup_finRange regions),
      if_pos (List.mem_finRange t)]

/-- [proved-derived; formal-checked] **The statement the Rust `PartitionedWrite::scope` carries.**
Any interleaving of the threads' single-address store sequences leaves exactly the state the
*sequential* schedule leaves: the device is free to merge the threads however it likes, and the
result is the one a reader can compute thread by thread. -/
theorem shuffleWrites_eq_sequential {V : Type v} {P : DisjointPartition span regions}
    {prog : Fin regions → List (Store V)} (hprog : P.Programmed prog)
    {l : List (Store V)} (hl : Interleaves prog l) (σ : State V) :
    l.foldl store σ = (schedule prog (List.finRange regions)).foldl store σ :=
  raceFreeInterleaved hprog hl (interleaves_schedule hprog) σ

/-! ### The D3 seam: scatter through an incidence index map -/

/-- [definition] A scatter: thread `t` writes value `v t` at the incidence address `idx t`.  Unlike
`write`, the address is data rather than a proved region, so disjointness is a property of the
index map and not of the partition. -/
def scatter {V : Type v} {m : ℕ} (idx : Fin m → ℕ) (v : Fin m → V)
    (σ : State V) (t : Fin m) : State V :=
  Function.update σ (idx t) (v t)

/-- [proved-derived; formal-checked] An injective incidence map makes scatter writes disjoint and
therefore order-independent. -/
theorem scatter_right_comm {V : Type v} {m : ℕ} {idx : Fin m → ℕ} (hinj : Function.Injective idx)
    (v : Fin m → V) (σ : State V) (t u : Fin m) :
    scatter idx v (scatter idx v σ t) u = scatter idx v (scatter idx v σ u) t := by
  rcases eq_or_ne t u with rfl | hne
  · rfl
  simp only [scatter]
  exact (Function.update_comm (fun h => hne (hinj h.symm)) (v u) (v t) σ).symm

/-- [proved-derived; formal-checked] Scatter through an injective index map is invariant under any
interleaving of the threads. -/
theorem scatter_perm {V : Type v} {m : ℕ} {idx : Fin m → ℕ} (hinj : Function.Injective idx)
    (v : Fin m → V) (σ : State V) {l₁ l₂ : List (Fin m)} (p : l₁.Perm l₂) :
    l₁.foldl (scatter idx v) σ = l₂.foldl (scatter idx v) σ :=
  foldl_perm (scatter_right_comm hinj v) p σ

/-- [counterexample; formal-checked] Scatter through a colliding (non-injective) index map is
order-dependent: two threads addressing the same slot with plain stores leave different final
states under different interleavings.  This is why the Rust
`DisjointPartition::scatter` constructor refuses a non-injective table and names the colliding
pair, and it is the exact obligation D3 inherits. -/
theorem scatter_order_dependent :
    ∃ (m : ℕ) (idx : Fin m → ℕ) (v : Fin m → ℕ) (σ : State ℕ) (t u : Fin m),
      scatter idx v (scatter idx v σ t) u ≠ scatter idx v (scatter idx v σ u) t := by
  refine ⟨2, fun _ => 0, fun t => t.val + 1, fun _ => 0, 0, 1, ?_⟩
  intro h
  have hpoint := congrFun h 0
  simp [scatter, Function.update] at hpoint

/-- [definition] A scatter through an associative-commutative accumulation: colliding threads add
into the slot instead of storing over it. -/
def scatterAdd {V : Type v} [AddCommMonoid V] {m : ℕ} (idx : Fin m → ℕ) (v : Fin m → V)
    (σ : State V) (t : Fin m) : State V :=
  fun a => if a = idx t then σ a + v t else σ a

/-- [proved-derived; formal-checked] Accumulating scatter writes commute even when the index map
collides. -/
theorem scatterAdd_right_comm {V : Type v} [AddCommMonoid V] {m : ℕ} (idx : Fin m → ℕ)
    (v : Fin m → V) (σ : State V) (t u : Fin m) :
    scatterAdd idx v (scatterAdd idx v σ t) u = scatterAdd idx v (scatterAdd idx v σ u) t := by
  funext a
  by_cases h1 : a = idx t <;> by_cases h2 : a = idx u
  · simp only [scatterAdd, if_pos h1, if_pos h2]
    exact add_right_comm _ _ _
  · simp only [scatterAdd, if_pos h1, if_neg h2]
  · simp only [scatterAdd, if_neg h1, if_pos h2]
  · simp only [scatterAdd, if_neg h1, if_neg h2]

/-- [proved-derived; formal-checked] **The D3 seam theorem.**  With an associative-commutative
accumulation the scatter is order-independent for *any* index map, injective or not.  A
non-injective incidence scatter is therefore admissible exactly when an accumulation law is
declared; without one it is refused. -/
theorem scatterAdd_perm {V : Type v} [AddCommMonoid V] {m : ℕ} (idx : Fin m → ℕ) (v : Fin m → V)
    (σ : State V) {l₁ l₂ : List (Fin m)} (p : l₁.Perm l₂) :
    l₁.foldl (scatterAdd idx v) σ = l₂.foldl (scatterAdd idx v) σ :=
  foldl_perm (scatterAdd_right_comm idx v) p σ

end DisjointPartition

end Soma.Holonics.Foundation.DeviceLaunchLaw

/-! ## Kernel receipts

Only `propext`, `Classical.choice` and `Quot.sound` are admissible. -/

#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.LaunchShape.cover_covers
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.LaunchShape.cover_tail
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.LaunchShape.threads_lt_wire
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.exists_unique_thread
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.LaunchShape.linearIndex_lt
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.LaunchShape.linearIndex_injective
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.LaunchShape.linearIndex_surjective
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.LaunchShape.linear_thread_bijective
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.LaunchShape.linear_thread_injective_guarded
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.guarded_of_le
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.foldl_guarded_cover
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.region_disjoint
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.region_subset
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.uniform
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.ofOffsets
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.write_right_comm
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.raceFree
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.foldl_store_apply
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.lastWrite_filter
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.foldl_store_congr
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.raceFreeInterleaved
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.filter_schedule
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.interleaves_schedule
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.shuffleWrites_eq_sequential
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.foldl_write_mem
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.foldl_write_notMem
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.scatter_perm
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.scatter_order_dependent
#print axioms Soma.Holonics.Foundation.DeviceLaunchLaw.DisjointPartition.scatterAdd_perm
