import Holonics.HNN.Propagation
import Holonics.Compression.Core.FaceMap
import Holonics.Aeon.Clock.Winding
import Mathlib.Data.ENat.Lattice

/-!
# HNN.Retention: the collapse onto what the admitted future distinguishes

[definition] Rebuild step 4 (#73), campaign 1, design item 6 (`docs/plans/THE_REBUILD.md`,
*Retention: the collapse onto what the admitted future distinguishes*). Between words only the
medium (the constitution `Θ` and the lift point `λ`), the open moments `M` and the pending ratios
persist. At every word's end the change is released; at an aeon boundary the constitution is
reduced to what the admitted future still distinguishes: every locus off the time-indexed causal
diamond of the source rings and the admitted receivers is released.

The laws are stated on the word's block graph (`HNN/Propagation.lean`): a locus state `θ y z` on
each block edge `z → y`, read at a class configuration `c` (the rings' phase and lock classes) as
the edge's block operator `op c (θ y z)`; a released locus takes the declared value `rel y z`, whose
operator is zero at every class (the zero map, the matched termination).

[definition] **What this file covers: the abstract model, not the concrete tick.** Every law
here that reads a word is stated for the abstract word of `HNN/Propagation` §4: a class-indexed
family of time-invariant linear block operators `readOp c θ : BlockOp K M` (`op c y z (θ y z)`),
`Sparse` on an abstract block graph `adj` (`LociSparse`), iterated by `Propagation.trajectory`.
That covers `release_indistinguishable`, `deposit_descends`, `release_structural`,
`admitted_nonincreasing`, `local_retention_blocks`, `constitution_descends`,
`blind_outside_observe`, `fieldStanding`, `contemporary_read` and `word_opens_at_zero`.
`diamond_recursion` is a statement about the recursions on any finite graph `adj`, so it applies to
the concrete ring/contact graph `HNN/Word.blockAdj` as it stands; `lift_reading` reads integer
lifts and applies to the concrete lift point as it stands. None of them is proved for
`HNN/Word.fieldTick`; the concrete tick has `fieldTick_balance`, `fieldTick_local`,
`word_tick_cone`, `elementSolve_spec` and `transitSolve_spec`. The bridge (`fieldTick` linear in the
change at fixed operands, and the `tick` of a `BlockOp` on `Ring ⊕ Contact` that is
`Sparse blockAdj`) is owed in #62, "Step 4 (#73) owed: the diamond on the concrete tick".

[proved-derived; formal-checked] What is proved.

1. **The recursions** (`diamond_recursion`). The reach recursion `r⁰ = 0 on 𝒮`,
   `r_h ← min(r_h, r_g + 1)` computes the hop distance exactly up to its round count
   (`reachRound_le_iff`); the observe recursion is the same on the reversed graph. The diamond
   rule `r_z + 1 + o_y ≤ e_last` computed from them is exactly `InDiamond`, and a block that
   observes no receiver within `n` hops lies in `Compression/Core/FaceMap.horizonBlind n` of the
   word (`blind_outside_observe`).
2. **Release is indistinguishable** (`release_indistinguishable`): the collapse changes no admitted
   reading at any class configuration, epoch `≤ e_last` or receiver (`Propagation.release_past_diamond`).
3. **Deposits descend** (`deposit_descends`, R3 R3): a deposit reads, on each block edge, the
   features and covectors at the ticks of its diamond window; with or without the collapse these
   agree on retained loci (`Propagation.trajectory_agrees_where_observed`,
   `sweep_agrees_where_reached`), and a released locus has an empty window, so
   `collapse ∘ deposit = deposit ∘ collapse`. The release is structural: no sequence of deposits
   resurrects a released locus (`release_structural`). A deposit law that moves a locus with an
   empty window breaks the descent (`deposit_descends_needs_empty_window_law`), and the diamond rule
   is tight on the path witness: releasing a retained edge changes a reading
   (`retained_edge_is_read`).
4. **Admitted families may only shrink** (`admitted_nonincreasing`): the collapse is sufficient for
   every later family contained in this one; a family that adds a receiver can read a released
   locus (`admitted_growth_reads_released`).
5. **The collapse is local** (`local_retention_blocks`, `constitution_descends`): a 0/1 projection
   per block edge, idempotent, inside the declared graph; retained loci keep their values and every
   admitted receiver factors through the collapse.
6. **The field's standing** (`fieldStanding`): the resident `(Θ, λ, M, pending)` with generators
   ingest, re-keying (locate keys), refine and deposit, observations the admitted faces of the
   current word and of every pending ratio at the contemporary constitution, and `retain` the
   collapse, is a `Foundation/Standing.StandingLaw`. The word opens at zero change and is linear in
   its open state (`word_opens_at_zero`); a pending ratio's read is unchanged by every intervening
   generator but a deposit, and after a deposit it returns exactly the residual
   (`contemporary_read`, `Propagation.word_variation_exact`). Each ring's clock reads its lift
   displacement, and an aeon closes on the clock torus exactly when every ring reads whole periods
   (`lift_reading`, `Aeon/Clock/Winding`).

[definition; agent-inferred] **The collapse and the carried remainders** (Decision 22 of the step 4
design). The collapse releases only exact complements, and a carried remainder is not one
(releasing it could move a later lattice value by a unit, and so a later admitted reading), so the
collapse releases no remainder of a retained locus and resets no deposit clock; a locus it deletes
leaves whole. Each deposit releases instead the tail of each entry below the precision its clock
has refined to, and one entry's tails sum below half a unit since the locus's founding
(`HNN/LatticeDeposit.{release_bounded_since_founding, lattice_deposit_descends}`). The carried
remainders' bits are bounded by the clock (`remainder_rat_bits_bounded`, `O(L + 2 log₂ m)`) and the
lattice entries' by their magnitudes (`lattice_bits_bounded`).

[open] Owed in #62 ("Step 4 (#73) owed"): the solved charts `H⁻¹` of the carried Grams, whose bits
follow the Hadamard bound as the Grams fill in; the word-level certificate of the lattice rule,
`Σ_ℓ K_ℓ 2^(−L_ℓ) < 1/(2L_R)`; the value-level kernel of a frozen aeon (a collapse below the loci,
campaign 3's); and the concrete-tick bridge named above.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.Retention

open Holonics.HNN.Propagation
open scoped BigOperators

/-! ## 1. The reach and observe recursions -/

section Recursion

open Classical in
/-- [definition] **The reach recursion** of the sources `S`: `r⁰_b = 0` on `S` and `⊤` elsewhere,
`r^(k+1)_b = min(r^k_b, min_(z → b) r^k_z + 1)`. The observe recursion is the same on the
reversed graph from the receivers. -/
def reachRound {B : Type*} [Fintype B] (adj : B → B → Prop) (S : Set B) : ℕ → B → ℕ∞
  | 0, b => if b ∈ S then 0 else ⊤
  | k + 1, b => min (reachRound adj S k b)
      (Finset.univ.inf fun z => if adj z b then reachRound adj S k z + 1 else ⊤)

variable {B : Type*} [Fintype B] {adj : B → B → Prop}

theorem reachRound_succ_le (S : Set B) (k : ℕ) (b : B) :
    reachRound adj S (k + 1) b ≤ reachRound adj S k b := by
  classical
  rw [reachRound]
  exact min_le_left _ _

theorem reachRound_antitone (S : Set B) {k k' : ℕ} (h : k ≤ k') (b : B) :
    reachRound adj S k' b ≤ reachRound adj S k b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact (reachRound_succ_le S _ b).trans ih

theorem reachRound_sound (S : Set B) (k : ℕ) (b : B) (t : ℕ)
    (h : reachRound adj S k b ≤ t) : b ∈ reachWithin adj S t := by
  classical
  induction k generalizing b t with
  | zero =>
    rw [reachRound] at h
    split_ifs at h with hb
    · exact ⟨b, hb, 0, Nat.zero_le _, ReachIn.refl b⟩
    · exact absurd h (by simp)
  | succ k ih =>
    rw [reachRound, min_le_iff] at h
    rcases h with h | h
    · exact ih b t h
    · rw [Finset.inf_le_iff] at h
      · obtain ⟨z, -, hz⟩ := h
        split_ifs at hz with hzb
        · have ht : 1 ≤ t := by
            by_contra h0
            push Not at h0
            interval_cases t
            have := le_trans le_add_self hz
            simp at this
          have hz' : reachRound adj S k z ≤ ((t - 1 : ℕ) : ℕ∞) := by
            have : reachRound adj S k z + 1 ≤ ((t - 1 : ℕ) : ℕ∞) + 1 := by
              rw [show ((t - 1 : ℕ) : ℕ∞) + 1 = (t : ℕ∞) by
                rw [show ((t - 1 : ℕ) : ℕ∞) + 1 = ((t - 1 + 1 : ℕ) : ℕ∞) by push_cast; ring,
                  Nat.sub_add_cancel ht]]
              exact hz
            exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
          have := reachWithin_step (ih z (t - 1) hz') hzb
          rwa [Nat.sub_add_cancel ht] at this
        · exact absurd hz (by simp)
      · exact ENat.natCast_lt_top t

theorem reachRound_complete (S : Set B) {x b : B} (hx : x ∈ S) {n : ℕ} (hr : ReachIn adj x b n)
    {k : ℕ} (hk : n ≤ k) : reachRound adj S k b ≤ n := by
  classical
  induction hr generalizing k with
  | refl =>
    refine (reachRound_antitone S (Nat.zero_le k) _).trans ?_
    simp [reachRound, hx]
  | @tail y z n _ hstep ih =>
    refine (reachRound_antitone S hk z).trans ?_
    rw [reachRound]
    refine (min_le_right _ _).trans ?_
    refine (Finset.inf_le (Finset.mem_univ y)).trans ?_
    rw [if_pos hstep, Nat.cast_add, Nat.cast_one]
    exact add_le_add_left (ih le_rfl) 1

/-- [proved-derived; formal-checked] After `k` rounds the reach recursion reads every distance up to
`k` exactly: `r^k_b ≤ t ↔ b` is within `t` hops of the sources, for every `t ≤ k`. -/
theorem reachRound_le_iff (S : Set B) {k t : ℕ} (ht : t ≤ k) (b : B) :
    reachRound adj S k b ≤ t ↔ b ∈ reachWithin adj S t := by
  refine ⟨reachRound_sound S k b t, ?_⟩
  rintro ⟨x, hx, n, hn, hr⟩
  exact (reachRound_complete S hx hr (hn.trans ht)).trans (by exact_mod_cast hn)

omit [Fintype B] in
theorem observes_iff_reachWithin_flip {R : Set B} {y : B} {m : ℕ} :
    Observes adj R y m ↔ y ∈ reachWithin (flip adj) R m := by
  constructor
  · rintro ⟨ρ, hρ, n, hn, hr⟩
    exact ⟨ρ, hρ, n, hn, hr.flip⟩
  · rintro ⟨ρ, hρ, n, hn, hr⟩
    exact ⟨ρ, hρ, n, hn, reachIn_flip_iff.mp hr⟩

/-- [definition] The observe recursion: the reach recursion of the receivers on the reversed
graph (`o_g ← min(o_g, o_h + 1)` along `g → h`). -/
def observeRound (adj : B → B → Prop) (R : Set B) (k : ℕ) (b : B) : ℕ∞ :=
  reachRound (flip adj) R k b

/-- [proved-derived; formal-checked] **The recursions decide the diamond** (R3 R1, R2). After
`e_last` rounds, an edge `z → y` lies in the causal diamond exactly when
`r_z + 1 + o_y ≤ e_last` for the computed `r` and `o`. -/
theorem diamond_recursion (S R : Set B) (eLast : ℕ) (z y : B) :
    InDiamond adj S R eLast z y ↔
      reachRound adj S eLast z + 1 + observeRound adj R eLast y ≤ eLast := by
  constructor
  · rintro ⟨j, m, hz, hy, hjm⟩
    have hr := (reachRound_le_iff S (by omega : j ≤ eLast) z).mpr hz
    have ho : observeRound adj R eLast y ≤ m :=
      (reachRound_le_iff (adj := flip adj) R (by omega : m ≤ eLast) y).mpr
        (observes_iff_reachWithin_flip.mp hy)
    calc reachRound adj S eLast z + 1 + observeRound adj R eLast y ≤ (j : ℕ∞) + 1 + m := by
          gcongr
      _ = ((j + 1 + m : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ eLast := by exact_mod_cast hjm
  · intro h
    have hr_ne : reachRound adj S eLast z ≠ ⊤ := by
      intro htop; rw [htop] at h; simp at h
    have ho_ne : observeRound adj R eLast y ≠ ⊤ := by
      intro htop; rw [htop] at h; simp at h
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hr_ne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ho_ne
    rw [← hj, ← hm] at h
    have hjm : j + 1 + m ≤ eLast := by exact_mod_cast h
    refine ⟨j, m, reachRound_sound S eLast z j (by rw [← hj]),
      observes_iff_reachWithin_flip.mpr (reachRound_sound (adj := flip adj) R eLast y m
        (by rw [hm]; rfl)), hjm⟩

end Recursion

/-! ## 2. Blind blocks are the face map's horizon-blind configurations -/

section Blind

variable {B : Type} [Fintype B] [DecidableEq B] {adj : B → B → Prop}
variable {K : Type} [Field K] {M : B → Type} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]

/-- [definition] One tick as a linear map on the block states. -/
def tickLin (T : BlockOp K M) : ((b : B) → M b) →ₗ[K] ((b : B) → M b) where
  toFun := tick T
  map_add' x y := by funext b; simp [tick, Finset.sum_add_distrib]
  map_smul' c x := by funext b; simp [tick, Finset.smul_sum]

/-- [definition] The receiving read of block `ρ`: keep block `ρ`, zero elsewhere. -/
def blockRead (ρ : B) : ((b : B) → M b) →ₗ[K] ((b : B) → M b) :=
  (LinearMap.single K M ρ).comp (LinearMap.proj ρ)

omit [DecidableEq B] in
theorem wordMap_tickLin (T : BlockOp K M) (w : List Unit) (x : (b : B) → M b) :
    Holonics.Compression.Core.FaceMap.wordMap (fun _ : Unit => tickLin T) w x =
      trajectory T x w.length := by
  induction w with
  | nil => rfl
  | cons g w ih =>
    simp only [Holonics.Compression.Core.FaceMap.wordMap, LinearMap.comp_apply, ih,
      List.length_cons]
    rfl

/-- [proved-derived; formal-checked] **A block that observes no receiver within `n` hops is
horizon-blind** (`Compression/Core/FaceMap.horizonBlind`, via `mem_horizonBlind_iff`): every change
supported on such blocks is read by no receiving block after any word of at most `n` ticks. The
face map's horizon is therefore read on the loci's sparsity by the observe recursion. -/
theorem blind_outside_observe {T : BlockOp K M} (hT : Sparse adj T) {Z : Set B}
    {x : (b : B) → M b} (hx : SupportedIn x Z) {R : Set B} {n : ℕ}
    (hno : ∀ z ∈ Z, ¬ Observes adj R z n) :
    x ∈ Holonics.Compression.Core.FaceMap.horizonBlind (fun ρ : R => blockRead ρ.1)
      (fun _ : Unit => tickLin T) n := by
  rw [Holonics.Compression.Core.FaceMap.mem_horizonBlind_iff]
  intro ρ w hw
  rw [wordMap_tickLin]
  have hzero : trajectory T x w.length ρ.1 = 0 := by
    apply tick_causal_cone hT hx w.length ρ.1
    rintro ⟨z, hz, m, hm, hr⟩
    exact hno z hz ⟨ρ.1, ρ.2, m, hm.trans hw, hr⟩
  simp [blockRead, hzero]

end Blind

/-! ## 3. The collapse, its indistinguishability and the descent of deposits -/

section Collapse

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
variable {Cls : Type*} {Θ : B → B → Type*}
variable (op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y)) (rel : (y z : B) → Θ y z)

/-- [definition] The block operators of the loci `θ` read at the class configuration `c`. -/
def readOp (c : Cls) (θ : (y z : B) → Θ y z) : BlockOp K M := fun y z => op c y z (θ y z)

variable (adj) in
/-- [definition] The loci respect the declared block graph at every class configuration. -/
def LociSparse (θ : (y z : B) → Θ y z) : Prop := ∀ c y z, ¬ adj z y → op c y z (θ y z) = 0

variable (adj) in
open Classical in
/-- [definition] **The collapse** at an aeon boundary: every locus off the causal diamond of the
sources `S`, the admitted receivers `R` and the last epoch `e_last` is released to `rel`. -/
def collapse (S R : Set B) (eLast : ℕ) (θ : (y z : B) → Θ y z) : (y z : B) → Θ y z :=
  fun y z => if InDiamond adj S R eLast z y then θ y z else rel y z

variable {op rel}

omit [Fintype B] in
theorem collapse_of_mem {S R : Set B} {eLast : ℕ} {θ : (y z : B) → Θ y z} {y z : B}
    (h : InDiamond adj S R eLast z y) : collapse adj rel S R eLast θ y z = θ y z := by
  classical
  simp [collapse, h]

omit [Fintype B] in
theorem collapse_of_not_mem {S R : Set B} {eLast : ℕ} {θ : (y z : B) → Θ y z} {y z : B}
    (h : ¬ InDiamond adj S R eLast z y) : collapse adj rel S R eLast θ y z = rel y z := by
  classical
  simp [collapse, h]

omit [Fintype B] in
theorem lociSparse_collapse (hrel : ∀ c y z, op c y z (rel y z) = 0) {θ : (y z : B) → Θ y z}
    (hθ : LociSparse adj op θ) (S R : Set B) (eLast : ℕ) :
    LociSparse adj op (collapse adj rel S R eLast θ) := by
  intro c y z h
  by_cases hd : InDiamond adj S R eLast z y
  · rw [collapse_of_mem hd]; exact hθ c y z h
  · rw [collapse_of_not_mem hd]; exact hrel c y z

omit [Fintype B] in
theorem sparse_readOp {θ : (y z : B) → Θ y z} (hθ : LociSparse adj op θ) (c : Cls) :
    Sparse adj (readOp op c θ) := fun y z h => hθ c y z h

/-- [proved-derived; formal-checked] **Every released locus changes no admitted reading.** At every
class configuration, every epoch `t ≤ e_last` and every covector supported on the admitted
receivers, the collapsed constitution reads exactly as the constitution
(`Propagation.release_past_diamond`). -/
theorem release_indistinguishable (hrel : ∀ c y z, op c y z (rel y z) = 0)
    {θ : (y z : B) → Θ y z} (hθ : LociSparse adj op θ) {S R : Set B} {eLast t : ℕ}
    (ht : t ≤ eLast) (c : Cls) {x₀ : (b : B) → M b} (hx : SupportedIn x₀ S)
    {g : (b : B) → Module.Dual K (M b)} (hg : SupportedIn g R) :
    pair g (trajectory (readOp op c (collapse adj rel S R eLast θ)) x₀ t) =
      pair g (trajectory (readOp op c θ) x₀ t) :=
  release_past_diamond (sparse_readOp hθ c)
    (sparse_readOp (lociSparse_collapse hrel hθ S R eLast) c) hx hg ht
    fun y z hd => by simp only [readOp, collapse_of_mem hd]

/-- [definition] An admitted family of readings: epochs at most `e_last`, covectors supported on
the admitted receivers. -/
def Admitted (R : Set B) (eLast : ℕ) (rd : List (ℕ × ((b : B) → Module.Dual K (M b)))) : Prop :=
  ∀ r ∈ rd, r.1 ≤ eLast ∧ SupportedIn r.2 R

variable (adj) in
open Classical in
/-- [definition] **The diamond window** of the edge `z → y` for a reading at epoch `t`: the ticks
`k < t` at which the edge's input can be nonzero (`r_z ≤ k`) and its output can still be read
(`o_y ≤ t − 1 − k`). -/
def windowTicks (S R : Set B) (t : ℕ) (z y : B) : List ℕ :=
  (List.range t).filter fun k => z ∈ reachWithin adj S k ∧ Observes adj R y (t - 1 - k)

variable (adj) in
/-- [definition] **The data a deposit reads on the edge `z → y`**: for every admitted reading and
every tick of its diamond window, the feature `x_k(z)` of the word's own trajectory and the
covector `λ(y)` swept back to tick `k + 1`. -/
def depositData (T : BlockOp K M) (x₀ : (b : B) → M b) (S R : Set B)
    (rd : List (ℕ × ((b : B) → Module.Dual K (M b)))) (z y : B) :
    List (M z × Module.Dual K (M y)) :=
  rd.flatMap fun r => (windowTicks adj S R r.1 z y).map fun k =>
    (trajectory T x₀ k z, sweep T r.2 (r.1 - 1 - k) y)

variable (adj op) in
open Classical in
/-- [definition] **The deposit**: on each declared edge the locus law `Φ` reads its own state and
its window's data; nothing else changes. -/
def deposit (Φ : (y z : B) → Θ y z → List (M z × Module.Dual K (M y)) → Θ y z) (S R : Set B)
    (c : Cls) (x₀ : (b : B) → M b) (rd : List (ℕ × ((b : B) → Module.Dual K (M b))))
    (θ : (y z : B) → Θ y z) : (y z : B) → Θ y z :=
  fun y z => if adj z y then Φ y z (θ y z) (depositData adj (readOp op c θ) x₀ S R rd z y)
    else θ y z

omit [Fintype B] in
theorem windowTicks_eq_nil {S R : Set B} {eLast t : ℕ} (ht : t ≤ eLast) {z y : B}
    (hout : ¬ InDiamond adj S R eLast z y) : windowTicks adj S R t z y = [] := by
  classical
  rw [windowTicks, List.filter_eq_nil_iff]
  intro k hk hpred
  simp only [decide_eq_true_eq] at hpred
  have hk' := List.mem_range.mp hk
  exact hout ⟨k, t - 1 - k, hpred.1, hpred.2, by omega⟩

theorem depositData_eq_nil (T : BlockOp K M) (x₀ : (b : B) → M b) {S R : Set B} {eLast : ℕ}
    {rd : List (ℕ × ((b : B) → Module.Dual K (M b)))} (hrd : Admitted R eLast rd) {z y : B}
    (hout : ¬ InDiamond adj S R eLast z y) : depositData adj T x₀ S R rd z y = [] := by
  rw [depositData, List.flatMap_eq_nil_iff]
  intro r hr
  rw [windowTicks_eq_nil (hrd r hr).1 hout, List.map_nil]

/-- [proved-derived; formal-checked] **A deposit gives the same result with or without the
collapse** (`deposit_descends`, R3 R3). On a retained edge the window's features and covectors are
the same under both constitutions (`trajectory_agrees_where_observed`,
`sweep_agrees_where_reached`); a released edge has an empty window, so the collapsed locus stays
released. Hence `collapse ∘ deposit = deposit ∘ collapse` on the admitted family. -/
theorem deposit_descends [DecidableEq B] (hrel : ∀ c y z, op c y z (rel y z) = 0)
    (Φ : (y z : B) → Θ y z → List (M z × Module.Dual K (M y)) → Θ y z)
    (hΦ : ∀ y z θ, Φ y z θ [] = θ) {θ : (y z : B) → Θ y z} (hθ : LociSparse adj op θ)
    {S R : Set B} {eLast : ℕ} (c : Cls) {x₀ : (b : B) → M b} (hx : SupportedIn x₀ S)
    {rd : List (ℕ × ((b : B) → Module.Dual K (M b)))} (hrd : Admitted R eLast rd) :
    collapse adj rel S R eLast (deposit adj op Φ S R c x₀ rd θ) =
      deposit adj op Φ S R c x₀ rd (collapse adj rel S R eLast θ) := by
  classical
  funext y z
  have hagree : ∀ y z, InDiamond adj S R eLast z y →
      readOp op c (collapse adj rel S R eLast θ) y z = readOp op c θ y z :=
    fun y z hd => by simp only [readOp, collapse_of_mem hd]
  have hT := sparse_readOp hθ c
  have hT' := sparse_readOp (lociSparse_collapse hrel hθ S R eLast) c
  by_cases hd : InDiamond adj S R eLast z y
  · rw [collapse_of_mem hd]
    simp only [deposit]
    split_ifs with hadj
    · rw [collapse_of_mem hd]
      congr 1
      rw [depositData, depositData]
      refine List.flatMap_congr fun r hr => List.map_congr_left fun k hk => ?_
      have hk' : k ∈ windowTicks adj S R r.1 z y := hk
      simp only [windowTicks, List.mem_filter, List.mem_range, decide_eq_true_eq] at hk'
      obtain ⟨hkt, hz, hy⟩ := hk'
      have htr := (hrd r hr).1
      refine Prod.ext ?_ ?_
      · refine (trajectory_agrees_where_observed hT hT' hx hagree (by omega) ?_).symm
        exact observes_mono (by omega) (observes_step hadj hy)
      · refine (sweep_agrees_where_reached hT hT' (hrd r hr).2 hagree (by omega) ?_).symm
        exact reachWithin_mono (by omega) (reachWithin_step hz hadj)
    · rw [collapse_of_mem hd]
  · rw [collapse_of_not_mem hd]
    simp only [deposit]
    split_ifs with hadj
    · rw [collapse_of_not_mem hd, depositData_eq_nil _ _ hrd hd, hΦ]
    · rw [collapse_of_not_mem hd]

/-- [proved-derived; formal-checked] **The release is structural** (`release_structural`). The
released loci are read from the declared graph, the sources, the admitted receivers and `e_last`
alone; every admitted deposit keeps a released locus released, so no sequence of later deposits
resurrects it, whatever the constitution's values. -/
theorem release_structural (Φ : (y z : B) → Θ y z → List (M z × Module.Dual K (M y)) → Θ y z)
    (hΦ : ∀ y z θ, Φ y z θ [] = θ) {S R : Set B} {eLast : ℕ}
    (steps : List (Cls × ((b : B) → M b) × List (ℕ × ((b : B) → Module.Dual K (M b)))))
    (hsteps : ∀ st ∈ steps, Admitted R eLast st.2.2) {θ : (y z : B) → Θ y z}
    (hθ : ∀ y z, ¬ InDiamond adj S R eLast z y → θ y z = rel y z) :
    ∀ y z, ¬ InDiamond adj S R eLast z y →
      steps.foldr (fun st θ' => deposit adj op Φ S R st.1 st.2.1 st.2.2 θ') θ y z = rel y z := by
  induction steps with
  | nil => exact hθ
  | cons st steps ih =>
    intro y z hout
    have ih' := ih (fun st h => hsteps st (List.mem_cons_of_mem _ h))
    simp only [List.foldr_cons, deposit]
    split_ifs with hadj
    · rw [depositData_eq_nil _ _ (hsteps st List.mem_cons_self) hout, hΦ, ih' y z hout]
    · exact ih' y z hout

/-- [proved-derived; formal-checked] **An admitted family may only shrink.** The collapse at one
boundary is sufficient for every later family contained in it (receivers `R′ ⊆ R`, last epoch
`e_last′ ≤ e_last`): a later reading never sees a locus this boundary released. -/
theorem admitted_nonincreasing (hrel : ∀ c y z, op c y z (rel y z) = 0)
    {θ : (y z : B) → Θ y z} (hθ : LociSparse adj op θ) {S R R' : Set B} {eLast eLast' t : ℕ}
    (hR : R' ⊆ R) (hlast : eLast' ≤ eLast) (ht : t ≤ eLast') (c : Cls) {x₀ : (b : B) → M b}
    (hx : SupportedIn x₀ S) {g : (b : B) → Module.Dual K (M b)} (hg : SupportedIn g R') :
    pair g (trajectory (readOp op c (collapse adj rel S R eLast θ)) x₀ t) =
      pair g (trajectory (readOp op c θ) x₀ t) := by
  refine release_past_diamond (sparse_readOp hθ c)
    (sparse_readOp (lociSparse_collapse hrel hθ S R eLast) c) hx hg ht ?_
  rintro y z ⟨j, m, hz, ⟨ρ, hρ, n, hn, hr⟩, hjm⟩
  simp only [readOp]
  rw [collapse_of_mem ⟨j, m, hz, ⟨ρ, hR hρ, n, hn, hr⟩, by omega⟩]

omit [Fintype B] in
/-- [proved-derived; formal-checked] **The collapse is a local 0/1 projection that keeps the
contact graph** (`local_retention_blocks`, R2 M3, M4): each locus is kept or released on its own,
the collapse is idempotent, and it keeps the loci inside the declared graph; a locus it keeps with a
nonzero operator is a declared edge of the diamond. -/
theorem local_retention_blocks (hrel : ∀ c y z, op c y z (rel y z) = 0)
    {θ : (y z : B) → Θ y z} (hθ : LociSparse adj op θ) (S R : Set B) (eLast : ℕ) :
    collapse adj rel S R eLast (collapse adj rel S R eLast θ) = collapse adj rel S R eLast θ ∧
      (∀ y z, collapse adj rel S R eLast θ y z = θ y z ∨
        collapse adj rel S R eLast θ y z = rel y z) ∧
      LociSparse adj op (collapse adj rel S R eLast θ) ∧
      ∀ c y z, op c y z (collapse adj rel S R eLast θ y z) ≠ 0 →
        adj z y ∧ InDiamond adj S R eLast z y := by
  refine ⟨?_, fun y z => ?_, lociSparse_collapse hrel hθ S R eLast, fun c y z hne => ?_⟩
  · funext y z
    by_cases hd : InDiamond adj S R eLast z y
    · rw [collapse_of_mem hd, collapse_of_mem hd]
    · rw [collapse_of_not_mem hd, collapse_of_not_mem hd]
  · by_cases hd : InDiamond adj S R eLast z y
    · exact Or.inl (collapse_of_mem hd)
    · exact Or.inr (collapse_of_not_mem hd)
  · by_cases hd : InDiamond adj S R eLast z y
    · refine ⟨?_, hd⟩
      by_contra hadj
      exact hne (lociSparse_collapse hrel hθ S R eLast c y z hadj)
    · rw [collapse_of_not_mem hd, hrel] at hne
      exact absurd rfl hne

/-- [proved-derived; formal-checked] **The constitution descends** (`constitution_descends`):
every retained locus keeps its value (so its law and its exact values), every released locus takes
the declared release, and every admitted receiver factors through the collapse at every class
configuration. -/
theorem constitution_descends (hrel : ∀ c y z, op c y z (rel y z) = 0)
    {θ : (y z : B) → Θ y z} (hθ : LociSparse adj op θ) (S R : Set B) (eLast : ℕ) :
    (∀ y z, InDiamond adj S R eLast z y → collapse adj rel S R eLast θ y z = θ y z) ∧
      (∀ y z, ¬ InDiamond adj S R eLast z y → collapse adj rel S R eLast θ y z = rel y z) ∧
      ∀ (c : Cls) (t : ℕ), t ≤ eLast → ∀ x₀ : (b : B) → M b, SupportedIn x₀ S →
        ∀ g : (b : B) → Module.Dual K (M b), SupportedIn g R →
          pair g (trajectory (readOp op c (collapse adj rel S R eLast θ)) x₀ t) =
            pair g (trajectory (readOp op c θ) x₀ t) :=
  ⟨fun _ _ hd => collapse_of_mem hd, fun _ _ hd => collapse_of_not_mem hd,
    fun c _ ht _ hx _ hg => release_indistinguishable hrel hθ ht c hx hg⟩

end Collapse

/-! ## 4. A later family that adds a receiver can read a released locus -/

section GrowthWitness

/-- [definition] The witness graph: the path `0 → 1 → 2` of three blocks. -/
def pathAdj (z y : Fin 3) : Prop := (z = 0 ∧ y = 1) ∨ (z = 1 ∧ y = 2)

instance : DecidableRel pathAdj := fun z y => by unfold pathAdj; infer_instance

/-- [definition] The witness constitution: the identity on each path edge. -/
def pathOp (y z : Fin 3) : ℚ →ₗ[ℚ] ℚ := if pathAdj z y then LinearMap.id else 0

theorem pathAdj_from_two {y : Fin 3} : ¬ pathAdj 2 y := by
  unfold pathAdj; omega

theorem reachIn_from_two {ρ : Fin 3} {n : ℕ} (h : ReachIn pathAdj 2 ρ n) : ρ = 2 := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => subst ih; exact absurd hstep pathAdj_from_two

theorem path_edge_released :
    ¬ InDiamond pathAdj ({0} : Set (Fin 3)) {1} 1 1 2 := by
  rintro ⟨j, m, -, ⟨ρ, hρ, n, -, hr⟩, -⟩
  rw [reachIn_from_two hr] at hρ
  exact absurd hρ (by decide)

theorem path_edge_retained : InDiamond pathAdj ({0} : Set (Fin 3)) {1} 1 0 1 :=
  ⟨0, 0, ⟨0, rfl, 0, le_rfl, ReachIn.refl 0⟩, ⟨1, rfl, 0, le_rfl, ReachIn.refl 1⟩, le_rfl⟩

theorem path_collapse (y z : Fin 3) :
    collapse pathAdj (fun _ _ => (0 : ℚ →ₗ[ℚ] ℚ)) {0} {1} 1 pathOp y z =
      if z = 0 ∧ y = 1 then LinearMap.id else 0 := by
  by_cases hd : InDiamond pathAdj ({0} : Set (Fin 3)) {1} 1 z y
  · rw [collapse_of_mem hd, pathOp]
    by_cases h01 : z = 0 ∧ y = 1
    · rw [if_pos (show pathAdj z y from Or.inl h01), if_pos h01]
    · rw [if_neg h01]
      split_ifs with hadj
      · rcases hadj with h | ⟨rfl, rfl⟩
        · exact absurd h h01
        · exact absurd hd path_edge_released
      · rfl
  · rw [collapse_of_not_mem hd]
    split_ifs with h01
    · obtain ⟨rfl, rfl⟩ := h01; exact absurd path_edge_retained hd
    · rfl

/-- [counterexample; formal-checked] **A later family that adds a receiver reads a released
locus** (the converse of `admitted_nonincreasing`). On the path `0 → 1 → 2` with source `0`,
receiver `1` and `e_last = 1`, the edge `1 → 2` is released; a later family adding receiver `2` at
epoch `2` reads `1` through the constitution and `0` through the collapse. -/
theorem admitted_growth_reads_released :
    pair (Pi.single 2 LinearMap.id : (b : Fin 3) → Module.Dual ℚ ((fun _ => ℚ) b))
        (trajectory (readOp (fun (_ : Unit) _ _ (θ : ℚ →ₗ[ℚ] ℚ) => θ) ()
          (collapse pathAdj (fun _ _ => (0 : ℚ →ₗ[ℚ] ℚ)) {0} {1} 1 pathOp))
          (Pi.single 0 1) 2) = 0 ∧
      pair (Pi.single 2 LinearMap.id : (b : Fin 3) → Module.Dual ℚ ((fun _ => ℚ) b))
        (trajectory (readOp (fun (_ : Unit) _ _ (θ : ℚ →ₗ[ℚ] ℚ) => θ) () pathOp)
          (Pi.single 0 1) 2) = 1 := by
  constructor
  · simp only [pair_single, trajectory, tick, readOp, path_collapse, Fin.sum_univ_three]
    simp
  · simp only [pair_single, trajectory, tick, readOp, pathOp, pathAdj, Fin.sum_univ_three]
    simp

/-- [counterexample; formal-checked] **The diamond rule is tight on the path.** The edge `0 → 1`
lies in the diamond of source `0`, receiver `1` and `e_last = 1`, and releasing it changes the
admitted reading at epoch `1` from `1` to `0`: a retained locus cannot be released. -/
theorem retained_edge_is_read :
    pair (Pi.single 1 LinearMap.id : (b : Fin 3) → Module.Dual ℚ ((fun _ => ℚ) b))
        (trajectory (readOp (fun (_ : Unit) _ _ (θ : ℚ →ₗ[ℚ] ℚ) => θ) () pathOp)
          (Pi.single 0 1) 1) = 1 ∧
      pair (Pi.single 1 LinearMap.id : (b : Fin 3) → Module.Dual ℚ ((fun _ => ℚ) b))
        (trajectory (readOp (fun (_ : Unit) _ _ (θ : ℚ →ₗ[ℚ] ℚ) => θ) ()
          (fun y z => if z = 0 ∧ y = 1 then 0 else pathOp y z)) (Pi.single 0 1) 1) = 0 := by
  constructor
  · simp only [pair_single, trajectory, tick, readOp, pathOp, pathAdj, Fin.sum_univ_three]
    simp
  · simp only [pair_single, trajectory, tick, readOp, pathOp, pathAdj, Fin.sum_univ_three]
    simp

/-- [counterexample; formal-checked] **`deposit_descends` needs a deposit law that an empty window
leaves unchanged.** The law `Φ(θ, data) = θ + I` moves a locus even with no data; on the released
edge `1 → 2` of the path, collapsing after the deposit gives `0` and depositing after the collapse
gives `I`. -/
theorem deposit_descends_needs_empty_window_law :
    collapse pathAdj (fun _ _ => (0 : ℚ →ₗ[ℚ] ℚ)) {0} {1} 1
        (deposit pathAdj (fun (_ : Unit) _ _ (θ : ℚ →ₗ[ℚ] ℚ) => θ)
          (fun _ _ θ (_ : List (ℚ × Module.Dual ℚ ℚ)) => θ + LinearMap.id) {0} {1} ()
          (Pi.single 0 1) [] pathOp) 2 1 = 0 ∧
      deposit pathAdj (fun (_ : Unit) _ _ (θ : ℚ →ₗ[ℚ] ℚ) => θ)
          (fun _ _ θ (_ : List (ℚ × Module.Dual ℚ ℚ)) => θ + LinearMap.id) {0} {1} ()
          (Pi.single 0 1) []
          (collapse pathAdj (fun _ _ => (0 : ℚ →ₗ[ℚ] ℚ)) {0} {1} 1 pathOp) 2 1 = LinearMap.id := by
  constructor
  · exact collapse_of_not_mem path_edge_released
  · have hadj : pathAdj 1 2 := Or.inr ⟨rfl, rfl⟩
    simp only [deposit, if_pos hadj, path_collapse]
    simp

end GrowthWitness

/-! ## 5. The word opens at zero change; the field's standing; the contemporary read -/

section Standing

variable {B : Type*} [Fintype B] [DecidableEq B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]

omit [DecidableEq B] in
/-- [proved-derived; formal-checked] **The word opens at zero change and is linear in its open
state** (R2 C2c, C3), on the abstract word: from the zero open state every tick of a `BlockOp` is
zero, and at fixed operands (one class configuration) the trajectory is linear in the open state,
so its readings are linear in the moment. This is the linearity of any linear trajectory; it says
nothing about what a word may carry in. That guarantee is structural in the Rust: `Current` has no
wave or contact-state field, and `Word::open` builds every wave at zero (guard 16). On the concrete
tick `fieldTick μ 0 = 0` follows once the bridge owed in #62 lands. -/
theorem word_opens_at_zero (T : BlockOp K M) :
    (∀ t, trajectory T 0 t = 0) ∧
      ∀ (a : K) (x x' : (b : B) → M b) (t : ℕ),
        trajectory T (a • x + x') t = a • trajectory T x t + trajectory T x' t := by
  constructor
  · intro t
    induction t with
    | zero => rfl
    | succ t ih => funext y; simp [trajectory, tick, ih]
  · intro a x x' t
    induction t with
    | zero => rfl
    | succ t ih =>
      funext y
      simp only [trajectory, tick, ih, Pi.add_apply, Pi.smul_apply, map_add, map_smul,
        Finset.sum_add_distrib, Finset.smul_sum]

variable {Cls Λ Mo Cell Crib : Type*} {Θ : B → B → Type*}

/-- [definition] **The resident field between words**: the constitution's loci, the lift point,
the open moment and the pending ratios (each its producing anchor and its copy of the moment).
There is no wave field: the change lives only inside a word. -/
structure Resident (Θ : B → B → Type*) (Λ Mo : Type*) where
  loci : (y z : B) → Θ y z
  lift : Λ
  moment : Mo
  pending : List (Λ × Mo)

/-- [definition] The admitted readings of one boundary: epoch at most `e_last`, covector supported
on the admitted receivers. -/
def AdmittedReading (K : Type*) [Field K] (M : B → Type*) [∀ b, AddCommGroup (M b)]
    [∀ b, Module K (M b)] (R : Set B) (eLast : ℕ) :=
  {r : ℕ × ((b : B) → Module.Dual K (M b)) // r.1 ≤ eLast ∧ SupportedIn r.2 R}

/-- [definition] The field's generators: ingest a source cell, locate keys from a crib
(re-keying), refine (a pending ratio at the current anchor), and deposit an admitted family. -/
inductive FieldGen (Cell Crib RD : Type*)
  | ingest (x : Cell)
  | locateKeys (crib : Crib)
  | refine
  | deposit (rd : RD)

/-- [definition] The field's sources: resident fields whose loci respect the declared graph. -/
def SparseResident (adj : B → B → Prop) (op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y))
    (Λ Mo : Type*) :=
  {res : Resident Θ Λ Mo // LociSparse adj op res.loci}

/-- [definition] The admitted families of readings, the payload of a deposit. -/
abbrev AdmittedFamily (K : Type*) [Field K] (M : B → Type*) [∀ b, AddCommGroup (M b)]
    [∀ b, Module K (M b)] (R : Set B) (eLast : ℕ) :=
  {rd : List (ℕ × ((b : B) → Module.Dual K (M b))) // Admitted R eLast rd}

/-- [definition] The generators acting on the resident field. -/
def fieldTransport (adj : B → B → Prop) (op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y))
    (cls : Λ → Cls) (openState : Λ → Mo → (b : B) → M b)
    (ingestStep : Cell → Λ × Mo → Λ × Mo) (rekey : Crib → Λ → Λ)
    (Φ : (y z : B) → Θ y z → List (M z × Module.Dual K (M y)) → Θ y z) (S R : Set B)
    (eLast : ℕ) :
    FieldGen Cell Crib (AdmittedFamily K M R eLast) →
      SparseResident adj op Λ Mo → SparseResident adj op Λ Mo
  | .ingest x, res =>
    ⟨⟨res.1.loci, (ingestStep x (res.1.lift, res.1.moment)).1,
      (ingestStep x (res.1.lift, res.1.moment)).2, res.1.pending⟩, res.2⟩
  | .locateKeys crib, res => ⟨⟨res.1.loci, rekey crib res.1.lift, res.1.moment, res.1.pending⟩, res.2⟩
  | .refine, res =>
    ⟨⟨res.1.loci, res.1.lift, res.1.moment, res.1.pending ++ [(res.1.lift, res.1.moment)]⟩, res.2⟩
  | .deposit rd, res =>
    ⟨⟨deposit adj op Φ S R (cls res.1.lift) (openState res.1.lift res.1.moment) rd.1 res.1.loci,
        res.1.lift, res.1.moment, res.1.pending⟩,
      fun c y z h => by
        simp only [deposit, if_neg h]
        exact res.2 c y z h⟩

/-- [definition] A word's admitted reading at an anchor `(λ, M)` and the current loci. -/
def wordReading (op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y)) (cls : Λ → Cls)
    (openState : Λ → Mo → (b : B) → M b) (R : Set B) (eLast : ℕ) (θ : (y z : B) → Θ y z)
    (anchor : Λ × Mo) (r : AdmittedReading K M R eLast) : K :=
  pair r.1.2 (trajectory (readOp op (cls anchor.1) θ) (openState anchor.1 anchor.2) r.1.1)

/-- [definition] The field's observations: the admitted faces of the current word
(`none`) and of each pending ratio (`some i`), read at the contemporary constitution. -/
def fieldObserve (adj : B → B → Prop) (op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y))
    (cls : Λ → Cls) (openState : Λ → Mo → (b : B) → M b) (R : Set B) (eLast : ℕ)
    (q : Option ℕ × AdmittedReading K M R eLast) (res : SparseResident adj op Λ Mo) : K :=
  match q.1 with
  | none => wordReading op cls openState R eLast res.1.loci (res.1.lift, res.1.moment) q.2
  | some i => match res.1.pending[i]? with
    | none => 0
    | some anchor => wordReading op cls openState R eLast res.1.loci anchor q.2

/-- [definition] The field's retention: the collapse of the constitution; lift point, moment and
pending ratios are kept. -/
def fieldRetain (adj : B → B → Prop) (op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y))
    (rel : (y z : B) → Θ y z) (S R : Set B) (eLast : ℕ)
    (hrel : ∀ c y z, op c y z (rel y z) = 0) (res : SparseResident adj op Λ Mo) :
    SparseResident adj op Λ Mo :=
  ⟨⟨collapse adj rel S R eLast res.1.loci, res.1.lift, res.1.moment, res.1.pending⟩,
    lociSparse_collapse hrel res.2 S R eLast⟩

variable {op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y)} {rel : (y z : B) → Θ y z}
  {cls : Λ → Cls} {openState : Λ → Mo → (b : B) → M b} {ingestStep : Cell → Λ × Mo → Λ × Mo}
  {rekey : Crib → Λ → Λ} {Φ : (y z : B) → Θ y z → List (M z × Module.Dual K (M y)) → Θ y z}
  {S R : Set B} {eLast : ℕ}

theorem fieldRetain_transport (hrel : ∀ c y z, op c y z (rel y z) = 0)
    (hΦ : ∀ y z θ, Φ y z θ [] = θ) (hopen : ∀ l m, SupportedIn (openState l m) S)
    (g : FieldGen Cell Crib (AdmittedFamily K M R eLast)) (res : SparseResident adj op Λ Mo) :
    fieldRetain adj op rel S R eLast hrel
        (fieldTransport adj op cls openState ingestStep rekey Φ S R eLast g res) =
      fieldTransport adj op cls openState ingestStep rekey Φ S R eLast g
        (fieldRetain adj op rel S R eLast hrel res) := by
  cases g with
  | ingest x => rfl
  | locateKeys crib => rfl
  | refine => rfl
  | deposit rd =>
    apply Subtype.ext
    simp only [fieldRetain, fieldTransport]
    congr 1
    exact deposit_descends hrel Φ hΦ res.2 _ (hopen _ _) rd.2

omit [DecidableEq B] in
theorem fieldObserve_retain (hrel : ∀ c y z, op c y z (rel y z) = 0)
    (hopen : ∀ l m, SupportedIn (openState l m) S) (q : Option ℕ × AdmittedReading K M R eLast)
    (res : SparseResident adj op Λ Mo) :
    fieldObserve adj op cls openState R eLast q (fieldRetain adj op rel S R eLast hrel res) =
      fieldObserve adj op cls openState R eLast q res := by
  obtain ⟨i, r⟩ := q
  cases i with
  | none =>
    exact release_indistinguishable hrel res.2 r.2.1 _ (hopen _ _) r.2.2
  | some i =>
    simp only [fieldObserve, fieldRetain]
    cases res.1.pending[i]? with
    | none => rfl
    | some anchor => exact release_indistinguishable hrel res.2 r.2.1 _ (hopen _ _) r.2.2

/-- [proved-derived; formal-checked] **The field's standing** (`fieldStanding`, R3 R3). The
resident `(Θ, λ, M, pending)` with the generators ingest, locate keys, refine and deposit, observed
through the admitted faces of the current word and of every pending ratio at the contemporary
constitution, is a `Foundation/Standing.StandingLaw` whose retention is the collapse: the collapse
commutes with every generator (`deposit_descends`) and every observation factors through it
(`release_indistinguishable`). -/
def fieldStanding (hrel : ∀ c y z, op c y z (rel y z) = 0) (hΦ : ∀ y z θ, Φ y z θ [] = θ)
    (hopen : ∀ l m, SupportedIn (openState l m) S) :
    Holonics.Foundation.Standing.StandingLaw (FieldGen Cell Crib (AdmittedFamily K M R eLast))
      (Option ℕ × AdmittedReading K M R eLast) (SparseResident adj op Λ Mo)
      (SparseResident adj op Λ Mo) K where
  transport := fieldTransport adj op cls openState ingestStep rekey Φ S R eLast
  observe := fieldObserve adj op cls openState R eLast
  retain := fieldRetain adj op rel S R eLast hrel
  reopen q word res := fieldObserve adj op cls openState R eLast q
    (Holonics.Foundation.Chronology.transportWord
      (fieldTransport adj op cls openState ingestStep rekey Φ S R eLast) word res)
  sufficient q word res := by
    rw [← Holonics.Foundation.Chronology.generatorEquivarianceExtendsToEveryTransportWord _ _ _
      (fieldRetain_transport hrel hΦ hopen) word res, fieldObserve_retain hrel hopen]

omit [DecidableEq B] in
/-- [proved-derived; formal-checked] **The contemporary read** (review C2, R2 C3). A pending
ratio keeps its producing anchor: every generator but a deposit (ingest, locate keys, refine)
leaves its read unchanged, so a delayed compare with no intervening deposit equals the immediate
one exactly; after a deposit the read changes by exactly the word's variation
(`Propagation.word_variation_exact`), the residual against the emitted face. -/
theorem contemporary_read (res : SparseResident adj op Λ Mo) (i : ℕ)
    (hi : i < res.1.pending.length) (r : AdmittedReading K M R eLast) :
    (∀ g : FieldGen Cell Crib (AdmittedFamily K M R eLast), (∀ rd, g ≠ .deposit rd) →
      fieldObserve adj op cls openState R eLast (some i, r)
          (fieldTransport adj op cls openState ingestStep rekey Φ S R eLast g res) =
        fieldObserve adj op cls openState R eLast (some i, r) res) ∧
      ∀ rd : AdmittedFamily K M R eLast,
        fieldObserve adj op cls openState R eLast (some i, r)
            (fieldTransport adj op cls openState ingestStep rekey Φ S R eLast (.deposit rd) res) -
          fieldObserve adj op cls openState R eLast (some i, r) res =
        ∑ k ∈ Finset.range r.1.1,
          pair (sweep (readOp op (cls (res.1.pending[i]).1)
              (deposit adj op Φ S R (cls res.1.lift) (openState res.1.lift res.1.moment) rd.1
                res.1.loci)) r.1.2 (r.1.1 - 1 - k))
            (tick (opSub (readOp op (cls (res.1.pending[i]).1)
                (deposit adj op Φ S R (cls res.1.lift) (openState res.1.lift res.1.moment) rd.1
                  res.1.loci))
              (readOp op (cls (res.1.pending[i]).1) res.1.loci))
              (trajectory (readOp op (cls (res.1.pending[i]).1) res.1.loci)
                (openState (res.1.pending[i]).1 (res.1.pending[i]).2) k)) := by
  have hget : res.1.pending[i]? = some (res.1.pending[i]) := List.getElem?_eq_getElem hi
  refine ⟨fun g hg => ?_, fun rd => ?_⟩
  · cases g with
    | ingest x => rfl
    | locateKeys crib => rfl
    | refine =>
      simp only [fieldObserve, fieldTransport]
      rw [List.getElem?_append_left hi]
    | deposit rd => exact absurd rfl (hg rd)
  · simp only [fieldObserve, fieldTransport, hget, wordReading]
    exact word_variation_exact _ _ _ _ _

end Standing

/-! ## 6. The lift point and its readings -/

section Lift

open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Reading Holonics.Aeon.Clock.Winding

/-- [proved-derived; formal-checked] **Each ring reads its own clock** (per-ring receipts in their
own clocks). Along any aeon of the lift of the rings' joint clock torus, ring `i`'s micro-step
clock reads its lift displacement (`Winding.reading_navigatorClock`), and the aeon returns to one
point of the clock torus exactly when every ring reads a whole number of its periods
(`Winding.torus_closes_iff`): the joint carry-out that bounds an aeon. -/
theorem lift_reading {ι : Type*} [DecidableEq ι] (d : ι → ℕ) {x y : ι → ℤ}
    (γ : Holonics.Aeon.Clock.Groupoid.Aeon (clockLift ι) x y) :
    (∀ i, reading (navigatorClock i) γ = y i - x i) ∧
      (torusPoint d x = torusPoint d y ↔ ∀ i, (d i : ℤ) ∣ y i - x i) := by
  refine ⟨fun i => reading_navigatorClock i γ, ?_⟩
  rw [torus_closes_iff d γ]
  simp only [reading_navigatorClock]

end Lift

section Audit

#print axioms reachRound_le_iff
#print axioms diamond_recursion
#print axioms blind_outside_observe
#print axioms release_indistinguishable
#print axioms deposit_descends
#print axioms release_structural
#print axioms admitted_nonincreasing
#print axioms admitted_growth_reads_released
#print axioms retained_edge_is_read
#print axioms deposit_descends_needs_empty_window_law
#print axioms local_retention_blocks
#print axioms constitution_descends
#print axioms word_opens_at_zero
#print axioms fieldStanding
#print axioms contemporary_read
#print axioms lift_reading

end Audit

end Holonics.HNN.Retention
