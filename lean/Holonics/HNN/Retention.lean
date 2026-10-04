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
`blind_outside_observe`, `fieldStanding`, `contemporary_read`, `word_opens_at_zero` and the
diamond under the carry (§4a–4b).
`diamond_recursion`, `continuing_recursion` and `reachWithin_card` are statements about the
recursions on any finite graph `adj`, so they apply to the concrete ring/contact graph `HNN/Word.blockAdj` as it stands; `lift_reading` reads integer
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
   features and covectors that reach it inside its causal diamond; with or without the collapse
   these agree on retained loci (`Propagation.trajectory_agrees_where_observed`,
   `sweep_agrees_where_reached`), and nothing reaches a released locus, so
   `collapse ∘ deposit = deposit ∘ collapse`. The release is structural: no sequence of deposits
   resurrects a released locus (`release_structural`). A deposit law that moves a locus nothing
   reaches breaks the descent (`deposit_descends_needs_empty_window_law`), and the diamond rule
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
7. **The reception cut composes on the cumulative clock** (§5a; #62, owed by the reception
   carry's clock, item 1; record B §2.4). On the word stepped tick by tick, the junction at crossing
   `t` and then the hop at the pump's phases `phase_at(t − 1)`, `phase_at(t)` (`pumpedStep`,
   `clockedRun`), a word run to its last crossing `T` and continued from the change arriving there
   at tick `T` is the uninterrupted word from `T` on: its states, the hop it runs at every later
   tick with its phases, and every per-hop balance (`reception_cut_composes`, from
   `clockedRun_add`). The rest word is the case `T = 0`: the unpumped word is the constant step's
   run (`rest_word_is_cut_at_zero`), and the pumped word opens at zero and is linear in its open
   state (`pumped_word_opens_at_zero`). The cut after the last junction does not compose: the
   junction is an involution (`Propagation.junctionScattering_involutive`), so the next word's first
   junction undoes it and the hop at `T` runs on the unscattered change, one hop reflected
   (`cut_after_junction_reflects`, `junction_cut_reflects`, `cut_after_junction_differs`).
8. **The diamond under the carry** (§4a–4b; #62, owed by the carry as the production default,
   record B §8). A word opened on the source moment plus a carried change supported on `S′` reads,
   and deposits, the same through the collapse seeded at `𝒮 ∪ S′`
   (`opened_release_indistinguishable`, `opened_deposit_descends`), with its windows read from the
   recursions seeded there (`windowTicks_recursion`); the rest diamond seeded at `𝒮` is not enough,
   since its collapse changes the opened word's reading on every edge it drops
   (`rest_diamond_drops_opened`). Over a chain of words each opened on the last one's end plus a
   source moment (`chainEnd`, the carry at `A = 0`), releasing every edge no walk from a source to
   a receiver passes changes no admitted reading of any later word at any epoch
   (`continuing_release_indistinguishable`), and releasing any edge such a walk passes changes one
   (`continuing_walk_edge_is_read`): a carried change stays on the blocks reached from the sources
   and agrees wherever a receiver is observed (`chain_agrees_on_walk`), and at the 0/1
   constitution no cancellation hides a released walk edge (`walk_edge_is_read`). The walk diamond
   is the diamond at `e_last = 2|B|` (`inDiamond_continuing_iff`), decided by the recursions in
   `|B|` rounds (`continuing_recursion`, `reachWithin_card`), which is `Diamond::continuing`'s
   `|rings|` rounds and `2|rings|`; where every block is reached from a source and observes a
   receiver, the continuing collapse releases nothing (`continuing_collapse_connected`).

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
/-- [definition] **The ticks inside the causal diamond** of the edge `z → y` for a reading at epoch
`t`: the ticks `k < t` at which the edge's input can be nonzero (`r_z ≤ k`) and its output can still
be read (`o_y ≤ t − 1 − k`). -/
def windowTicks (S R : Set B) (t : ℕ) (z y : B) : List ℕ :=
  (List.range t).filter fun k => z ∈ reachWithin adj S k ∧ Observes adj R y (t - 1 - k)

variable (adj) in
/-- [definition] **The data a deposit reads on the edge `z → y`**: for every admitted reading and
every tick inside its causal diamond, the feature `x_k(z)` of the word's own trajectory and the
covector `λ(y)` swept back to tick `k + 1`. -/
def depositData (T : BlockOp K M) (x₀ : (b : B) → M b) (S R : Set B)
    (rd : List (ℕ × ((b : B) → Module.Dual K (M b)))) (z y : B) :
    List (M z × Module.Dual K (M y)) :=
  rd.flatMap fun r => (windowTicks adj S R r.1 z y).map fun k =>
    (trajectory T x₀ k z, sweep T r.2 (r.1 - 1 - k) y)

variable (adj op) in
open Classical in
/-- [definition] **The deposit**: on each declared edge the locus law `Φ` reads its own state and
the data that reached it inside its causal diamond; nothing else changes. -/
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
collapse** (`deposit_descends`, R3 R3). On a retained edge the features and covectors that reach
it are the same under both constitutions (`trajectory_agrees_where_observed`,
`sweep_agrees_where_reached`); nothing reaches a released edge, so the collapsed locus stays
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

/-- [counterexample; formal-checked] **`deposit_descends` needs a deposit law that leaves a
locus nothing reaches unchanged.** The law `Φ(θ, data) = θ + I` moves a locus even with no data; on
the released edge `1 → 2` of the path, collapsing after the deposit gives `0` and depositing after
the collapse gives `I`. -/
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

/-! ## 4a. The diamond under the carry: the opened word and the continuing chain -/

section Carry

variable {B : Type*} [Fintype B] {adj : B → B → Prop}

omit [Fintype B] in
theorem supportedIn_union {M : B → Type*} [∀ b, AddCommGroup (M b)] {x x' : (b : B) → M b}
    {S S' : Set B} (hx : SupportedIn x S) (hx' : SupportedIn x' S') :
    SupportedIn (x + x') (S ∪ S') := by
  intro b hb
  simp only [Set.mem_union, not_or] at hb
  simp [hx b hb.1, hx' b hb.2]

open Classical in
/-- [proved-derived; formal-checked] **The windows are read from the recursions.** For a reading
at epoch `t ≤ e_last`, a tick `k` lies in the window `D(z → y, t)` of the seeds `S` exactly when
`k < t`, `r_z ≤ k` and `o_y ≤ t − 1 − k` for the reach and observe recursions run `e_last` rounds.
Seeded at `𝒮 ∪ S′` this is the opened word's window (`Diamond::opened`,
`Diamond::element_window`, `Diamond::channel_window`). -/
theorem windowTicks_recursion (S R : Set B) {eLast t : ℕ} (ht : t ≤ eLast) (z y : B) (k : ℕ) :
    k ∈ windowTicks adj S R t z y ↔
      k < t ∧ reachRound adj S eLast z ≤ k ∧
        observeRound adj R eLast y ≤ ((t - 1 - k : ℕ) : ℕ∞) := by
  simp only [windowTicks, List.mem_filter, List.mem_range, decide_eq_true_eq]
  constructor
  · rintro ⟨hk, hz, hy⟩
    exact ⟨hk, (reachRound_le_iff S (by omega) z).mpr hz,
      (reachRound_le_iff (adj := flip adj) R (by omega) y).mpr
        (observes_iff_reachWithin_flip.mp hy)⟩
  · rintro ⟨hk, hz, hy⟩
    exact ⟨hk, reachRound_sound S eLast z k hz,
      observes_iff_reachWithin_flip.mpr (reachRound_sound (adj := flip adj) R eLast y _ hy)⟩

section Opened

variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
variable {Cls : Type*} {Θ : B → B → Type*}
variable {op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y)} {rel : (y z : B) → Θ y z}

/-- [proved-derived; formal-checked] **The opened word's collapse is indistinguishable**
(#62, the diamond under the carry, item 1). A word opened on the source moment `u` (supported on
the sources `𝒮`) plus a carried change `x` (supported on `S′`) reads the same through the collapse
seeded at `𝒮 ∪ S′` as through the constitution, at every class configuration, epoch `t ≤ e_last`
and receiver. -/
theorem opened_release_indistinguishable (hrel : ∀ c y z, op c y z (rel y z) = 0)
    {θ : (y z : B) → Θ y z} (hθ : LociSparse adj op θ) {S S' R : Set B} {eLast t : ℕ}
    (ht : t ≤ eLast) (c : Cls) {u x : (b : B) → M b} (hu : SupportedIn u S)
    (hx : SupportedIn x S') {g : (b : B) → Module.Dual K (M b)} (hg : SupportedIn g R) :
    pair g (trajectory (readOp op c (collapse adj rel (S ∪ S') R eLast θ)) (u + x) t) =
      pair g (trajectory (readOp op c θ) (u + x) t) :=
  release_indistinguishable hrel hθ ht c (supportedIn_union hu hx) hg

/-- [proved-derived; formal-checked] **The opened word's deposit descends** (#62, the diamond
under the carry, item 1). With the windows `D(z → y, t) = {k < t | r_z ≤ k, o_y ≤ t − 1 − k}` read
from the reach seeded at `𝒮 ∪ S′` (`windowTicks_recursion`), a deposit of the word opened on
`u + x` gives the same result with or without the collapse seeded there. -/
theorem opened_deposit_descends [DecidableEq B] (hrel : ∀ c y z, op c y z (rel y z) = 0)
    (Φ : (y z : B) → Θ y z → List (M z × Module.Dual K (M y)) → Θ y z)
    (hΦ : ∀ y z θ, Φ y z θ [] = θ) {θ : (y z : B) → Θ y z} (hθ : LociSparse adj op θ)
    {S S' R : Set B} {eLast : ℕ} (c : Cls) {u x : (b : B) → M b} (hu : SupportedIn u S)
    (hx : SupportedIn x S') {rd : List (ℕ × ((b : B) → Module.Dual K (M b)))}
    (hrd : Admitted R eLast rd) :
    collapse adj rel (S ∪ S') R eLast (deposit adj op Φ (S ∪ S') R c (u + x) rd θ) =
      deposit adj op Φ (S ∪ S') R c (u + x) rd (collapse adj rel (S ∪ S') R eLast θ) :=
  deposit_descends hrel Φ hΦ hθ c (supportedIn_union hu hx) hrd

end Opened

/-! ### The walk diamond and its recursion -/

variable (adj) in
/-- [definition] **Every block a walk from `S` reaches**, at any distance. -/
def reachAll (S : Set B) : Set B := {b | ∃ t, b ∈ reachWithin adj S t}

variable (adj) in
/-- [definition] **The block observes a receiver** at some distance. -/
def ObservesAll (R : Set B) (y : B) : Prop := ∃ m, Observes adj R y m

variable (adj) in
/-- [definition] **The edge `z → y` lies on a walk from a source to a receiver.** -/
def OnWalk (S R : Set B) (z y : B) : Prop := z ∈ reachAll adj S ∧ ObservesAll adj R y

omit [Fintype B] in
theorem reachWithin_succ (S : Set B) (t : ℕ) :
    reachWithin adj S (t + 1) = reachWithin adj S t ∪ {b | ∃ a ∈ reachWithin adj S t, adj a b} := by
  ext b
  constructor
  · rintro ⟨x, hx, n, hn, hr⟩
    rcases Nat.lt_or_ge n (t + 1) with h | h
    · exact Or.inl ⟨x, hx, n, by omega, hr⟩
    · obtain rfl : n = t + 1 := by omega
      cases hr with
      | tail hr' hstep => exact Or.inr ⟨_, ⟨x, hx, t, le_rfl, hr'⟩, hstep⟩
  · rintro (h | ⟨a, ha, hab⟩)
    · exact reachWithin_mono (by omega) h
    · exact reachWithin_step ha hab

omit [Fintype B] in
theorem reachWithin_stable {S : Set B} {t : ℕ}
    (h : reachWithin adj S (t + 1) = reachWithin adj S t) (k : ℕ) :
    reachWithin adj S (t + k) = reachWithin adj S t := by
  induction k with
  | zero => rfl
  | succ k ih => rw [← add_assoc, reachWithin_succ, ih, ← reachWithin_succ, h]

/-- [proved-derived; formal-checked] **A walk is never needed longer than `|B| − 1` hops.** The
reach sets grow until one round adds nothing and are constant from then on; each growing round adds
a block, so they stop growing by round `|B| − 1`. -/
theorem reachWithin_card (S : Set B) (t : ℕ) :
    reachWithin adj S t ⊆ reachWithin adj S (Fintype.card B - 1) := by
  intro b hb
  rcases le_or_gt t (Fintype.card B - 1) with ht | ht
  · exact reachWithin_mono ht hb
  have hS : (reachWithin adj S 0).Nonempty := by
    obtain ⟨x, hx, -⟩ := hb
    exact ⟨x, x, hx, 0, le_rfl, ReachIn.refl x⟩
  have hcount : ∀ k, (∀ i < k, reachWithin adj S (i + 1) ≠ reachWithin adj S i) →
      (reachWithin adj S 0).ncard + k ≤ (reachWithin adj S k).ncard := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hne
      have h1 := ih fun i hi => hne i (by omega)
      have hsub : reachWithin adj S k ⊂ reachWithin adj S (k + 1) :=
        Set.ssubset_iff_subset_ne.mpr ⟨reachWithin_mono (by omega), (hne k (by omega)).symm⟩
      have h2 := Set.ncard_lt_ncard hsub (Set.toFinite _)
      omega
  obtain ⟨i, hi, heq⟩ :
      ∃ i < Fintype.card B, reachWithin adj S (i + 1) = reachWithin adj S i := by
    by_contra hno
    push Not at hno
    have h := hcount (Fintype.card B) hno
    have hle : (reachWithin adj S (Fintype.card B)).ncard ≤ Fintype.card B := by
      calc (reachWithin adj S (Fintype.card B)).ncard ≤ (Set.univ : Set B).ncard :=
            Set.ncard_le_ncard (Set.subset_univ _)
        _ = Fintype.card B := by rw [Set.ncard_univ, Nat.card_eq_fintype_card]
    have hpos := (Set.ncard_pos (Set.toFinite _)).mpr hS
    omega
  have hti : t = i + (t - i) := by omega
  rw [hti, reachWithin_stable heq] at hb
  exact reachWithin_mono (by omega) hb

theorem observes_card {R : Set B} {y : B} {m : ℕ} (h : Observes adj R y m) :
    Observes adj R y (Fintype.card B - 1) :=
  observes_iff_reachWithin_flip.mpr
    (reachWithin_card (adj := flip adj) R m (observes_iff_reachWithin_flip.mp h))

/-- [proved-derived; formal-checked] **The continuing diamond is the walk diamond**
(`Diamond::continuing`). At `e_last = 2 |B|` an edge lies in the causal diamond exactly when a walk
from a source passes through it to a receiver. -/
theorem inDiamond_continuing_iff (S R : Set B) (z y : B) :
    InDiamond adj S R (2 * Fintype.card B) z y ↔ OnWalk adj S R z y := by
  have hpos : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨z⟩
  constructor
  · rintro ⟨j, m, hz, hy, -⟩
    exact ⟨⟨j, hz⟩, ⟨m, hy⟩⟩
  · rintro ⟨⟨j, hz⟩, ⟨m, hy⟩⟩
    exact ⟨_, _, reachWithin_card S j hz, observes_card hy, by omega⟩

/-- [proved-derived; formal-checked] **The recursions decide the walk diamond in `|B|` rounds**
(`Diamond::continuing`: both recursions run `|rings|` rounds, `e_last = 2 |rings|`). An edge
`z → y` lies on a walk from a source to a receiver exactly when
`r_z + 1 + o_y ≤ 2 |B|` for the reach and observe recursions run `|B|` rounds. -/
theorem continuing_recursion (S R : Set B) (z y : B) :
    OnWalk adj S R z y ↔
      reachRound adj S (Fintype.card B) z + 1 + observeRound adj R (Fintype.card B) y ≤
        ((2 * Fintype.card B : ℕ) : ℕ∞) := by
  have hpos : 0 < Fintype.card B := Fintype.card_pos_iff.mpr ⟨z⟩
  constructor
  · rintro ⟨⟨j, hz⟩, ⟨m, hy⟩⟩
    obtain ⟨n, hn⟩ : ∃ n, n + 1 = Fintype.card B := ⟨Fintype.card B - 1, by omega⟩
    have hr : reachRound adj S (Fintype.card B) z ≤ n :=
      (reachRound_le_iff S (by omega) z).mpr (by
        have := reachWithin_card S j hz
        rwa [← hn, Nat.add_sub_cancel] at this)
    have ho : observeRound adj R (Fintype.card B) y ≤ n :=
      (reachRound_le_iff (adj := flip adj) R (by omega) y).mpr
        (observes_iff_reachWithin_flip.mp (by
          have := observes_card hy
          rwa [← hn, Nat.add_sub_cancel] at this))
    calc reachRound adj S (Fintype.card B) z + 1 + observeRound adj R (Fintype.card B) y
        ≤ (n : ℕ∞) + 1 + n := by gcongr
      _ = ((n + 1 + n : ℕ) : ℕ∞) := by push_cast; ring
      _ ≤ ((2 * Fintype.card B : ℕ) : ℕ∞) := by exact_mod_cast (by omega)
  · intro h
    have hr_ne : reachRound adj S (Fintype.card B) z ≠ ⊤ := by
      intro htop
      rw [htop, top_add, top_add, top_le_iff] at h
      exact ENat.natCast_ne_top _ h
    have ho_ne : observeRound adj R (Fintype.card B) y ≠ ⊤ := by
      intro htop
      rw [htop, add_top, top_le_iff] at h
      exact ENat.natCast_ne_top _ h
    obtain ⟨j, hj⟩ := ENat.ne_top_iff_exists.mp hr_ne
    obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp ho_ne
    exact ⟨⟨j, reachRound_sound S _ z j (by rw [← hj])⟩,
      ⟨m, observes_iff_reachWithin_flip.mpr
        (reachRound_sound (adj := flip adj) R _ y m (by rw [hm]; rfl))⟩⟩

/-! ### The continuing chain -/

section Chain

variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]

omit [Fintype B] in
theorem reachAll_step {S : Set B} {z y : B} (hz : z ∈ reachAll adj S) (h : adj z y) :
    y ∈ reachAll adj S := by
  obtain ⟨t, ht⟩ := hz
  exact ⟨t + 1, reachWithin_step ht h⟩

omit [Fintype B] in
theorem observesAll_step {R : Set B} {z y : B} (h : adj z y) (hy : ObservesAll adj R y) :
    ObservesAll adj R z := by
  obtain ⟨m, hm⟩ := hy
  exact ⟨m + 1, observes_step h hm⟩

omit [Fintype B] in
theorem subset_reachAll (S : Set B) : S ⊆ reachAll adj S :=
  fun b hb => ⟨0, b, hb, 0, le_rfl, ReachIn.refl b⟩

/-- [proved-derived; formal-checked] **One tick keeps the change on the reached blocks and agrees
on the observing blocks.** If two sparse ticks agree on every edge a walk from `S` to `R` passes,
and two changes are supported on the blocks reached from `S` and agree on every block that
observes `R`, the ticked changes are again so. -/
theorem tick_agrees_on_walk {T T' : BlockOp K M} (hT : Sparse adj T) (hT' : Sparse adj T')
    {S R : Set B} (hagree : ∀ y z, OnWalk adj S R z y → T y z = T' y z)
    {x x' : (b : B) → M b} (hx : SupportedIn x (reachAll adj S))
    (hx' : SupportedIn x' (reachAll adj S)) (hxx : ∀ b, ObservesAll adj R b → x b = x' b) :
    SupportedIn (tick T x) (reachAll adj S) ∧ SupportedIn (tick T' x') (reachAll adj S) ∧
      ∀ b, ObservesAll adj R b → tick T x b = tick T' x' b := by
  have hsupp : ∀ U : BlockOp K M, Sparse adj U → ∀ v : (b : B) → M b,
      SupportedIn v (reachAll adj S) → SupportedIn (tick U v) (reachAll adj S) := by
    intro U hU v hv y hy
    refine Finset.sum_eq_zero fun z _ => ?_
    by_cases h : adj z y
    · have hz : z ∉ reachAll adj S := fun hz => hy (reachAll_step hz h)
      rw [hv z hz, map_zero]
    · simp [hU y z h]
  refine ⟨hsupp T hT x hx, hsupp T' hT' x' hx', fun y hy => ?_⟩
  refine Finset.sum_congr rfl fun z _ => ?_
  by_cases h : adj z y
  · by_cases hz : z ∈ reachAll adj S
    · rw [hagree y z ⟨hz, hy⟩, hxx z (observesAll_step h hy)]
    · rw [hx z hz, hx' z hz, map_zero, map_zero]
  · simp [hT y z h, hT' y z h]

theorem trajectory_agrees_on_walk {T T' : BlockOp K M} (hT : Sparse adj T) (hT' : Sparse adj T')
    {S R : Set B} (hagree : ∀ y z, OnWalk adj S R z y → T y z = T' y z)
    {x x' : (b : B) → M b} (hx : SupportedIn x (reachAll adj S))
    (hx' : SupportedIn x' (reachAll adj S)) (hxx : ∀ b, ObservesAll adj R b → x b = x' b)
    (t : ℕ) :
    SupportedIn (trajectory T x t) (reachAll adj S) ∧
      SupportedIn (trajectory T' x' t) (reachAll adj S) ∧
      ∀ b, ObservesAll adj R b → trajectory T x t b = trajectory T' x' t b := by
  induction t with
  | zero => exact ⟨hx, hx', hxx⟩
  | succ t ih => exact tick_agrees_on_walk hT hT' hagree ih.1 ih.2.1 ih.2.2

omit [Fintype B] in
theorem pair_agrees_on_observers {R : Set B} {g : (b : B) → Module.Dual K (M b)}
    [Fintype B] (hg : SupportedIn g R) {x x' : (b : B) → M b}
    (h : ∀ b, ObservesAll adj R b → x b = x' b) : pair g x = pair g x' := by
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : b ∈ R
  · rw [h b ⟨0, b, hb, 0, le_rfl, ReachIn.refl b⟩]
  · rw [hg b hb]
    simp

variable {Cls : Type*} {Θ : B → B → Type*}

variable (op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y)) in
/-- [definition] **A chain of words under the carry at `A = 0`** (record B §8;
`Opens::OnMotion`). From the carried change `x`, each word `(c, T, u)` opens on the change the
last one reached plus its source moment `u`, and runs `T` ticks at its class configuration `c`;
`chainEnd` is the change the last word reached. The rest chain (`A = I`) is the case where every
word opens on its moment alone. -/
def chainEnd (θ : (y z : B) → Θ y z) :
    ((b : B) → M b) → List (Cls × ℕ × ((b : B) → M b)) → (b : B) → M b
  | x, [] => x
  | x, w :: ws => chainEnd θ (trajectory (readOp op w.1 θ) (x + w.2.2) w.2.1) ws

variable {op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y)} {rel : (y z : B) → Θ y z}

theorem chain_agrees_on_walk {θ θ' : (y z : B) → Θ y z} (hθ : LociSparse adj op θ)
    (hθ' : LociSparse adj op θ') {S R : Set B}
    (hagree : ∀ c y z, OnWalk adj S R z y → op c y z (θ y z) = op c y z (θ' y z))
    (ws : List (Cls × ℕ × ((b : B) → M b))) (hws : ∀ w ∈ ws, SupportedIn w.2.2 S)
    {x x' : (b : B) → M b} (hx : SupportedIn x (reachAll adj S))
    (hx' : SupportedIn x' (reachAll adj S)) (hxx : ∀ b, ObservesAll adj R b → x b = x' b) :
    SupportedIn (chainEnd op θ x ws) (reachAll adj S) ∧
      SupportedIn (chainEnd op θ' x' ws) (reachAll adj S) ∧
      ∀ b, ObservesAll adj R b → chainEnd op θ x ws b = chainEnd op θ' x' ws b := by
  induction ws generalizing x x' with
  | nil => exact ⟨hx, hx', hxx⟩
  | cons w ws ih =>
    have hu : SupportedIn w.2.2 (reachAll adj S) := fun b hb =>
      hws w List.mem_cons_self b fun hbS => hb (subset_reachAll S hbS)
    have hadd : ∀ v : (b : B) → M b, SupportedIn v (reachAll adj S) →
        SupportedIn (v + w.2.2) (reachAll adj S) := fun v hv b hb => by
      simp [hv b hb, hu b hb]
    have h := trajectory_agrees_on_walk (sparse_readOp hθ w.1) (sparse_readOp hθ' w.1)
      (fun y z hw => hagree w.1 y z hw) (hadd x hx) (hadd x' hx')
      (fun b hb => by simp [hxx b hb]) w.2.1
    exact ih (fun v hv => hws v (List.mem_cons_of_mem _ hv)) h.1 h.2.1 h.2.2

/-- [proved-derived; formal-checked] **The continuing collapse is indistinguishable over the
chain** (#62, the diamond under the carry, item 2; `Diamond::continuing`, `Opens::OnMotion`,
`collapse`). Releasing every locus no walk from a source to a receiver passes (the collapse at
`e_last = 2 |B|`, `inDiamond_continuing_iff`) changes no admitted reading of any word of any chain
of words each opened on the last one's end plus a source moment, at any epoch of that word. No
epoch bound enters: a change carried across words stays on the blocks reached from the sources, and
agrees on every block that observes a receiver (`chain_agrees_on_walk`). -/
theorem continuing_release_indistinguishable (hrel : ∀ c y z, op c y z (rel y z) = 0)
    {θ : (y z : B) → Θ y z} (hθ : LociSparse adj op θ) {S R : Set B}
    (ws : List (Cls × ℕ × ((b : B) → M b))) (hws : ∀ w ∈ ws, SupportedIn w.2.2 S) (c : Cls)
    {u : (b : B) → M b} (hu : SupportedIn u S) (t : ℕ) {g : (b : B) → Module.Dual K (M b)}
    (hg : SupportedIn g R) :
    pair g (trajectory (readOp op c (collapse adj rel S R (2 * Fintype.card B) θ))
        (chainEnd op (collapse adj rel S R (2 * Fintype.card B) θ) 0 ws + u) t) =
      pair g (trajectory (readOp op c θ) (chainEnd op θ 0 ws + u) t) := by
  have hθc := lociSparse_collapse hrel hθ S R (2 * Fintype.card B)
  have hagree : ∀ c y z, OnWalk adj S R z y →
      op c y z (collapse adj rel S R (2 * Fintype.card B) θ y z) = op c y z (θ y z) :=
    fun c y z hw => by rw [collapse_of_mem ((inDiamond_continuing_iff S R z y).mpr hw)]
  have h0 : SupportedIn (0 : (b : B) → M b) (reachAll adj S) := fun _ _ => rfl
  have hch := chain_agrees_on_walk hθc hθ hagree ws hws h0 h0 fun _ _ => rfl
  have hu' : SupportedIn u (reachAll adj S) := fun b hb => hu b fun hbS => hb (subset_reachAll S hbS)
  have hadd : ∀ v : (b : B) → M b, SupportedIn v (reachAll adj S) →
      SupportedIn (v + u) (reachAll adj S) := fun v hv b hb => by simp [hv b hb, hu' b hb]
  have h := trajectory_agrees_on_walk (sparse_readOp hθc c) (sparse_readOp hθ c)
    (fun y z hw => hagree c y z hw) (hadd _ hch.1) (hadd _ hch.2.1)
    (fun b hb => by simp [hch.2.2 b hb]) t
  exact pair_agrees_on_observers hg h.2.2

/-- [proved-derived; formal-checked] **In a field where every block is reached from a source and
observes a receiver, the continuing collapse releases nothing.** -/
theorem continuing_collapse_connected {Θ' : B → B → Type*} (rel' : (y z : B) → Θ' y z)
    {S R : Set B} (hconn : ∀ b, b ∈ reachAll adj S ∧ ObservesAll adj R b)
    (θ : (y z : B) → Θ' y z) : collapse adj rel' S R (2 * Fintype.card B) θ = θ := by
  funext y z
  exact collapse_of_mem ((inDiamond_continuing_iff S R z y).mpr ⟨(hconn z).1, (hconn y).2⟩)

end Chain

end Carry

/-! ## 4b. The diamonds under the carry are tight -/

section CarryTight

open Classical

variable {B : Type*} [Fintype B] {adj : B → B → Prop}

/-- [definition] **The 0/1 constitution keeping the edges `P`**: the identity on every kept edge
`z → y`, zero elsewhere, on one rational line per block. -/
def keepOp (P : B → B → Prop) : BlockOp ℚ (fun _ : B => ℚ) :=
  fun y z => if P z y then LinearMap.id else 0

theorem tick_keepOp (P : B → B → Prop) (x : B → ℚ) (y : B) :
    tick (keepOp P) x y = ∑ z, if P z y then x z else 0 := by
  simp only [tick, keepOp]
  refine Finset.sum_congr rfl fun z _ => ?_
  split_ifs <;> simp

theorem trajectory_keep_nonneg (P : B → B → Prop) {x : B → ℚ} (hx : 0 ≤ x) (t : ℕ) :
    0 ≤ trajectory (keepOp P) x t := by
  induction t with
  | zero => exact hx
  | succ t ih =>
    intro y
    show 0 ≤ tick (keepOp P) (trajectory (keepOp P) x t) y
    rw [tick_keepOp]
    exact Finset.sum_nonneg fun z _ => by split_ifs; exacts [ih z, le_rfl]

/-- One kept edge carries its tail's value into its head at the next tick. -/
theorem keep_step_le (P : B → B → Prop) {x : B → ℚ} (hx : 0 ≤ x) {t : ℕ} {z y : B}
    (h : P z y) : trajectory (keepOp P) x t z ≤ trajectory (keepOp P) x (t + 1) y := by
  show _ ≤ tick (keepOp P) (trajectory (keepOp P) x t) y
  rw [tick_keepOp]
  have hn := trajectory_keep_nonneg P hx t
  refine le_trans (le_of_eq (if_pos h).symm)
    (Finset.single_le_sum (f := fun w => if P w y then trajectory (keepOp P) x t w else 0)
      (fun w _ => by split_ifs; exacts [hn w, le_rfl]) (Finset.mem_univ z))

theorem keep_le {P P' : B → B → Prop} (hPP : ∀ z y, P' z y → P z y) {x : B → ℚ} (hx : 0 ≤ x)
    (t : ℕ) (b : B) : trajectory (keepOp P') x t b ≤ trajectory (keepOp P) x t b := by
  induction t generalizing b with
  | zero => exact le_rfl
  | succ t ih =>
    show tick (keepOp P') (trajectory (keepOp P') x t) b ≤
      tick (keepOp P) (trajectory (keepOp P) x t) b
    rw [tick_keepOp, tick_keepOp]
    refine Finset.sum_le_sum fun z _ => ?_
    by_cases h' : P' z b
    · rw [if_pos h', if_pos (hPP z b h')]; exact ih z
    · rw [if_neg h']
      split_ifs
      · exact trajectory_keep_nonneg P hx t z
      · exact le_rfl

/-- [proved-derived; formal-checked] **The released constitution's difference.** For `P′ ⊆ P` and
a nonnegative open state, write `D_t = x_t(P) − x_t(P′)`. Along an edge `z → y` that `P` keeps,
`D_t(z) ≤ D_(t+1)(y)`; along an edge `P` keeps and `P′` releases, also `x_t(P′)(z) ≤ D_(t+1)(y)`. -/
theorem keep_diff_step {P P' : B → B → Prop} (hPP : ∀ z y, P' z y → P z y) {x : B → ℚ}
    (hx : 0 ≤ x) (t : ℕ) {z y : B} (h : P z y) :
    (trajectory (keepOp P) x t z - trajectory (keepOp P') x t z ≤
        trajectory (keepOp P) x (t + 1) y - trajectory (keepOp P') x (t + 1) y) ∧
      (¬ P' z y → trajectory (keepOp P') x t z ≤
        trajectory (keepOp P) x (t + 1) y - trajectory (keepOp P') x (t + 1) y) := by
  set X := trajectory (keepOp P) x t
  set X' := trajectory (keepOp P') x t
  have hX' := trajectory_keep_nonneg P' hx t
  have hle := keep_le hPP hx t
  have hsum : trajectory (keepOp P) x (t + 1) y - trajectory (keepOp P') x (t + 1) y =
      ∑ w, ((if P w y then X w else 0) - (if P' w y then X' w else 0)) := by
    show tick (keepOp P) X y - tick (keepOp P') X' y = _
    rw [tick_keepOp, tick_keepOp, Finset.sum_sub_distrib]
  have hnn : ∀ w, 0 ≤ (if P w y then X w else 0) - (if P' w y then X' w else 0) := by
    intro w
    by_cases h' : P' w y
    · rw [if_pos (hPP w y h'), if_pos h']; exact sub_nonneg.mpr (hle w)
    · rw [if_neg h', sub_zero]
      split_ifs
      · exact (hX' w).trans (hle w)
      · exact le_rfl
  have hz : ∀ v, v ≤ (if P z y then X z else 0) - (if P' z y then X' z else 0) →
      v ≤ trajectory (keepOp P) x (t + 1) y - trajectory (keepOp P') x (t + 1) y := by
    intro v hv
    rw [hsum]
    exact hv.trans (Finset.single_le_sum (fun w _ => hnn w) (Finset.mem_univ z))
  constructor
  · refine hz _ ?_
    by_cases h' : P' z y
    · rw [if_pos h, if_pos h']
    · rw [if_pos h, if_neg h', sub_zero]
      exact sub_le_self _ (hX' z)
  · intro h'
    refine hz _ ?_
    rw [if_pos h, if_neg h', sub_zero]
    exact hle z

/-- Along a walk of `P` from the open block, the value of `P′` or the difference stays positive. -/
theorem keep_walk_pos {P P' : B → B → Prop} (hPP : ∀ z y, P' z y → P z y) (s : B) {b : B}
    {n : ℕ} (hr : ReachIn P s b n) :
    0 < trajectory (keepOp P') (Pi.single s (1 : ℚ)) n b ∨
      0 < trajectory (keepOp P) (Pi.single s (1 : ℚ)) n b -
        trajectory (keepOp P') (Pi.single s (1 : ℚ)) n b := by
  have hx : (0 : B → ℚ) ≤ Pi.single s 1 := Pi.single_nonneg.mpr zero_le_one
  induction hr with
  | refl => left; simp [trajectory]
  | @tail a c n _ hstep ih =>
    have hd := keep_diff_step hPP hx n hstep
    rcases ih with ih | ih
    · by_cases h' : P' a c
      · exact Or.inl (lt_of_lt_of_le ih (keep_step_le P' hx h'))
      · exact Or.inr (lt_of_lt_of_le ih (hd.2 h'))
    · exact Or.inr (lt_of_lt_of_le ih hd.1)

/-- Along a walk of `P`, a positive difference stays positive. -/
theorem keep_diff_walk {P P' : B → B → Prop} (hPP : ∀ z y, P' z y → P z y) (s : B) {a b : B}
    {m : ℕ} (hr : ReachIn P a b m) {t : ℕ}
    (ha : 0 < trajectory (keepOp P) (Pi.single s (1 : ℚ)) t a -
      trajectory (keepOp P') (Pi.single s (1 : ℚ)) t a) :
    0 < trajectory (keepOp P) (Pi.single s (1 : ℚ)) (t + m) b -
      trajectory (keepOp P') (Pi.single s (1 : ℚ)) (t + m) b := by
  have hx : (0 : B → ℚ) ≤ Pi.single s 1 := Pi.single_nonneg.mpr zero_le_one
  induction hr with
  | refl => exact ha
  | @tail c d m _ hstep ih => exact lt_of_lt_of_le ih (keep_diff_step hPP hx (t + m) hstep).1

/-- [proved-derived; formal-checked] **A released edge on a walk is read.** At the 0/1
constitution keeping `P`, release any edges (`P′ ⊆ P`) including one edge `z₀ → y₀` that a walk of
`P` from `s` through it to `ρ` passes. The word opened on the unit change at `s` reads strictly less
at `ρ` at the walk's length: no cancellation can hide a released edge a walk passes. -/
theorem walk_edge_is_read {P P' : B → B → Prop} (hPP : ∀ z y, P' z y → P z y)
    {s z₀ y₀ ρ : B} {j m : ℕ} (hs : ReachIn P s z₀ j) (he : P z₀ y₀) (hne : ¬ P' z₀ y₀)
    (hρ : ReachIn P y₀ ρ m) :
    trajectory (keepOp P') (Pi.single s (1 : ℚ)) (j + 1 + m) ρ <
      trajectory (keepOp P) (Pi.single s (1 : ℚ)) (j + 1 + m) ρ := by
  have hx : (0 : B → ℚ) ≤ Pi.single s 1 := Pi.single_nonneg.mpr zero_le_one
  have hd := keep_diff_step hPP hx j he
  have hy : 0 < trajectory (keepOp P) (Pi.single s (1 : ℚ)) (j + 1) y₀ -
      trajectory (keepOp P') (Pi.single s (1 : ℚ)) (j + 1) y₀ := by
    rcases keep_walk_pos hPP s hs with h | h
    · exact lt_of_lt_of_le h (hd.2 hne)
    · exact lt_of_lt_of_le h hd.1
  exact sub_pos.mp (keep_diff_walk hPP s hρ hy)

/-- [proved-derived; formal-checked] **The continuing collapse is tight** (#62, the diamond under
the carry, item 2). Releasing any edge that a walk from a source to a receiver passes changes an
admitted reading: at the 0/1 constitution keeping every edge, the word opened on a unit moment at a
source reads strictly less at a receiver. With `continuing_release_indistinguishable`, the loci the
continuing collapse keeps are exactly those it may keep at every constitution. -/
theorem continuing_walk_edge_is_read {S R : Set B} {z₀ y₀ : B} (he : adj z₀ y₀)
    (hw : OnWalk adj S R z₀ y₀) :
    ∃ s ∈ S, ∃ ρ ∈ R, ∃ t,
      trajectory (keepOp fun z y => adj z y ∧ ¬ (z = z₀ ∧ y = y₀)) (Pi.single s (1 : ℚ)) t ρ <
        trajectory (keepOp adj) (Pi.single s (1 : ℚ)) t ρ := by
  obtain ⟨⟨-, s, hs, n, -, hr⟩, ⟨-, ρ, hρ, n', -, hr'⟩⟩ := hw
  exact ⟨s, hs, ρ, hρ, n + 1 + n', walk_edge_is_read (fun _ _ h => h.1) hr he
    (fun h => h.2 ⟨rfl, rfl⟩) hr'⟩

omit [Fintype B] in
/-- [proved-derived; formal-checked] **The collapse of the 0/1 constitution keeps the diamond's
edges.** -/
theorem collapse_keepOp (S R : Set B) (eLast : ℕ) :
    collapse adj (fun _ _ => (0 : ℚ →ₗ[ℚ] ℚ)) S R eLast (keepOp adj) =
      keepOp fun z y => adj z y ∧ InDiamond adj S R eLast z y := by
  funext y z
  by_cases hd : InDiamond adj S R eLast z y
  · rw [collapse_of_mem hd]
    simp only [keepOp, hd, and_true]
  · rw [collapse_of_not_mem hd]
    simp only [keepOp, hd, and_false, if_false]

/-- [proved-derived; formal-checked] **The rest diamond drops the opened word's carried motion**
(#62, the diamond under the carry, item 1; `Diamond::opened`). An edge in the diamond seeded at
`𝒮 ∪ S′` but not in the rest diamond seeded at `𝒮` is read by a word opened on a carried change in
`S′`: the rest collapse of the 0/1 constitution changes that word's reading at a receiver, at an
epoch `≤ e_last`. -/
theorem rest_diamond_drops_opened {S S' R : Set B} {eLast : ℕ} {z₀ y₀ : B} (he : adj z₀ y₀)
    (hopen : InDiamond adj (S ∪ S') R eLast z₀ y₀) (hrest : ¬ InDiamond adj S R eLast z₀ y₀) :
    ∃ s ∈ S', ∃ ρ ∈ R, ∃ t ≤ eLast,
      trajectory (collapse adj (fun _ _ => (0 : ℚ →ₗ[ℚ] ℚ)) S R eLast (keepOp adj))
          (Pi.single s (1 : ℚ)) t ρ <
        trajectory (keepOp adj) (Pi.single s (1 : ℚ)) t ρ := by
  obtain ⟨j, m, ⟨s, hs, n, hn, hr⟩, ⟨ρ, hρ, n', hn', hr'⟩, hjm⟩ := hopen
  have hs' : s ∈ S' := by
    rcases hs with hs | hs
    · exact absurd ⟨j, m, ⟨s, hs, n, hn, hr⟩, ⟨ρ, hρ, n', hn', hr'⟩, hjm⟩ hrest
    · exact hs
  refine ⟨s, hs', ρ, hρ, n + 1 + n', by omega, ?_⟩
  rw [collapse_keepOp]
  exact walk_edge_is_read (fun _ _ h => h.1) hr he (fun h => hrest h.2) hr'

end CarryTight

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

/-! ## 5a. The reception cut composes on the pumped clock -/

section Cut

/-- [definition] **The word on the cumulative clock**: from the state `x` arriving at crossing
`t₀`, the step `S t` at each later tick `t` (the junction at crossing `t`, then hop `t`). The tick
index is the word's cumulative clock (record B §2.4): it is never reset at a reception. -/
def clockedRun {X : Type*} (S : ℕ → X → X) (t₀ : ℕ) (x : X) : ℕ → X
  | 0 => x
  | n + 1 => S (t₀ + n) (clockedRun S t₀ x n)

/-- [definition] **The pumped step at tick `t`** (record B §2.4, `ResonatorOperands::step`): the
junction scatters crossing `t`, then the hop runs with every resonator's pump switching from
`phase_at(t − 1)` to `phase_at(t)` (`t − 1` truncated at `0`, as the Rust's
`opened_at.saturating_sub(1)`). -/
def pumpedStep {X Φ : Type*} (J : ℕ → X → X) (hop : Φ → Φ → X → X) (phase : ℕ → Φ) (t : ℕ)
    (x : X) : X :=
  hop (phase (t - 1)) (phase t) (J t x)

/-- [proved-derived; formal-checked] **The cut composes on the clock**: running `a` steps from
crossing `t₀` and then `b` steps from crossing `t₀ + a`, from the state arriving there, is the
uninterrupted run of `a + b` steps. -/
theorem clockedRun_add {X : Type*} (S : ℕ → X → X) (t₀ : ℕ) (x : X) (a b : ℕ) :
    clockedRun S (t₀ + a) (clockedRun S t₀ x a) b = clockedRun S t₀ x (a + b) := by
  induction b with
  | zero => rfl
  | succ b ih =>
    show S (t₀ + a + b) (clockedRun S (t₀ + a) (clockedRun S t₀ x a) b) =
      S (t₀ + (a + b)) (clockedRun S t₀ x (a + b))
    rw [ih, Nat.add_assoc]

/-- [proved-derived; formal-checked] **The reception cut composes** (#62, owed by the reception
carry's clock, item 1; record B §2.4). A word opened at crossing `t₀` runs `n` full ticks and
reaches its last crossing `T = t₀ + n` (`e = n + 1` crossings); its receiver reads that crossing,
and the carry holds the change `y` arriving there, before the last junction. The next word opens on
`y` at tick `T`: its first junction scatters crossing `T` and its first hop runs at phase `T`.
Then for every later `m` it is the uninterrupted word from `T` on: its states; the hop it runs at
its step `m`, at phases `phase_at(T + m − 1)` and `phase_at(T + m)` on the scattered crossing
`T + m`; and every per-hop balance `β t (before) (after)`, whatever its reading. The proof assumes
nothing of the junction, the hop or the phase: the composition is the cumulative clock's. -/
theorem reception_cut_composes {X Φ R : Type*} (J : ℕ → X → X) (hop : Φ → Φ → X → X)
    (phase : ℕ → Φ) (β : ℕ → X → X → R) (t₀ n : ℕ) (x : X) (m : ℕ) :
    let S := pumpedStep J hop phase
    let y := clockedRun S t₀ x n
    clockedRun S (t₀ + n) y m = clockedRun S t₀ x (n + m) ∧
      clockedRun S (t₀ + n) y (m + 1) =
        hop (phase (t₀ + n + m - 1)) (phase (t₀ + n + m))
          (J (t₀ + n + m) (clockedRun S t₀ x (n + m))) ∧
      β (t₀ + n + m) (clockedRun S (t₀ + n) y m) (clockedRun S (t₀ + n) y (m + 1)) =
        β (t₀ + (n + m)) (clockedRun S t₀ x (n + m)) (clockedRun S t₀ x (n + m + 1)) := by
  intro S y
  have h := clockedRun_add S t₀ x n m
  have h' := clockedRun_add S t₀ x n (m + 1)
  refine ⟨h, ?_, ?_⟩
  · show S (t₀ + n + m) (clockedRun S (t₀ + n) y m) = _
    rw [h]
    rfl
  · rw [h, h']
    simp only [Nat.add_assoc]

/-- [proved-derived; formal-checked] **The rest word is the cut at `T = 0`** (beside
`word_opens_at_zero`). The unpumped word, one block operator at every tick, is the clocked run of
its constant step from tick `0`, whatever tick it opens at; and a cut after `0` full ticks is the
word itself. -/
theorem rest_word_is_cut_at_zero {B : Type*} [Fintype B] {K : Type*} [Field K] {M : B → Type*}
    [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)] (T : BlockOp K M) (t₀ : ℕ)
    (x : (b : B) → M b) (n : ℕ) :
    clockedRun (fun _ => tick T) t₀ x n = trajectory T x n ∧
      clockedRun (fun _ => tick T) (t₀ + 0) (clockedRun (fun _ => tick T) t₀ x 0) n =
        trajectory T x n := by
  have h : ∀ t₀ n, clockedRun (fun _ => tick T) t₀ x n = trajectory T x n := by
    intro t₀ n
    induction n with
    | zero => rfl
    | succ n ih => simp only [clockedRun, trajectory, ih]
  exact ⟨h t₀ n, by rw [Nat.add_zero]; exact h t₀ n⟩

/-- [proved-derived; formal-checked] **The pumped word opens at zero and is linear in its open
state** (`word_opens_at_zero` on the cumulative clock): with a block operator `T t` at each tick
(the pump's phase read from the tick), the clocked run from the zero state is zero at every step
and is linear in its open state. So at rest (`A = I`, no carried interior) the word opened at any
tick `T` is the run from the imposed moment alone. -/
theorem pumped_word_opens_at_zero {B : Type*} [Fintype B] {K : Type*} [Field K] {M : B → Type*}
    [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)] (T : ℕ → BlockOp K M) (t₀ : ℕ) :
    (∀ n, clockedRun (fun t => tick (T t)) t₀ 0 n = 0) ∧
      ∀ (a : K) (x x' : (b : B) → M b) (n : ℕ),
        clockedRun (fun t => tick (T t)) t₀ (a • x + x') n =
          a • clockedRun (fun t => tick (T t)) t₀ x n +
            clockedRun (fun t => tick (T t)) t₀ x' n := by
  constructor
  · intro n
    induction n with
    | zero => rfl
    | succ n ih => funext y; simp [clockedRun, tick, ih]
  · intro a x x' n
    induction n with
    | zero => rfl
    | succ n ih =>
      funext y
      simp only [clockedRun, tick, ih, Pi.add_apply, Pi.smul_apply, map_add, map_smul,
        Finset.sum_add_distrib, Finset.smul_sum]

/-- [proved-derived; formal-checked] **The cut after the junction reflects one hop.** If the carry
held the change after the last junction, `J T y`, the next word's first junction scatters it again;
the junction is an involution, so the hop at `T` runs on the unscattered `y`
(`HNN/Propagation.junctionScattering_involutive`), where the uninterrupted word runs it on `J T y`:
the crossing's scattering is undone, one hop of total reflection. -/
theorem cut_after_junction_reflects {X Φ : Type*} (J : ℕ → X → X) (hop : Φ → Φ → X → X)
    (phase : ℕ → Φ) (T : ℕ) (hJ : ∀ z, J T (J T z) = z) (y : X) :
    pumpedStep J hop phase T (J T y) = hop (phase (T - 1)) (phase T) y ∧
      pumpedStep J hop phase T y = hop (phase (T - 1)) (phase T) (J T y) := by
  simp [pumpedStep, hJ]

/-- [proved-derived; formal-checked] **The after-junction cut does not compose**: with the identity
hop and the reflecting junction `x ↦ −x` (an involution) over `ℚ`, the after-junction carry reads
`1` where the uninterrupted word reads `−1`. -/
theorem cut_after_junction_differs :
    pumpedStep (fun _ (x : ℚ) => -x) (fun (_ _ : Unit) (x : ℚ) => x) (fun _ => ()) 0
        ((fun _ (x : ℚ) => -x) 0 1) ≠
      pumpedStep (fun _ (x : ℚ) => -x) (fun (_ _ : Unit) (x : ℚ) => x) (fun _ => ()) 0 1 := by
  norm_num [pumpedStep]

/-- [proved-derived; formal-checked] **On the concrete junction**: the junction scattering of
`HNN/Propagation` is an involution (`junctionScattering_involutive`), so a carry held after it
reflects the first hop exactly as `cut_after_junction_reflects` states. -/
theorem junction_cut_reflects {V : Type*} [AddCommGroup V] [Module ℝ V] {ι : Type*} [Fintype ι]
    {Φ : Type*} (Y : ℝ) (G : ι → ℝ) (hY : Y ≠ 0) (hsum : admittanceSum Y G ≠ 0)
    (hop : Φ → Φ → V × (ι → V) → V × (ι → V)) (phase : ℕ → Φ) (T : ℕ) (y : V × (ι → V)) :
    pumpedStep (fun _ => junction Y G) hop phase T (junction Y G y) =
      hop (phase (T - 1)) (phase T) y :=
  (cut_after_junction_reflects (fun _ => junction Y G) hop phase T
    (junctionScattering_involutive Y G hY hsum) y).1

end Cut

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
#print axioms clockedRun_add
#print axioms reception_cut_composes
#print axioms rest_word_is_cut_at_zero
#print axioms pumped_word_opens_at_zero
#print axioms cut_after_junction_reflects
#print axioms cut_after_junction_differs
#print axioms junction_cut_reflects
#print axioms windowTicks_recursion
#print axioms opened_release_indistinguishable
#print axioms opened_deposit_descends
#print axioms reachWithin_card
#print axioms inDiamond_continuing_iff
#print axioms continuing_recursion
#print axioms chain_agrees_on_walk
#print axioms continuing_release_indistinguishable
#print axioms continuing_collapse_connected
#print axioms walk_edge_is_read
#print axioms continuing_walk_edge_is_read
#print axioms rest_diamond_drops_opened

end Audit

end Holonics.HNN.Retention
