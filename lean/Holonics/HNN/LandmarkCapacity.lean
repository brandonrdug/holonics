import Holonics.HNN.LandmarkCompaction

/-!
# HNN.LandmarkCapacity: a landmark's storage has a capacity, and at its ceiling it carries

[definition; agent-inferred] Decision 39 of the step 4 design (`docs/plans/THE_REBUILD.md`, "A
landmark's storage has a capacity: at its ceiling it carries"), rebuild step 4 (#73). Decisions
28–37 read a landmark's counts as exchangeable: its KT face weighs the node's first arrival as much
as its latest. A landmark is a storage on its own clock, its arrivals, and a storage has a capacity.
The computational object is the helical pair interaction; this owner is the receiving parametron's
landmark register. Of the winding guide's six general objects it touches three: the **helix** (the
node's count register winds to its capacity and carries, `n ← ⌈n/2⌉`), **faces and placement** (the
carried register's face is a normalized receiving face on each dyadic digit) and the **tower thread**
(the context depth; a chain's nodes route the same arrivals, so a stored chain keeps one register).
The pair, the cell holonomy and the tube stay attached, unchanged.

```text
register   n : A → ℕ, opened at 0
step       n' = carry_L(n + e_c) ;  carry_L(m) = ⌈m/2⌉ (each count) when Σ m ≥ L, else m ;  L = 2^c
face       k(n)(c) = (n_c + 1/2)/(Σ n + |A|/2)   KT's, read on the carried register before the next arrival
own weight M(x_1 … x_t) = ∏_t k(n_(t−1))(x_t)
c = ∞      carry_∞ = id: KT's register (Decision 28)
half units h = 2n + 1:  ⌈n/2⌉ ↦ 2⌊(h + 1)/4⌋ + 1 ;  binary: Σ n ≥ L ⟺ h_0 + h_1 ≥ 2L + 2
```

[definition; agent-inferred] **When the carry acts.** The deposit counts its arrival, and the
deposit that brings the node's total to the ceiling carries it at once: the register a node keeps
between arrivals, and the face read before the next arrival, is a function of the arrivals so far
(`capLaw`, a `LandmarkTree.NodeLaw`). The register is not a function of the counts alone: the capped
register is not exchangeable.

[proved-derived; formal-checked] What is proved.

1. **The capped register is a node law** (`capCarry`, `capLaw`, `cap_face_pos`, `cap_face_sum`): its
   face is KT's on the carried counts, positive and normalized at every register.
2. **The carry** (`cap_carry_laws`, `cap_carry_half_units`): it only lowers the total, a reached
   symbol keeps a count and an unreached one stays at zero; so a node's total never passes its
   arrivals (`cap_run_total_le`), and KT's floor `1/(2n + 2)` and the lattice's widths hold unchanged.
   On half-unit masses `h = 2n + 1` it is `h ↦ 2⌊(h + 1)/4⌋ + 1`, and on a binary digit the ceiling
   reads `h_0 + h_1 ≥ 2L + 2`.
3. **`c = ∞` and every ceiling a node does not reach are KT's register** (`cap_unbounded_is_kt`,
   `cap_below_ceiling_is_kt`): the unbounded law is `LandmarkTree.ktLaw`; at the ceiling `L` a node
   reached fewer than `L` times holds its counts, and its own weight over at most `L` arrivals is
   KT's.
4. **The capped tree** (`capped_tree_laws`): stored where paths part it is the capped tree of one
   node a depth, code for code, exactly in `ℚ` (`LandmarkCompaction.compacted_node_law`); its face is
   positive and normalized, its root weight is the prequential code of its faces, and the code is
   complete. Over a passage shorter than the ceiling (every passage when `c = ∞`) it is Decision 28's
   tree exactly: weight `LandmarkTree.stopWeight` and face `LandmarkTree.stopFace`.

The tree weighting's Kraft form and dominance hold at the capped register's own weights as at any
node law's (`LandmarkTree.own_mixture_over_trees`, `own_kraft_and_dominance`).

[conditional] The capped register's code against a source that drifts (a piecewise-stationary
source, the reason a capacity can pay) is not bounded here: whether a ceiling earns bits on a cut is
a measurement (Decision 39's receipt), not a theorem.

The Rust consumer is `crates/holonics/src/hnn/landmark.rs` (`hnn::landmark::Capacity`, declared in
`LandmarkDeclaration::capacity`, consumed by the one `Law`'s deposit and by `IdealLandmarks`): the
node's half-unit masses carry at the ceiling after each deposit, and a stored chain is one register.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LandmarkCapacity

open Finset
open Holonics.HNN.LandmarkTree
open Holonics.HNN.LandmarkCompaction
open Holonics.HNN.ConvergenceFounding (prequentialCode)

universe v

/-! ## 1. The capped register -/

section Register

variable {A : Type v} [Fintype A] [DecidableEq A]

/-- [definition] **The register's carry at the ceiling**: unbounded (`none`, `c = ∞`) it never
carries; at the ceiling `L` (`some L`, `L = 2^c`) a register whose total reaches `L` carries every
count, `n ← ⌈n/2⌉ = ⌊(n + 1)/2⌋`. -/
def capCarry (cap : Option ℕ) (n : A → ℕ) : A → ℕ :=
  match cap with
  | none => n
  | some L => if L ≤ ∑ c, n c then fun c => (n c + 1) / 2 else n

/-- [definition] **The capped register's node law** (Decision 39): the register is the counts,
stepped by the arrival's count and then the carry, and read at KT's face on the carried counts. -/
def capLaw (A : Type v) [Fintype A] [DecidableEq A] [Nonempty A] (cap : Option ℕ) : NodeLaw A where
  State := A → ℕ
  init := fun _ => 0
  step := fun n c => capCarry cap (bump n c)
  face := ktFace
  face_pos := ktFace_pos
  face_sum := ktFace_sum

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`cap_face_pos`: the capped register's face is positive**, at
every register. -/
theorem cap_face_pos [DecidableEq A] [Nonempty A] (cap : Option ℕ) (σ : (capLaw A cap).State)
    (c : A) : 0 < (capLaw A cap).face σ c :=
  ktFace_pos σ c

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`cap_face_sum`: the capped register's face is normalized**,
at every register. -/
theorem cap_face_sum [DecidableEq A] [Nonempty A] (cap : Option ℕ) (σ : (capLaw A cap).State) :
    ∑ c, (capLaw A cap).face σ c = 1 :=
  ktFace_sum σ

/-- [proved-derived; formal-checked] **`cap_unbounded_is_kt`: `c = ∞` is KT's register** (Decision
28's node): the unbounded capped law is `ktLaw`. -/
theorem cap_unbounded_is_kt [Nonempty A] : capLaw A none = ktLaw A := rfl

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`cap_carry_laws`: the carry only lowers the register, and a
reached symbol keeps a count.** For every ceiling: the carried total is at most the total, each
carried count is at most the count, a positive count stays positive and a zero count stays zero. -/
theorem cap_carry_laws (cap : Option ℕ) (n : A → ℕ) :
    ∑ c, capCarry cap n c ≤ ∑ c, n c ∧ (∀ c, capCarry cap n c ≤ n c) ∧
      ∀ c, (0 < capCarry cap n c ↔ 0 < n c) := by
  have hle : ∀ c, capCarry cap n c ≤ n c := fun c => by
    cases cap with
    | none => exact le_rfl
    | some L =>
      simp only [capCarry]
      split_ifs
      · show (n c + 1) / 2 ≤ n c
        omega
      · exact le_rfl
  refine ⟨Finset.sum_le_sum fun c _ => hle c, hle, fun c => ?_⟩
  cases cap with
  | none => exact Iff.rfl
  | some L =>
    simp only [capCarry]
    split_ifs
    · show 0 < (n c + 1) / 2 ↔ 0 < n c
      omega
    · exact Iff.rfl

/-- [proved-derived; formal-checked] **`cap_carry_half_units`: the carry on half-unit masses.** A
count `n` is carried as its half-unit mass `h = 2n + 1` (the executed arena's): `⌈n/2⌉` has the
half-unit mass `2⌊(h + 1)/4⌋ + 1`, and on a binary digit the ceiling `n_0 + n_1 ≥ L` reads
`h_0 + h_1 ≥ 2L + 2`. -/
theorem cap_carry_half_units (n n₀ n₁ L : ℕ) :
    2 * ((n + 1) / 2) + 1 = 2 * ((2 * n + 1 + 1) / 4) + 1 ∧
      (L ≤ n₀ + n₁ ↔ 2 * L + 2 ≤ (2 * n₀ + 1) + (2 * n₁ + 1)) := by
  constructor <;> omega

omit [DecidableEq A] in
/-- The capped register after a word. -/
theorem cap_run_snoc [DecidableEq A] [Nonempty A] (cap : Option ℕ) (w : List A) (c : A) :
    (capLaw A cap).run (w ++ [c]) = capCarry cap (bump ((capLaw A cap).run w) c) :=
  NodeLaw.run_snoc _ w c

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`cap_run_total_le`: a node's total never passes its
arrivals.** The capped register's total after a word is at most the word's length, so a node's KT
face is at least `1/(2n + 2)` over `n` arrivals (`LandmarkTree.kt_binary_ge`), as without a
capacity. -/
theorem cap_run_total_le [DecidableEq A] [Nonempty A] (cap : Option ℕ) (w : List A) :
    ∑ c, (capLaw A cap).run w c ≤ w.length := by
  induction w using List.reverseRecOn with
  | nil => simp [NodeLaw.run_nil, capLaw]
  | append_singleton w c ih =>
    rw [cap_run_snoc, List.length_append, List.length_singleton]
    calc ∑ c', capCarry cap (bump ((capLaw A cap).run w) c) c'
        ≤ ∑ c', bump ((capLaw A cap).run w) c c' := (cap_carry_laws cap _).1
      _ = ∑ c', (capLaw A cap).run w c' + 1 := sum_bump _ c
      _ ≤ w.length + 1 := by omega

omit [DecidableEq A] in
/-- [proved-derived; formal-checked] **`cap_below_ceiling_is_kt`: a node the ceiling has not reached
reads KT exactly.** At the ceiling `L`, a node reached by a word of fewer than `L` arrivals holds the
word's counts (no carry has acted), and its own weight over at most `L` arrivals is KT's sequential
likelihood (every face it read was read before any carry). -/
theorem cap_below_ceiling_is_kt [DecidableEq A] [Nonempty A] (L : ℕ) (w : List A) :
    (w.length < L → (capLaw A (some L)).run w = counts w) ∧
      (w.length ≤ L → (capLaw A (some L)).mass w = ktSeq w) := by
  induction w using List.reverseRecOn with
  | nil => exact ⟨fun _ => counts_nil.symm, fun _ => ktSeq_nil.symm⟩
  | append_singleton w c ih =>
    simp only [List.length_append, List.length_singleton] at ih ⊢
    have hrun : w.length + 1 < L → (capLaw A (some L)).run (w ++ [c]) = counts (w ++ [c]) := by
      intro hw
      rw [cap_run_snoc, ih.1 (by omega), counts_snoc]
      have hsum : ¬ L ≤ ∑ c', bump (counts w) c c' := by
        rw [sum_bump, sum_counts]
        omega
      show capCarry (some L) (bump (counts w) c) = bump (counts w) c
      simp only [capCarry]
      rw [if_neg hsum]
    refine ⟨fun hw => hrun hw, fun hw => ?_⟩
    rw [NodeLaw.mass_snoc, ih.2 (by omega), ih.1 (by omega)]
    show ktSeq w * ktFace (counts w) c = ktSeq (w ++ [c])
    simp only [ktSeq, counts_snoc, ktMass_bump]

end Register

/-! ## 2. The capped tree -/

section Tree

variable {Ltr : Type*} [Fintype Ltr] [DecidableEq Ltr] {A : Type v} [Fintype A] [DecidableEq A]
  [Nonempty A]

omit [Fintype Ltr] [Fintype A] [DecidableEq A] [Nonempty A] in
/-- A node's routed subsequence is no longer than the passage. -/
theorem routed_length_le (ctx : List A → List Ltr) (h : List A) (s : List Ltr) :
    (routed (observations ctx h) s).length ≤ h.length := by
  have hobs : ∀ h, (observations ctx h).length = h.length := by
    intro h
    induction h with
    | nil => rfl
    | cons c h ih => simp [observations, ih]
  calc (routed (observations ctx h) s).length
      ≤ (observations ctx h).length := by
        simp only [routed, List.length_map]
        exact List.length_filter_le _ _
    _ = h.length := hobs h

omit [Fintype Ltr] in
/-- [proved-derived; formal-checked] **Below the ceiling the capped standing is Decision 28's**: over
a passage of fewer than `L` arrivals (every passage when `c = ∞`), each node's register is its count
table and its own weight its KT mass. -/
theorem cap_standing_below (cap : Option ℕ) (ctx : List A → List Ltr) (h : List A)
    (hL : ∀ L, cap = some L → h.length < L) (s : List Ltr) :
    lawState (capLaw A cap) (lawStandingOf (capLaw A cap) ctx h) s = standingOf ctx h s ∧
      lawOwn (capLaw A cap) (lawStandingOf (capLaw A cap) ctx h) s =
        ktMass (standingOf ctx h s) := by
  cases cap with
  | none => exact ktLaw_standing ctx h s
  | some L =>
    obtain ⟨hs, ho⟩ := law_state_own_routed (capLaw A (some L)) ctx h s
    obtain ⟨hN, -⟩ := standing_is_routed_counts ctx h s
    have hlen := lt_of_le_of_lt (routed_length_le ctx h s) (hL L rfl)
    rw [hs, ho, (cap_below_ceiling_is_kt L _).1 hlen, (cap_below_ceiling_is_kt L _).2 hlen.le, hN]
    exact ⟨rfl, rfl⟩

/-- [definition] **The capped tree's root face** after a past, at the address it opens: the node
law's tree face at the capped register (`LandmarkTree.lawFace`). -/
def capFace (cap : Option ℕ) (j : ℕ → ℕ) (D : ℕ) (ctx : List A → List Ltr) (h : List A) :
    A → ℚ :=
  lawFace (capLaw A cap) (fun d => ladder (j d)) (lawStandingOf (capLaw A cap) ctx h) D (ctx h) 0

/-- [definition] **The capped tree's root weight** after a past. -/
def capWeight (cap : Option ℕ) (j : ℕ → ℕ) (D : ℕ) (ctx : List A → List Ltr) (h : List A) : ℚ :=
  ownWeight (fun d => ladder (j d)) (lawOwn (capLaw A cap) (lawStandingOf (capLaw A cap) ctx h)) D []

/-- [definition] **The compacted capped tree's root face**: stored where paths part (Decision 37),
an absent child read at the register's opening face. -/
def capCompactFace (cap : Option ℕ) (j : ℕ → ℕ) (D : ℕ) (ctx : List A → List Ltr) (h : List A) :
    A → ℚ :=
  massCompactFace j (lawReached (capLaw A cap) (lawStandingOf (capLaw A cap) ctx h))
    (lawOwn (capLaw A cap) (lawStandingOf (capLaw A cap) ctx h))
    (fun s => (capLaw A cap).face (lawState (capLaw A cap) (lawStandingOf (capLaw A cap) ctx h) s))
    ((capLaw A cap).face (capLaw A cap).init) D (ctx h)

/-- [definition] **The compacted capped tree's root weight.** -/
def capCompactWeight (cap : Option ℕ) (j : ℕ → ℕ) (D : ℕ) (ctx : List A → List Ltr)
    (h : List A) : ℚ :=
  massCompactWeight j (lawReached (capLaw A cap) (lawStandingOf (capLaw A cap) ctx h))
    (lawOwn (capLaw A cap) (lawStandingOf (capLaw A cap) ctx h)) D

/-- [proved-derived; formal-checked] **`capped_tree_laws`: the capped tree** (Decision 39). At any
ceiling (`some L`, `L = 2^c`) or none (`c = ∞`), on the dyadic ladder `w_d = 1 − 2^(−j_d)` at any
rungs `j_d ≥ 0`, for every passage built by arrivals from the empty standing over addresses
reaching the declared depth `D`:
* **stored where paths part it is the capped tree**: the compacted weight and face are the capped
  tree's of one node a depth, each stored chain one register (`compacted_node_law`);
* **its face is a receiving face**: positive and normalized;
* **its code**: the compacted root weight is the prequential code of its faces, and that code is
  complete (it sums to one over the words of every length);
* **below the ceiling it is Decision 28's tree**: over a passage of fewer than `L` arrivals, and
  over every passage when `c = ∞`, its weight is `stopWeight` and its face `stopFace`, exactly. -/
theorem capped_tree_laws (cap : Option ℕ) (j : ℕ → ℕ) (D : ℕ) (ctx : List A → List Ltr)
    (hctx : ∀ h, D ≤ (ctx h).length) :
    (∀ h, capCompactWeight cap j D ctx h = capWeight cap j D ctx h) ∧
      (∀ h, capCompactFace cap j D ctx h = capFace cap j D ctx h) ∧
      (∀ h, (∀ c, 0 < capFace cap j D ctx h c) ∧ ∑ c, capFace cap j D ctx h c = 1) ∧
      (∀ h, capCompactWeight cap j D ctx h = prequentialCode (capFace cap j D ctx) h) ∧
      (∀ n, wordSum n (prequentialCode (capFace cap j D ctx)) = 1) ∧
      ∀ h, (∀ L, cap = some L → h.length < L) →
        capWeight cap j D ctx h = stopWeight (fun d => ladder (j d)) (standingOf ctx h) D [] ∧
          capFace cap j D ctx h = stopFace (fun d => ladder (j d)) (standingOf ctx h) D (ctx h) 0 := by
  obtain ⟨hweight, hface, hnorm, hpre, hcomplete⟩ :=
    compacted_node_law (capLaw A cap) j D ctx hctx
  refine ⟨hweight, fun h => funext (hface h), hnorm, hpre, hcomplete, fun h hL => ?_⟩
  have hown : lawOwn (capLaw A cap) (lawStandingOf (capLaw A cap) ctx h) =
      fun s => ktMass (standingOf ctx h s) :=
    funext fun s => (cap_standing_below cap ctx h hL s).2
  have hstate : ∀ s, lawState (capLaw A cap) (lawStandingOf (capLaw A cap) ctx h) s =
      standingOf ctx h s := fun s => (cap_standing_below cap ctx h hL s).1
  refine ⟨?_, ?_⟩
  · rw [capWeight, hown, ownWeight_kt]
  · rw [capFace, lawFace, hown, ownLam_kt]
    simp only [hstate]
    rfl

end Tree

section Audit

#print axioms cap_face_pos
#print axioms cap_face_sum
#print axioms cap_unbounded_is_kt
#print axioms cap_carry_laws
#print axioms cap_carry_half_units
#print axioms cap_run_snoc
#print axioms cap_run_total_le
#print axioms cap_below_ceiling_is_kt
#print axioms routed_length_le
#print axioms cap_standing_below
#print axioms capped_tree_laws

end Audit

end Holonics.HNN.LandmarkCapacity
