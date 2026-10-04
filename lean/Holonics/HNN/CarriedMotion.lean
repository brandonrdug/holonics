import Holonics.HNN.LocusMap

/-!
# HNN.CarriedMotion: a releasing collapse releases the carried motion its material held

[definition] #62 and #310 (record B §8, atlas `hnn.carried-motion-released`): under the reception
carry a releasing collapse (`hnn::reference::Reference::close_aeon`, `hnn::retention::collapse`)
releases with each released locus's material the motion that material held
(`hnn::word::ReceptionCarry::released`, `hnn::word::WordOpening::released`). A released channel
`a` drops its state `[u_a, w_a]` and its momentum `π_a = C_a w_a`; a released resonator drops its
state, phase and momentum. Arrivals stay (they sit on the declared conductance at the lift), and
so does ring storage (on the declared admittance `Y_r`); neither is a constitution locus. The
release reaches the resident's carry, every carried pending opening and the arrived opening.

On `Word.Medium` the contact block `a` holds the channel state `(u_a, w_a)`; the arrivals and the
storage wave sit in the rings' blocks (`TickBlocks.BlockM`). The momentum `π_a = C_a w_a` is a
reading of the state at the material, so it leaves with `w_a`. `releaseMotion keep x` zeroes the
contact block of every channel the collapse does not keep and leaves every ring block whole.

[proved-derived; formal-checked] What is proved.

1. **The argument, on any block graph** (`motion_release_agrees`). A change carried on the blocks
   a walk from the sources reaches agrees with its motion release on every block that observes a
   receiver, when the release moves only blocks that a walk from a source to a receiver does not
   pass. A released block reached from a source that observed a receiver would put itself on such a
   walk, so the collapse would have kept it (the reviewer's argument).
2. **The concrete release moves only off-walk blocks** (`releaseMotion_agrees`). Under the Rust's
   rule at the continuing diamond (`Diamond::continuing`, `e_last = 2 |B|`; `LocusMap.Retained`),
   a released channel's contact block is never both reached from a source and observing a
   receiver: through its end ring the edge into the receiver would lie on a walk, and
   `LocusMap.channel_of_edge` would retain the channel.
3. **Indistinguishable along the continuing chain** (`carried_motion_release_indistinguishable`,
   `continuing_motion_release_indistinguishable`). Releasing the material
   (`LocusMap.release`) and the carried motion it held together, at an aeon's close, changes no
   admitted reading of any later word of the chain at any class and any epoch. The carried change
   may be any change on the reached blocks: the resident's carry (`chainEnd` of the words before
   the close), a pending ratio's carried opening, or the arrived targets' opening.
4. **The first law's re-read is decided on the pre-release diamond** (`first_law_held_diamond`;
   the fix in `80546c9e`, host `Reference::close_aeon`, card `port.rs`). The arrived targets'
   reading was taken on the opening before the release. When no locus the collapse releases is
   retained by the diamond seeded on that opening's support (with each contact block's end rings,
   `EndChange::support`), the reading on the released opening at the collapsed medium equals the
   held reading at every epoch `t ≤ e`, so the exchange step is not needed. The hypothesis that the
   held opening is supported on the seed set is what fails for the post-release support:
   `EndChange::support` drops a contact's rings once its state is zero, and the motion the release
   removed may be all that put a ring in the seed.

[open] **The resonator's motion** (owed in #62). `Word.Medium` carries no resonator operand
(`LocusMap`'s first owed item), so the concrete statement here covers the channels. A resonator
sits on its ring's element edge `g → g` and its state on its ring; `motion_release_agrees` and
`carried_motion_release_indistinguishable'` hold for any block layout and any sparse operator
family, so they cover the resonator's state once the loaded ring's block carries it. The pumped
resonator's operator moves with the tick: the tick-indexed family, owed in #62
(`HNN/CarriedStanding`'s second model limit).

This closes `HNN/CarriedStanding`'s third model limit (its `retain` keeps the carry whole): the
carry `carriedStanding` keeps whole and the carry released here give the same admitted readings.
`HNN/Word`, `HNN/TickBlocks`, `HNN/Retention`, `HNN/CarriedStanding` (its header excepted) and
`HNN/LocusMap` are unchanged. No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.CarriedMotion

open Holonics.Geometry.AffineSwing
open Holonics.HNN.Propagation
open Holonics.HNN.Word
open Holonics.HNN.TickBlocks
open Holonics.HNN.Retention
open Holonics.HNN.LocusMap
open scoped BigOperators

universe u

/-! ## 1. The argument on any block graph -/

section Generic

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]

omit [Fintype B] in
/-- [proved-derived; formal-checked] **A motion release that moves only off-walk blocks agrees on
every observing block.** A carried change supported on the blocks reached from the sources, and a
release of it that is again so supported and changes no block both reached and observing, agree on
every block that observes a receiver: an unreached block holds no motion in either. -/
theorem motion_release_agrees {S R : Set B} {x x' : (b : B) → M b}
    (hx : SupportedIn x (reachAll adj S)) (hx' : SupportedIn x' (reachAll adj S))
    (hwalk : ∀ b, b ∈ reachAll adj S → ObservesAll adj R b → x' b = x b) :
    ∀ b, ObservesAll adj R b → x' b = x b := by
  intro b hb
  by_cases hr : b ∈ reachAll adj S
  · exact hwalk b hr hb
  · rw [hx b hr, hx' b hr]

variable {Cls : Type*} {Θ : B → B → Type*}
variable {op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y)}

/-- [proved-derived; formal-checked] **Releasing the material and the carried motion it held is
indistinguishable along the continuing chain**, on any block graph and any sparse family. Two
families that agree on every walk edge, run from a carried change and its motion release, give
every later word of any chain the same admitted readings at every class and epoch. -/
theorem carried_motion_release_indistinguishable' {θ θ' : (y z : B) → Θ y z}
    (hθ : LociSparse adj op θ) (hθ' : LociSparse adj op θ') {S R : Set B}
    (hagree : ∀ c y z, OnWalk adj S R z y → op c y z (θ' y z) = op c y z (θ y z))
    {x x' : (b : B) → M b} (hx : SupportedIn x (reachAll adj S))
    (hx' : SupportedIn x' (reachAll adj S))
    (hwalk : ∀ b, b ∈ reachAll adj S → ObservesAll adj R b → x' b = x b)
    (ws : List (Cls × ℕ × ((b : B) → M b))) (hws : ∀ w ∈ ws, SupportedIn w.2.2 S) (c : Cls)
    {u : (b : B) → M b} (hu : SupportedIn u S) (t : ℕ) {g : (b : B) → Module.Dual K (M b)}
    (hg : SupportedIn g R) :
    pair g (trajectory (readOp op c θ') (chainEnd op θ' x' ws + u) t) =
      pair g (trajectory (readOp op c θ) (chainEnd op θ x ws + u) t) := by
  have hch := chain_agrees_on_walk hθ' hθ hagree ws hws hx' hx
    (motion_release_agrees hx hx' hwalk)
  have hu' : SupportedIn u (reachAll adj S) := fun b hb =>
    hu b fun hbS => hb (subset_reachAll S hbS)
  have hadd : ∀ v : (b : B) → M b, SupportedIn v (reachAll adj S) →
      SupportedIn (v + u) (reachAll adj S) := fun v hv b hb => by simp [hv b hb, hu' b hb]
  have h := trajectory_agrees_on_walk (sparse_readOp hθ' c) (sparse_readOp hθ c)
    (fun y z hw => hagree c y z hw) (hadd _ hch.1) (hadd _ hch.2.1)
    (fun b hb => by rw [Pi.add_apply, Pi.add_apply, hch.2.2 b hb]) t
  exact pair_agrees_on_observers hg h.2.2

theorem trajectory_sub (T : BlockOp K M) (x x' : (b : B) → M b) (t : ℕ) :
    trajectory T x t - trajectory T x' t = trajectory T (x - x') t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    funext y
    simp only [trajectory, tick, Pi.sub_apply, ← ih, map_sub, Finset.sum_sub_distrib]

theorem pair_sub (g : (b : B) → Module.Dual K (M b)) (x x' : (b : B) → M b) :
    pair g x - pair g x' = pair g (x - x') := by
  simp only [pair, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]

end Generic

/-! ## 2. The concrete motion release -/

section Concrete

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}

open Classical in
/-- [definition] **The carried motion across a releasing collapse** (`ReceptionCarry::released`):
the contact block `(u_a, w_a)` of every channel the collapse does not keep becomes zero, and with
`w_a` its momentum `π_a = C_a w_a`; every ring block (storage wave and arrivals) stays. -/
def releaseMotion (keep : Locus Ring Contact → Prop)
    (x : (b : Ring ⊕ Contact) → BlockM endRing V Ch b) : (b : Ring ⊕ Contact) → BlockM endRing V Ch b
  | .inl r => x (.inl r)
  | .inr a => if keep (.channel a) then x (.inr a) else 0

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact]
  [∀ r, InnerProductSpace ℝ (V r)] [∀ a, InnerProductSpace ℝ (Ch a)]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
/-- The motion release keeps zero blocks zero. -/
theorem releaseMotion_supported {keep : Locus Ring Contact → Prop}
    {x : (b : Ring ⊕ Contact) → BlockM endRing V Ch b} {S : Set (Ring ⊕ Contact)}
    (hx : SupportedIn x S) : SupportedIn (releaseMotion keep x) S := by
  classical
  intro b hb
  cases b with
  | inl r => exact hx _ hb
  | inr a =>
    simp only [releaseMotion]
    split_ifs
    · exact hx _ hb
    · rfl

omit [DecidableEq Ring] [DecidableEq Contact]
  [∀ r, InnerProductSpace ℝ (V r)] [∀ a, InnerProductSpace ℝ (Ch a)]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
/-- [proved-derived; formal-checked] **The concrete release moves only off-walk blocks.** Under
the continuing rule a released channel's contact block is never both reached from a source and
observing a receiver: its edge into an observing end ring would lie on a walk, and the channel
would be retained (`LocusMap.channel_of_edge`, `Retention.inDiamond_continuing_iff`). -/
theorem releaseMotion_agrees {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {keep : Locus Ring Contact → Prop}
    (hkeep : ∀ ℓ, Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact)) ℓ → keep ℓ)
    (x : (b : Ring ⊕ Contact) → BlockM endRing V Ch b) (b : Ring ⊕ Contact)
    (hr : b ∈ reachAll (blockAdj endRing) S) (ho : ObservesAll (blockAdj endRing) R b) :
    releaseMotion keep x b = x b := by
  classical
  cases b with
  | inl r => rfl
  | inr a =>
    simp only [releaseMotion]
    split_ifs with hk
    · rfl
    · exfalso
      obtain ⟨m, hm⟩ := ho
      obtain ⟨s, m', -, ho'⟩ := obs_contact hR hm
      have hw : OnWalk (blockAdj endRing) S R (.inr a) (.inl (endRing (a, s))) := ⟨hr, ⟨m', ho'⟩⟩
      have hd := (inDiamond_continuing_iff (adj := blockAdj endRing) S R _ _).mpr hw
      exact hk (hkeep _ (channel_of_edge hS hR (Or.inl rfl) (Or.inr ⟨s, rfl⟩) hd))

/-- [proved-derived; formal-checked] **The carried motion released with its material is
indistinguishable along the continuing chain** (#310, record B §8; `ReceptionCarry::released`,
`WordOpening::released`, `Reference::close_aeon`). From any carried change on the blocks the
sources reach (the resident's carry, a pending ratio's carried opening, the arrived opening),
releasing the channels the continuing rule does not keep (`LocusMap.release`) together with the
motion they held (`releaseMotion`), then running any chain of later words each opened on the last
one's end plus a source moment, changes no admitted reading of any later word at any class and
epoch. -/
theorem carried_motion_release_indistinguishable {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R)
    {x : (b : Ring ⊕ Contact) → BlockM endRing V Ch b}
    (hx : SupportedIn x (reachAll (blockAdj endRing) S))
    (ws : List ((Ring → ρ → ℝ) × ℕ × ((b : Ring ⊕ Contact) → BlockM endRing V Ch b)))
    (hws : ∀ w ∈ ws, SupportedIn w.2.2 S) (c : Ring → ρ → ℝ)
    {u : (b : Ring ⊕ Contact) → BlockM endRing V Ch b} (hu : SupportedIn u S) (t : ℕ)
    {g : (b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b)} (hg : SupportedIn g R) :
    pair g (trajectory (readOp mediumOp c
        (fun _ _ => release (Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact))) μ))
        (chainEnd mediumOp
          (fun _ _ => release (Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact))) μ)
          (releaseMotion (Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact))) x) ws + u) t) =
      pair g (trajectory (readOp mediumOp c (fun _ _ => μ))
        (chainEnd mediumOp (fun _ _ => μ) x ws + u) t) :=
  carried_motion_release_indistinguishable' (lociSparse_uniform μ) (lociSparse_uniform _)
    (fun c y z hw => mediumOp_release_on_walk hμ hS hR c y z hw) hx
    (releaseMotion_supported hx) (releaseMotion_agrees hS hR (fun _ h => h) x) ws hws c hu t hg

/-- [proved-derived; formal-checked] **The aeon's close on the continuing chain.** Words before the
close run on the medium; at the close the collapse releases the material and the carried motion it
held; the words after it run on the released medium from the released carry. Every admitted
reading of every word after the close is the one the unreleased run gives, at every class and
epoch. -/
theorem continuing_motion_release_indistinguishable {μ : Medium endRing V Ch ρ}
    (hμ : μ.Admissible) {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R)
    (before after : List ((Ring → ρ → ℝ) × ℕ × ((b : Ring ⊕ Contact) → BlockM endRing V Ch b)))
    (hbefore : ∀ w ∈ before, SupportedIn w.2.2 S) (hafter : ∀ w ∈ after, SupportedIn w.2.2 S)
    (c : Ring → ρ → ℝ) {u : (b : Ring ⊕ Contact) → BlockM endRing V Ch b} (hu : SupportedIn u S)
    (t : ℕ) {g : (b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b)}
    (hg : SupportedIn g R) :
    pair g (trajectory (readOp mediumOp c
        (fun _ _ => release (Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact))) μ))
        (chainEnd mediumOp
          (fun _ _ => release (Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact))) μ)
          (releaseMotion (Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact)))
            (chainEnd mediumOp (fun _ _ => μ) 0 before)) after + u) t) =
      pair g (trajectory (readOp mediumOp c (fun _ _ => μ))
        (chainEnd mediumOp (fun _ _ => μ) (chainEnd mediumOp (fun _ _ => μ) 0 before) after + u)
        t) := by
  have h0 : SupportedIn (0 : (b : Ring ⊕ Contact) → BlockM endRing V Ch b)
      (reachAll (blockAdj endRing) S) := fun _ _ => rfl
  have hx := (chain_agrees_on_walk (R := R) (lociSparse_uniform μ) (lociSparse_uniform μ)
    (fun _ _ _ _ => rfl) before hbefore h0 h0 fun _ _ => rfl).1
  exact carried_motion_release_indistinguishable hμ hS hR hx after hafter c hu t hg

/-! ## 3. The first law's re-read on the pre-release diamond -/

omit [Fintype Ring] in
/-- The release keeps every edge of a diamond whose retained loci it keeps. -/
theorem blockOp_release_kept {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {e : ℕ} {keep : Locus Ring Contact → Prop}
    (hkeep : ∀ ℓ, Retained endRing S R e ℓ → keep ℓ) {y z : Ring ⊕ Contact}
    (hd : InDiamond (blockAdj endRing) S R e z y) :
    blockOp (release_admissible hμ keep) y z = blockOp hμ y z :=
  blockOp_agree (release_admissible hμ _) hμ rfl fun _ hℓ =>
    agreeOn_release (hkeep _ (retained_of_reads hS hR hℓ hd))

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
/-- A contact block whose channel the held diamond does not retain, seeded with its end rings,
observes no receiver within the diamond's last epoch. -/
theorem released_contact_unobserved {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {e : ℕ} {a : Contact}
    (ha : (.inr a : Ring ⊕ Contact) ∈ S) (hn : ¬ ChannelRetained endRing S R e a) {m : ℕ}
    (hm : m ≤ e) : ¬ Observes (blockAdj endRing) R (.inr a) m := by
  intro ho
  obtain ⟨s, m', hm', ho'⟩ := obs_contact hR ho
  exact hn ⟨0, m', s, s, ⟨_, hS a ha s, 0, le_rfl, ReachIn.refl _⟩, ho', by omega⟩

/-- [proved-derived; formal-checked] **The first law's re-read is decided on the pre-release
diamond** (the fix in `80546c9e`: host `Reference::close_aeon`, card `port.rs`). Let the arrived
targets' opening `x` be supported on the seed set `S` of its diamond (its support with each contact
block's end rings, `EndChange::support` before the release). When every locus that diamond retains
at its last epoch `e` is kept by the collapse, the reading of the released opening on the released
medium equals the held reading of `x` on the medium at every epoch `t ≤ e`: the exchange step
(`Ledger::release` of the re-read) is not needed. -/
theorem first_law_held_diamond {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {e : ℕ} {keep : Locus Ring Contact → Prop}
    (hkeep : ∀ ℓ, Retained endRing S R e ℓ → keep ℓ)
    {x : (b : Ring ⊕ Contact) → BlockM endRing V Ch b} (hx : SupportedIn x S)
    {g : (b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b)} (hg : SupportedIn g R)
    {t : ℕ} (ht : t ≤ e) :
    pair g (trajectory (blockOp (release_admissible hμ keep)) (releaseMotion keep x) t) =
      pair g (trajectory (blockOp hμ) x t) := by
  classical
  -- The released medium reads the same on every diamond edge.
  have h1 : pair g (trajectory (blockOp (release_admissible hμ keep)) (releaseMotion keep x) t) =
      pair g (trajectory (blockOp hμ) (releaseMotion keep x) t) :=
    release_past_diamond (blockOp_sparse _) (blockOp_sparse _) (releaseMotion_supported hx) hg ht
      fun _ _ hd => blockOp_release_kept hμ hS hR hkeep hd
  rw [h1, ← sub_eq_zero, pair_sub, trajectory_sub]
  -- The released motion sits on contact blocks no diamond edge leaves.
  set δ := releaseMotion keep x - x
  let Z : Set (Ring ⊕ Contact) :=
    {b | ∃ a, b = .inr a ∧ ¬ keep (.channel a) ∧ (.inr a : Ring ⊕ Contact) ∈ S}
  have hδ : SupportedIn δ Z := by
    intro b hb
    cases b with
    | inl r => simp [δ, releaseMotion]
    | inr a =>
      simp only [δ, Pi.sub_apply, releaseMotion]
      split_ifs with hk
      · exact sub_self _
      · have hS' : (.inr a : Ring ⊕ Contact) ∉ S := fun h => hb ⟨a, rfl, hk, h⟩
        rw [hx _ hS', sub_self]
  have hzero : ∀ y z, InDiamond (blockAdj endRing) Z R e z y →
      blockOp hμ y z = (0 : BlockOp ℝ (BlockM endRing V Ch)) y z := by
    rintro y z ⟨j, m, ⟨b, ⟨a, rfl, hk, haS⟩, n, hn, hr⟩, ho, hjm⟩
    by_cases hadj : blockAdj endRing z y
    · exfalso
      have hnr : ¬ ChannelRetained endRing S R e a := fun h => hk (hkeep (.channel a) h)
      exact released_contact_unobserved hS hR haS hnr (m := n + (m + 1)) (by omega)
        (observes_trans ⟨n, le_rfl, hr⟩ (observes_step hadj ho))
    · rw [blockOp_sparse hμ y z hadj]
      rfl
  rw [release_past_diamond (T := 0) (fun _ _ _ => rfl) (blockOp_sparse hμ) hδ hg ht hzero]
  cases t with
  | zero =>
    refine Finset.sum_eq_zero fun b _ => ?_
    by_cases hb : b ∈ Z
    · obtain ⟨a, rfl, -, -⟩ := hb
      simp [hg _ (hR a)]
    · simp [trajectory, hδ b hb]
  | succ k =>
    refine Finset.sum_eq_zero fun b _ => ?_
    simp [trajectory, tick]

end Concrete

section Audit

#print axioms motion_release_agrees
#print axioms carried_motion_release_indistinguishable'
#print axioms releaseMotion_agrees
#print axioms carried_motion_release_indistinguishable
#print axioms continuing_motion_release_indistinguishable
#print axioms released_contact_unobserved
#print axioms first_law_held_diamond

end Audit

end Holonics.HNN.CarriedMotion
