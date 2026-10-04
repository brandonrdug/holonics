import Holonics.HNN.Retention

/-!
# HNN.CarriedStanding: the field's standing with the carried change and deposits between words

[definition] #62, owed by the reception carry as the production default (#310): the standing law
over a resident that holds the carried change, with deposits between the words. `Retention.Resident`
has no wave field, and `Retention.continuing_release_indistinguishable` is proved at one fixed
constitution over the chain of words. This file joins them: the resident holds the carried change,
the words open on it, a refine writes it, a compare stages its deposit between words, and the
retention is the continuing collapse (`Diamond::continuing`, `Opens::OnMotion`), the collapse at
`e_last = 2 |B|`, which keeps every edge a walk from a source to a receiver passes
(`inDiamond_continuing_iff`).

The model is the Rust as #310 landed (`90cae05a`; `hnn/reference.rs`, `hnn/word.rs`,
`hnn/pending.rs`):

* `Resident.carried : Option<ReceptionCarry>` is `CarriedResident.carried : Carry`: the change at
  the last word's end (`EndChange`), the references it was read at (the contacts' conductances and
  momenta, read here as the diagonal loci `θ b b` of the cut) and the lift it ended on. The rest
  opening (no carry) is the carry with zero change, on which every crossing is zero.
* `ReceptionCarry::opening` is `opening`: the moment's open state plus the carried change crossed
  into the contemporary references, `cross` (per contact `transmitted`, `held_rate`; per resonator
  `held_resonator_rate`; `interior_of` zeroes every source ring's storage). Each is local to its own
  block and linear in the change.
* `Word::reception_end` followed by `ReceptionCarry::absorbed` is `endCarry`: the word's end
  change, through the declared absorption (`Nothing` the identity, `Complete` zero), with the
  references of the constitution it ran at.
* The pending ratios are one chain in refine order (`Reference::refine`, the reception carry §8,
  atlas `hnn.pending-chain`). Refine opens its word on the carried change, stores that carry
  (`PendingSlot.opening`) and writes the carry to the end its word reaches (`resident.carried =
  ended`), whether or not earlier ratios are still pending. Compare reads the `i`-th pending word on
  its stored carry at the contemporary constitution (the kept read while the constitution is the
  one it was read at) and stages its deposit (`compose`, `StagedSlot.deposit`); discard drops a
  pending ratio (`discard(Handle::Pending)`); neither moves the carry. The Rust's
  `pending_capacity` bounds the chain; the law holds at any length. A staged deposit is committed
  by a later generator
  (`Reference::deposit`, `Constitution::deposited`), which applies it to the loci then current
  (`applyStaged`, equal to `Retention.deposit` at the staging loci by `deposit_eq_applyStaged`), or
  dropped (`discard(Handle::Staged)`).
* The deposit's windows are seeded at the sources and the support of the opening's interior
  (`Diamond::opened`).
* The collapse keeps the carry whole (`ContinuingState` saves it whole). The Rust's `close_aeon`
  also releases the carried motion on the loci it releases (`ReceptionCarry::released`,
  `WordOpening::released`; atlas `hnn.carried-motion-released`); the third model limit below.

[proved-derived; formal-checked] **The standing** (`carriedStanding`). The continuing collapse is a
`Foundation/Standing.StandingLaw` for this resident: every admitted future face, of the current word
and of every pending ratio, after any word of ingests, re-keyings, refines, compares, discards, and
commits and discards of staged deposits, is read off the collapsed resident. The collapse does not
commute with the generators (a deposit after it moves only retained loci, and the carry it ends on
is read at the collapsed constitution), so the law is proved through the agreement it does keep
(`Agree`): the loci and the staged data agree on every walk edge, each carry agrees on every block
that observes a receiver and its references agree on every block also reached from a source. Every
generator keeps the agreement (`step_agree`): a carried change stays on the blocks reached from the
sources and agrees wherever a receiver is observed (`Retention.trajectory_agrees_on_walk`); the
deposit's data on a walk edge agree, the features because its source block observes a receiver and
the swept covectors because its target is reached from a source (`sweep_agrees_on_walk`, on the
reversed graph); its windows agree because every seed that reaches an observing block observes a
receiver (`windowTicks_agree`). Every face respects it (`observe_agree`).

[definition; agent-inferred] **Model limits, read against the Rust at #310.**
1. *Compare and commit.* They are separate generators here, as in the Rust: compare stages, a later
   `deposit i` commits, `discardStaged i` drops. No limit remains. The commits between two refines
   act on the loci; their composition at held momentum (#62 5975646405 item 2, `ChainedBalance`'s
   `dep k`) is not stated here.
2. *The word is time-invariant at its class* (`readOp op (cls λ)` at every tick). The Rust violates
   this on every ring with a declared, pumped resonator: `Word::tick` runs that ring's element at
   the pump's phase at each tick (`operands.resonators()[ring]`, `Resonance`), on the refinement's
   clock, which continues across a continuing word's boundary. The phase moves only the element
   edge `g → g` (`Locus::Resonator(g)` is retained by the element's rule), so every tick's
   operators agree on the same walk edges; the time-indexed family's laws
   (`trajectory_agrees_on_walk` for a tick-indexed operator family, and the word read from its
   opening phase) are owed in #62. Unpumped rings are time-invariant. The executed tick's carried
   remainders are a separate matter: the exact law is linear, the lattice outputs are not
   (`HNN/Word` item 7).
3. *The motion release.* `retain` keeps the carry whole. The Rust's `close_aeon` also zeroes the
   carried motion on every channel and resonator it releases: the state and momentum, and a
   resonator's phase (record B §8). The released loci lie off every walk from a source to a
   receiver. The release of the carried open state is owed in #62.

The readings carry no epoch bound, since the continuing collapse reads every epoch. That the
crossing at a block reads only that block's loci is the type of `cross`; which of the medium's
operands each block edge reads is `HNN/LocusMap`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.CarriedStanding

open Holonics.HNN.Propagation Holonics.HNN.Retention

section Flip

variable {B : Type*} {adj : B → B → Prop}

theorem reachAll_flip {R : Set B} {b : B} : b ∈ reachAll (flip adj) R ↔ ObservesAll adj R b := by
  constructor
  · rintro ⟨t, x, hx, n, hn, hr⟩
    exact ⟨n, x, hx, n, le_rfl, reachIn_flip_iff.mp hr⟩
  · rintro ⟨m, ρ, hρ, n, hn, hr⟩
    exact ⟨n, ρ, hρ, n, le_rfl, reachIn_flip_iff.mpr hr⟩

theorem observesAll_flip {S : Set B} {b : B} : ObservesAll (flip adj) S b ↔ b ∈ reachAll adj S := by
  constructor
  · rintro ⟨m, ρ, hρ, n, hn, hr⟩
    exact ⟨n, ρ, hρ, n, le_rfl, reachIn_flip_iff.mp hr⟩
  · rintro ⟨t, x, hx, n, hn, hr⟩
    exact ⟨n, x, hx, n, le_rfl, reachIn_flip_iff.mpr hr⟩

/-- A block that reaches a block observing a receiver observes a receiver. -/
theorem observesAll_of_reachIn {R : Set B} {x z : B} {n : ℕ} (hr : ReachIn adj x z n)
    (hz : ObservesAll adj R z) : ObservesAll adj R x := by
  obtain ⟨m, hm⟩ := hz
  exact ⟨_, observes_trans ⟨n, le_rfl, hr⟩ hm⟩

end Flip

section Lists

variable {α β : Type*} {r : α → β → Prop}

theorem forall₂_getElem? {l : List α} {l' : List β} (h : List.Forall₂ r l l') (i : ℕ) :
    Option.Rel r l[i]? l'[i]? := by
  induction h generalizing i with
  | nil => exact .none
  | cons hab _ ih =>
    cases i with
    | zero => exact .some hab
    | succ i => exact ih i

theorem forall₂_eraseIdx {l : List α} {l' : List β} (h : List.Forall₂ r l l') (i : ℕ) :
    List.Forall₂ r (l.eraseIdx i) (l'.eraseIdx i) := by
  induction h generalizing i with
  | nil => exact .nil
  | cons hab htl ih =>
    cases i with
    | zero => exact htl
    | succ i => exact .cons hab (ih i)

theorem forall₂_self {s : α → α → Prop} (hs : ∀ a, s a a) (l : List α) : List.Forall₂ s l l := by
  induction l with
  | nil => exact .nil
  | cons a l ih => exact .cons (hs a) ih

end Lists

section Walk

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]

/-- [proved-derived; formal-checked] **The swept covectors agree on the reached blocks.** If two
sparse ticks agree on every walk edge from `S` to `R`, a covector supported on the receivers `R`
swept back any number of ticks agrees on every block reached from `S`: the walk diamond on the
reversed graph, from `R` to `S`. -/
theorem sweep_agrees_on_walk {T T' : BlockOp K M} (hT : Sparse adj T) (hT' : Sparse adj T')
    {S R : Set B} (hagree : ∀ y z, OnWalk adj S R z y → T y z = T' y z)
    {g : (b : B) → Module.Dual K (M b)} (hg : SupportedIn g R) (n : ℕ) {y : B}
    (hy : y ∈ reachAll adj S) : sweep T g n y = sweep T' g n y := by
  have hg' : SupportedIn g (reachAll (flip adj) R) := fun b hb =>
    hg b fun hbR => hb (subset_reachAll (adj := flip adj) R hbR)
  have hagree' : ∀ y z, OnWalk (flip adj) R S z y → dualOp T y z = dualOp T' y z := by
    rintro y z ⟨hz, hy⟩
    simp only [dualOp]
    rw [hagree z y ⟨observesAll_flip.mp hy, reachAll_flip.mp hz⟩]
  exact (trajectory_agrees_on_walk (adj := flip adj) (sparse_dualOp hT) (sparse_dualOp hT')
    hagree' hg' hg' (fun _ _ => rfl) n).2.2 y (observesAll_flip.mpr hy)

omit [Fintype B] in
open Classical in
/-- [proved-derived; formal-checked] **The windows of an observing edge agree** when the seeds
agree on every block that observes a receiver: a seed whose walk reaches the edge's source block
observes the receiver the edge does. -/
theorem windowTicks_agree {R sd sd' : Set B}
    (hsd : ∀ s, ObservesAll adj R s → (s ∈ sd ↔ s ∈ sd')) {z : B} (hz : ObservesAll adj R z)
    (t : ℕ) (y : B) : windowTicks adj sd R t z y = windowTicks adj sd' R t z y := by
  have hreach : ∀ k, z ∈ reachWithin adj sd k ↔ z ∈ reachWithin adj sd' k := fun k => by
    constructor
    · rintro ⟨x, hx, n, hn, hr⟩
      exact ⟨x, (hsd x (observesAll_of_reachIn hr hz)).mp hx, n, hn, hr⟩
    · rintro ⟨x, hx, n, hn, hr⟩
      exact ⟨x, (hsd x (observesAll_of_reachIn hr hz)).mpr hx, n, hn, hr⟩
  simp only [windowTicks, hreach]

variable {Cls : Type*} {Θ : B → B → Type*} {op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y)}

/-- [proved-derived; formal-checked] **A deposit's data agree on every walk edge.** For two
constitutions that agree on every walk edge from `S` to `R`, open states supported on the reached
blocks and agreeing on the observing ones, windows seeded at sets that agree on the observing blocks
and readings supported on `R`, the data a deposit reads on a declared walk edge agree: the features
because its source block observes a receiver, the swept covectors because its target is reached
from a source, and the windows because every seed that reaches the edge observes a receiver. -/
theorem depositData_agree {θ θ' : (y z : B) → Θ y z} (hθ : LociSparse adj op θ)
    (hθ' : LociSparse adj op θ') {S R sd sd' : Set B}
    (hL : ∀ y z, OnWalk adj S R z y → θ y z = θ' y z)
    (hsd : ∀ s, ObservesAll adj R s → (s ∈ sd ↔ s ∈ sd')) (c : Cls) {x₀ x₀' : (b : B) → M b}
    (hx : SupportedIn x₀ (reachAll adj S)) (hx' : SupportedIn x₀' (reachAll adj S))
    (hxx : ∀ b, ObservesAll adj R b → x₀ b = x₀' b)
    {rd : List (ℕ × ((b : B) → Module.Dual K (M b)))} (hrd : ∀ r ∈ rd, SupportedIn r.2 R)
    {y z : B} (hw : OnWalk adj S R z y) (hadj : adj z y) :
    depositData adj (readOp op c θ) x₀ sd R rd z y =
      depositData adj (readOp op c θ') x₀' sd' R rd z y := by
  have hT := sparse_readOp hθ c
  have hT' := sparse_readOp hθ' c
  have hagree : ∀ y z, OnWalk adj S R z y → readOp op c θ y z = readOp op c θ' y z :=
    fun y z h => by simp only [readOp, hL y z h]
  have hz : ObservesAll adj R z := observesAll_step hadj hw.2
  have hy : y ∈ reachAll adj S := reachAll_step hw.1 hadj
  rw [depositData, depositData]
  refine List.flatMap_congr fun r hr => ?_
  rw [windowTicks_agree hsd hz]
  refine List.map_congr_left fun k _ => Prod.ext ?_ ?_
  · exact (trajectory_agrees_on_walk hT hT' hagree hx hx' hxx k).2.2 z hz
  · exact sweep_agrees_on_walk hT hT' hagree (hrd r hr) _ hy

variable (adj) in
open Classical in
/-- [definition] **A staged deposit committed** (`Reference::deposit`,
`Constitution::deposited`): on each declared edge the locus law `Φ` reads the locus as it stands at
the commit and the data the deposit staged for that edge; nothing else changes. -/
def applyStaged (Φ : (y z : B) → Θ y z → List (M z × Module.Dual K (M y)) → Θ y z)
    (d : (y z : B) → List (M z × Module.Dual K (M y))) (θ : (y z : B) → Θ y z) :
    (y z : B) → Θ y z :=
  fun y z => if adj z y then Φ y z (θ y z) (d y z) else θ y z

/-- [proved-derived; formal-checked] A deposit is its data staged and committed at once. -/
theorem deposit_eq_applyStaged (Φ : (y z : B) → Θ y z → List (M z × Module.Dual K (M y)) → Θ y z)
    (S R : Set B) (c : Cls) (x₀ : (b : B) → M b)
    (rd : List (ℕ × ((b : B) → Module.Dual K (M b)))) (θ : (y z : B) → Θ y z) :
    deposit adj op Φ S R c x₀ rd θ =
      applyStaged adj Φ (fun y z => depositData adj (readOp op c θ) x₀ S R rd z y) θ := rfl

omit [Fintype B] in
/-- [proved-derived; formal-checked] A committed deposit agrees on every walk edge when the loci
and the staged data agree there. -/
theorem applyStaged_agree (Φ : (y z : B) → Θ y z → List (M z × Module.Dual K (M y)) → Θ y z)
    {S R : Set B} {d d' : (y z : B) → List (M z × Module.Dual K (M y))}
    (hd : ∀ y z, OnWalk adj S R z y → adj z y → d y z = d' y z) {θ θ' : (y z : B) → Θ y z}
    (hL : ∀ y z, OnWalk adj S R z y → θ y z = θ' y z) {y z : B} (hw : OnWalk adj S R z y) :
    applyStaged adj Φ d θ y z = applyStaged adj Φ d' θ' y z := by
  classical
  simp only [applyStaged]
  split_ifs with hadj
  · rw [hL y z hw, hd y z hw hadj]
  · exact hL y z hw

/-- [proved-derived; formal-checked] **A deposit agrees on every walk edge.** Two constitutions
that agree on every walk edge from `S` to `R`, deposited from open states supported on the reached
blocks and agreeing on the observing ones, with windows seeded at sets that agree on the observing
blocks and readings supported on `R`, agree after the deposit on every walk edge. -/
theorem deposit_agree (Φ : (y z : B) → Θ y z → List (M z × Module.Dual K (M y)) → Θ y z)
    {θ θ' : (y z : B) → Θ y z} (hθ : LociSparse adj op θ) (hθ' : LociSparse adj op θ')
    {S R sd sd' : Set B} (hL : ∀ y z, OnWalk adj S R z y → θ y z = θ' y z)
    (hsd : ∀ s, ObservesAll adj R s → (s ∈ sd ↔ s ∈ sd')) (c : Cls) {x₀ x₀' : (b : B) → M b}
    (hx : SupportedIn x₀ (reachAll adj S)) (hx' : SupportedIn x₀' (reachAll adj S))
    (hxx : ∀ b, ObservesAll adj R b → x₀ b = x₀' b)
    {rd : List (ℕ × ((b : B) → Module.Dual K (M b)))} (hrd : ∀ r ∈ rd, SupportedIn r.2 R)
    {y z : B} (hw : OnWalk adj S R z y) :
    deposit adj op Φ sd R c x₀ rd θ y z = deposit adj op Φ sd' R c x₀' rd θ' y z := by
  rw [deposit_eq_applyStaged, deposit_eq_applyStaged]
  exact applyStaged_agree Φ (fun y z hw hadj =>
    depositData_agree hθ hθ' hL hsd c hx hx' hxx hrd hw hadj) hL hw

end Walk

/-! ## The resident with the carried change -/

section Objects

variable {B : Type*}

/-- [definition] **The carry** (`ReceptionCarry`): the change at the last word's end, the
references it was read at (each block's own locus at that cut) and the lift it ended on. -/
structure Carry (M : B → Type*) (Θ : B → B → Type*) (Λ : Type*) where
  change : (b : B) → M b
  ref : (b : B) → Θ b b
  lift : Λ

/-- [definition] **A pending ratio under the carry** (`PendingSlot`): its producing anchor and the
carry its word opened on (`PendingSlot.opening`). -/
structure Pend (M : B → Type*) (Θ : B → B → Type*) (Λ Mo : Type*) where
  lift : Λ
  moment : Mo
  opening : Carry M Θ Λ

/-- [definition] **The resident field with the carried change**: the constitution's loci, the
lift point, the open moment, the carried change, the pending ratios of the chain in refine order,
and the staged deposits (`Resident.staged`), each the data it staged on every edge. -/
structure CarriedResident (K : Type*) [Field K] (M : B → Type*) [∀ b, AddCommGroup (M b)]
    [∀ b, Module K (M b)] (Θ : B → B → Type*) (Λ Mo : Type*) where
  loci : (y z : B) → Θ y z
  lift : Λ
  moment : Mo
  carried : Carry M Θ Λ
  pending : List (Pend M Θ Λ Mo)
  staged : List ((y z : B) → List (M z × Module.Dual K (M y)))

/-- [definition] **The carry law**: the block operators, the class read at a lift, the moment's
open state, the word's ticks, the crossing of a carried change into the contemporary references
(local to each block, linear in the change), the absorption at a word's end, the ingest and
re-keying of the lift and moment, and the locus law of the deposit. -/
structure CarryLaw (K : Type*) [Field K] (M : B → Type*) [∀ b, AddCommGroup (M b)]
    [∀ b, Module K (M b)] (Θ : B → B → Type*) (Cls Λ Mo Cell Crib : Type*) where
  op : Cls → (y z : B) → Θ y z → (M z →ₗ[K] M y)
  cls : Λ → Cls
  openState : Λ → Mo → (b : B) → M b
  ticks : Λ → Mo → ℕ
  cross : Λ → Λ → (b : B) → Θ b b → Θ b b → (M b →ₗ[K] M b)
  absorb : (b : B) → M b →ₗ[K] M b
  ingestStep : Cell → Λ × Mo → Λ × Mo
  rekey : Crib → Λ → Λ
  Φ : (y z : B) → Θ y z → List (M z × Module.Dual K (M y)) → Θ y z

/-- [definition] The generators under the carry: ingest a source cell, locate keys (re-keying),
refine, compare the `i`-th pending ratio (staging its deposit), discard the `i`-th pending ratio,
commit a staged deposit, and discard a staged deposit. -/
inductive CarryGen (Cell Crib RD : Type*)
  | ingest (x : Cell)
  | locateKeys (crib : Crib)
  | refine
  | compare (i : ℕ) (rd : RD)
  | discard (i : ℕ)
  | deposit (i : ℕ)
  | discardStaged (i : ℕ)

end Objects

section Resident

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
variable {Cls Λ Mo Cell Crib : Type*} {Θ : B → B → Type*}

variable (L : CarryLaw K M Θ Cls Λ Mo Cell Crib)

/-- [definition] **The opening's interior** (`ReceptionCarry::opening`): the carried change
crossed into the references of the constitution `θ` at the lift `l`. -/
def interior (θ : (y z : B) → Θ y z) (l : Λ) (c : Carry M Θ Λ) : (b : B) → M b :=
  fun b => L.cross c.lift l b (c.ref b) (θ b b) (c.change b)

/-- [definition] **The word's opening** (`Word::open_received`): the moment's open state plus the
opening's interior. -/
def opening (θ : (y z : B) → Θ y z) (l : Λ) (m : Mo) (c : Carry M Θ Λ) : (b : B) → M b :=
  L.openState l m + interior L θ l c

/-- [definition] **The deposit's seeds** (`Diamond::opened`): the sources and the support of the
opening's interior. -/
def seeds (S : Set B) (θ : (y z : B) → Θ y z) (l : Λ) (c : Carry M Θ Λ) : Set B :=
  S ∪ {b | interior L θ l c b ≠ 0}

/-- [definition] **The carry at a word's end** (`Word::reception_end`, `ReceptionCarry::absorbed`):
the change the word opened on `c` reaches after its ticks, through the absorption, with the
references of the constitution it ran at. -/
def endCarry (θ : (y z : B) → Θ y z) (l : Λ) (m : Mo) (c : Carry M Θ Λ) : Carry M Θ Λ where
  change b := L.absorb b (trajectory (readOp L.op (L.cls l) θ) (opening L θ l m c) (L.ticks l m) b)
  ref b := θ b b
  lift := l

variable (adj) in
/-- [definition] **The data a compare stages** (`compose`, `StagedSlot.deposit`): on every edge,
what the pending word opened on its stored carry at the constitution `θ` reads there, in the windows
seeded at the sources and the opening's interior. -/
def stagedOf (S R : Set B) (θ : (y z : B) → Θ y z) (p : Pend M Θ Λ Mo)
    (rd : List (ℕ × ((b : B) → Module.Dual K (M b)))) :
    (y z : B) → List (M z × Module.Dual K (M y)) :=
  fun y z => depositData adj (readOp L.op (L.cls p.lift) θ) (opening L θ p.lift p.moment p.opening)
    (seeds L S θ p.lift p.opening) R rd z y

/-- [definition] The admitted readings under the continuing collapse: any epoch, a covector
supported on the receivers. -/
def ReceiverReading (K : Type*) [Field K] (M : B → Type*) [∀ b, AddCommGroup (M b)]
    [∀ b, Module K (M b)] (R : Set B) :=
  {r : ℕ × ((b : B) → Module.Dual K (M b)) // SupportedIn r.2 R}

/-- [definition] The admitted families of readings, the payload of a compare's deposit. -/
def ReceiverFamily (K : Type*) [Field K] (M : B → Type*) [∀ b, AddCommGroup (M b)]
    [∀ b, Module K (M b)] (R : Set B) :=
  {rd : List (ℕ × ((b : B) → Module.Dual K (M b))) // ∀ r ∈ rd, SupportedIn r.2 R}

variable (adj) in
/-- [definition] **The generators acting on the resident** (one chain in refine order). Refine
opens a pending ratio on the carried change, stores that carry and writes the carry to the end its
word reaches; compare reads the `i`-th pending word on its stored carry at the contemporary
constitution and stages the data its deposit reads; discard drops the `i`-th pending ratio; neither
moves the carry. A deposit commits a staged deposit on the constitution as it then stands, and a
staged deposit may be discarded. A compare or discard of no pending ratio and a commit of no staged
deposit leave the resident unchanged (the Rust refuses them). -/
def step (S R : Set B) :
    CarryGen Cell Crib (ReceiverFamily K M R) →
      CarriedResident K M Θ Λ Mo → CarriedResident K M Θ Λ Mo
  | .ingest x, res =>
    { res with lift := (L.ingestStep x (res.lift, res.moment)).1,
               moment := (L.ingestStep x (res.lift, res.moment)).2 }
  | .locateKeys crib, res => { res with lift := L.rekey crib res.lift }
  | .refine, res =>
    { res with carried := endCarry L res.loci res.lift res.moment res.carried,
               pending := res.pending ++ [⟨res.lift, res.moment, res.carried⟩] }
  | .compare i rd, res =>
    match res.pending[i]? with
    | none => res
    | some p =>
      { res with
        pending := res.pending.eraseIdx i
        staged := res.staged ++ [stagedOf adj L S R res.loci p rd.1] }
  | .discard i, res => { res with pending := res.pending.eraseIdx i }
  | .deposit i, res =>
    match res.staged[i]? with
    | none => res
    | some d => { res with loci := applyStaged adj L.Φ d res.loci, staged := res.staged.eraseIdx i }
  | .discardStaged i, res => { res with staged := res.staged.eraseIdx i }

/-- [definition] A word's admitted reading opened on a carry, at the constitution `θ`. -/
def wordRead {R : Set B} (θ : (y z : B) → Θ y z) (l : Λ) (m : Mo) (c : Carry M Θ Λ)
    (r : ReceiverReading K M R) : K :=
  pair r.1.2 (trajectory (readOp L.op (L.cls l) θ) (opening L θ l m c) r.1.1)

/-- [definition] **The faces**: the current word opened on the carried change (`none`) and the
`i`-th pending word on its stored carry (`some i`), each at the contemporary constitution. -/
def observe {R : Set B} : Option ℕ × ReceiverReading K M R → CarriedResident K M Θ Λ Mo → K
  | (none, r), res => wordRead L res.loci res.lift res.moment res.carried r
  | (some i, r), res =>
    match res.pending[i]? with
    | none => 0
    | some p => wordRead L res.loci p.lift p.moment p.opening r

variable (adj) in
/-- [definition] **The retention**: the continuing collapse of the constitution; the lift point,
the moment, the carried change and the pending ratio are kept whole. -/
def retain (rel : (y z : B) → Θ y z) (S R : Set B) (res : CarriedResident K M Θ Λ Mo) :
    CarriedResident K M Θ Λ Mo :=
  { res with loci := collapse adj rel S R (2 * Fintype.card B) res.loci }

variable (adj) in
/-- [definition] **The valid residents**: loci inside the declared graph, and every carry's change
on the blocks reached from the sources. -/
def Valid (S : Set B) (res : CarriedResident K M Θ Λ Mo) : Prop :=
  LociSparse adj L.op res.loci ∧ SupportedIn res.carried.change (reachAll adj S) ∧
    ∀ p ∈ res.pending, SupportedIn p.opening.change (reachAll adj S)

/-! ### The agreement the generators keep -/

variable (adj) in
/-- [definition] Two carries agree on the observing blocks: equal lifts, changes equal on every
block that observes a receiver, references equal on every such block reached from a source. -/
def CarryAgree (S R : Set B) (c c' : Carry M Θ Λ) : Prop :=
  c.lift = c'.lift ∧ (∀ b, b ∈ reachAll adj S → ObservesAll adj R b → c.ref b = c'.ref b) ∧
    ∀ b, ObservesAll adj R b → c.change b = c'.change b

variable (adj) in
/-- [definition] Two pending ratios agree: equal anchors and agreeing carries. -/
def PendAgree (S R : Set B) (p p' : Pend M Θ Λ Mo) : Prop :=
  p.lift = p'.lift ∧ p.moment = p'.moment ∧ CarryAgree adj S R p.opening p'.opening

variable (adj) in
/-- [definition] Two staged deposits agree on every declared walk edge. -/
def StagedAgree (S R : Set B) (d d' : (y z : B) → List (M z × Module.Dual K (M y))) : Prop :=
  ∀ y z, OnWalk adj S R z y → adj z y → d y z = d' y z

variable (adj) in
/-- [definition] **The agreement**: loci equal on every walk edge, equal lift and moment, agreeing
carries, agreeing pending ratios and agreeing staged deposits. -/
def Agree (S R : Set B) (res res' : CarriedResident K M Θ Λ Mo) : Prop :=
  (∀ y z, OnWalk adj S R z y → res.loci y z = res'.loci y z) ∧ res.lift = res'.lift ∧
    res.moment = res'.moment ∧ CarryAgree adj S R res.carried res'.carried ∧
    List.Forall₂ (PendAgree adj S R) res.pending res'.pending ∧
    List.Forall₂ (StagedAgree adj S R) res.staged res'.staged

omit [Fintype B] [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)] in
theorem carryAgree_refl {S R : Set B} (c : Carry M Θ Λ) : CarryAgree adj S R c c :=
  ⟨rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

variable {L}

omit [Fintype B] in
theorem interior_supported {S : Set B} {θ : (y z : B) → Θ y z} {l : Λ} {c : Carry M Θ Λ}
    (hc : SupportedIn c.change (reachAll adj S)) :
    SupportedIn (interior L θ l c) (reachAll adj S) := fun b hb => by
  simp [interior, hc b hb]

omit [Fintype B] in
theorem opening_supported {S : Set B} (hopen : ∀ l m, SupportedIn (L.openState l m) S)
    {θ : (y z : B) → Θ y z} {l : Λ} {m : Mo} {c : Carry M Θ Λ}
    (hc : SupportedIn c.change (reachAll adj S)) :
    SupportedIn (opening L θ l m c) (reachAll adj S) := fun b hb => by
  simp [opening, hopen l m b fun hbS => hb (subset_reachAll S hbS),
    interior_supported (L := L) (θ := θ) (l := l) hc b hb]

omit [Fintype B] in
theorem interior_agree {S R : Set B} {θ θ' : (y z : B) → Θ y z}
    (hL : ∀ y z, OnWalk adj S R z y → θ y z = θ' y z) (l : Λ) {c c' : Carry M Θ Λ}
    (hc : SupportedIn c.change (reachAll adj S)) (hc' : SupportedIn c'.change (reachAll adj S))
    (hcc : CarryAgree adj S R c c') {b : B} (hb : ObservesAll adj R b) :
    interior L θ l c b = interior L θ' l c' b := by
  by_cases hr : b ∈ reachAll adj S
  · simp only [interior]
    rw [hcc.1, hcc.2.1 b hr hb, hL b b ⟨hr, hb⟩, hcc.2.2 b hb]
  · simp [interior, hc b hr, hc' b hr]

omit [Fintype B] in
theorem opening_agree {S R : Set B} {θ θ' : (y z : B) → Θ y z}
    (hL : ∀ y z, OnWalk adj S R z y → θ y z = θ' y z) (l : Λ) (m : Mo) {c c' : Carry M Θ Λ}
    (hc : SupportedIn c.change (reachAll adj S)) (hc' : SupportedIn c'.change (reachAll adj S))
    (hcc : CarryAgree adj S R c c') {b : B} (hb : ObservesAll adj R b) :
    opening L θ l m c b = opening L θ' l m c' b := by
  simp only [opening, Pi.add_apply, interior_agree hL l hc hc' hcc hb]

theorem endCarry_supported {S : Set B} (hopen : ∀ l m, SupportedIn (L.openState l m) S)
    {θ : (y z : B) → Θ y z} (hθ : LociSparse adj L.op θ) (l : Λ) (m : Mo) {c : Carry M Θ Λ}
    (hc : SupportedIn c.change (reachAll adj S)) :
    SupportedIn (endCarry L θ l m c).change (reachAll adj S) := fun b hb => by
  have hx := opening_supported (L := L) (θ := θ) (l := l) (m := m) hopen hc
  have h := (trajectory_agrees_on_walk (R := (∅ : Set B)) (sparse_readOp hθ (L.cls l))
    (sparse_readOp hθ (L.cls l)) (fun _ _ _ => rfl) hx hx (fun _ _ => rfl) (L.ticks l m)).1
  simp only [endCarry, h b hb, map_zero]

theorem endCarry_agree {S R : Set B} (hopen : ∀ l m, SupportedIn (L.openState l m) S)
    {θ θ' : (y z : B) → Θ y z} (hθ : LociSparse adj L.op θ) (hθ' : LociSparse adj L.op θ')
    (hL : ∀ y z, OnWalk adj S R z y → θ y z = θ' y z) (l : Λ) (m : Mo) {c c' : Carry M Θ Λ}
    (hc : SupportedIn c.change (reachAll adj S)) (hc' : SupportedIn c'.change (reachAll adj S))
    (hcc : CarryAgree adj S R c c') :
    CarryAgree adj S R (endCarry L θ l m c) (endCarry L θ' l m c') := by
  refine ⟨rfl, fun b hr hb => hL b b ⟨hr, hb⟩, fun b hb => ?_⟩
  have h := trajectory_agrees_on_walk (sparse_readOp hθ (L.cls l)) (sparse_readOp hθ' (L.cls l))
    (fun y z hw => by simp only [readOp, hL y z hw]) (opening_supported hopen hc)
    (opening_supported hopen hc') (fun b hb => opening_agree hL l m hc hc' hcc hb) (L.ticks l m)
  simp only [endCarry, h.2.2 b hb]

omit [Fintype B] in
theorem seeds_agree {S R : Set B} {θ θ' : (y z : B) → Θ y z}
    (hL : ∀ y z, OnWalk adj S R z y → θ y z = θ' y z) (l : Λ) {c c' : Carry M Θ Λ}
    (hc : SupportedIn c.change (reachAll adj S)) (hc' : SupportedIn c'.change (reachAll adj S))
    (hcc : CarryAgree adj S R c c') (s : B) (hs : ObservesAll adj R s) :
    s ∈ seeds L S θ l c ↔ s ∈ seeds L S θ' l c' := by
  simp only [seeds, Set.mem_union, Set.mem_ofPred_eq, interior_agree hL l hc hc' hcc hs]

/-! ### Validity, agreement with the collapse, and the generators -/

theorem step_valid {S R : Set B} (hopen : ∀ l m, SupportedIn (L.openState l m) S)
    (g : CarryGen Cell Crib (ReceiverFamily K M R)) {res : CarriedResident K M Θ Λ Mo}
    (hv : Valid adj L S res) : Valid adj L S (step adj L S R g res) := by
  obtain ⟨θ, l, m, c, P, D⟩ := res
  obtain ⟨hθ, hc, hP⟩ := hv
  cases g with
  | ingest x => exact ⟨hθ, hc, hP⟩
  | locateKeys crib => exact ⟨hθ, hc, hP⟩
  | refine =>
    refine ⟨hθ, endCarry_supported hopen hθ l m hc, fun p hp => ?_⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hP p hp
    · rw [List.mem_singleton.mp hp]
      exact hc
  | compare i rd =>
    simp only [step]
    cases P[i]? with
    | none => exact ⟨hθ, hc, hP⟩
    | some p => exact ⟨hθ, hc, fun q hq => hP q (List.mem_of_mem_eraseIdx hq)⟩
  | discard i => exact ⟨hθ, hc, fun q hq => hP q (List.mem_of_mem_eraseIdx hq)⟩
  | deposit i =>
    simp only [step]
    cases D[i]? with
    | none => exact ⟨hθ, hc, hP⟩
    | some d =>
      refine ⟨fun c y z h => ?_, hc, hP⟩
      classical
      simp only [applyStaged, if_neg h]
      exact hθ c y z h
  | discardStaged i => exact ⟨hθ, hc, hP⟩

theorem step_agree {S R : Set B} (hopen : ∀ l m, SupportedIn (L.openState l m) S)
    (g : CarryGen Cell Crib (ReceiverFamily K M R)) {res res' : CarriedResident K M Θ Λ Mo}
    (hv : Valid adj L S res) (hv' : Valid adj L S res') (h : Agree adj S R res res') :
    Agree adj S R (step adj L S R g res) (step adj L S R g res') := by
  obtain ⟨θ, l, m, c, P, D⟩ := res
  obtain ⟨θ', l', m', c', P', D'⟩ := res'
  obtain ⟨hθ, hc, hP⟩ := hv
  obtain ⟨hθ', hc', hP'⟩ := hv'
  obtain ⟨hL, hl, hm, hcc, hPP, hDD⟩ := h
  simp only at hl hm
  subst hl hm
  cases g with
  | ingest x => exact ⟨hL, rfl, rfl, hcc, hPP, hDD⟩
  | locateKeys crib => exact ⟨hL, rfl, rfl, hcc, hPP, hDD⟩
  | refine =>
    exact ⟨hL, rfl, rfl, endCarry_agree hopen hθ hθ' hL l m hc hc' hcc,
      List.rel_append hPP (.cons ⟨rfl, rfl, hcc⟩ .nil), hDD⟩
  | compare i rd =>
    have hi := forall₂_getElem? hPP i
    simp only [step]
    cases hpi : P[i]? with
    | none =>
      rw [hpi] at hi
      cases hpi' : P'[i]? with
      | none => exact ⟨hL, rfl, rfl, hcc, hPP, hDD⟩
      | some p' =>
        rw [hpi'] at hi
        cases hi
    | some p =>
      rw [hpi] at hi
      cases hpi' : P'[i]? with
      | none =>
        rw [hpi'] at hi
        cases hi
      | some p' =>
        rw [hpi'] at hi
        obtain ⟨hpl, hpm, hpo⟩ := Option.rel_some_some.mp hi
        have hp := hP p (List.mem_of_getElem? hpi)
        have hp' := hP' p' (List.mem_of_getElem? hpi')
        have hnew : StagedAgree adj S R (stagedOf adj L S R θ p rd.1)
            (stagedOf adj L S R θ' p' rd.1) := fun y z hw hadj => by
          simp only [stagedOf]
          rw [← hpl, ← hpm]
          exact depositData_agree hθ hθ' hL (seeds_agree hL p.lift hp hp' hpo) _
            (opening_supported hopen hp) (opening_supported hopen hp')
            (fun b hb => opening_agree hL p.lift p.moment hp hp' hpo hb) rd.2 hw hadj
        exact ⟨hL, rfl, rfl, hcc, forall₂_eraseIdx hPP i, List.rel_append hDD (.cons hnew .nil)⟩
  | discard i => exact ⟨hL, rfl, rfl, hcc, forall₂_eraseIdx hPP i, hDD⟩
  | deposit i =>
    have hi := forall₂_getElem? hDD i
    simp only [step]
    generalize D[i]? = o at hi ⊢
    generalize D'[i]? = o' at hi ⊢
    cases hi with
    | none => exact ⟨hL, rfl, rfl, hcc, hPP, hDD⟩
    | some hdd =>
      exact ⟨fun y z hw => applyStaged_agree L.Φ hdd hL hw, rfl, rfl, hcc, hPP,
        forall₂_eraseIdx hDD i⟩
  | discardStaged i => exact ⟨hL, rfl, rfl, hcc, hPP, forall₂_eraseIdx hDD i⟩

theorem retain_valid {S R : Set B} {rel : (y z : B) → Θ y z}
    (hrel : ∀ c y z, L.op c y z (rel y z) = 0) {res : CarriedResident K M Θ Λ Mo}
    (hv : Valid adj L S res) : Valid adj L S (retain adj rel S R res) :=
  ⟨lociSparse_collapse hrel hv.1 S R _, hv.2.1, hv.2.2⟩

theorem agree_retain {S R : Set B} (rel : (y z : B) → Θ y z) (res : CarriedResident K M Θ Λ Mo) :
    Agree adj S R res (retain adj rel S R res) := by
  refine ⟨fun y z hw => ?_, rfl, rfl, carryAgree_refl _, ?_, ?_⟩
  · simp only [retain]
    rw [collapse_of_mem ((inDiamond_continuing_iff S R z y).mpr hw)]
  · exact forall₂_self (s := PendAgree adj S R) (fun _ => ⟨rfl, rfl, carryAgree_refl _⟩) _
  · exact forall₂_self (s := StagedAgree adj S R) (fun _ _ _ _ _ => rfl) res.staged

theorem wordRead_agree {S R : Set B} (hopen : ∀ l m, SupportedIn (L.openState l m) S)
    {θ θ' : (y z : B) → Θ y z} (hθ : LociSparse adj L.op θ) (hθ' : LociSparse adj L.op θ')
    (hL : ∀ y z, OnWalk adj S R z y → θ y z = θ' y z) (l : Λ) (m : Mo) {c c' : Carry M Θ Λ}
    (hc : SupportedIn c.change (reachAll adj S)) (hc' : SupportedIn c'.change (reachAll adj S))
    (hcc : CarryAgree adj S R c c') (r : ReceiverReading K M R) :
    wordRead L θ l m c r = wordRead L θ' l m c' r := by
  have h := trajectory_agrees_on_walk (sparse_readOp hθ (L.cls l)) (sparse_readOp hθ' (L.cls l))
    (fun y z hw => by simp only [readOp, hL y z hw]) (opening_supported hopen hc)
    (opening_supported hopen hc') (fun b hb => opening_agree hL l m hc hc' hcc hb) r.1.1
  exact pair_agrees_on_observers r.2 h.2.2

theorem observe_agree {S R : Set B} (hopen : ∀ l m, SupportedIn (L.openState l m) S)
    (q : Option ℕ × ReceiverReading K M R) {res res' : CarriedResident K M Θ Λ Mo}
    (hv : Valid adj L S res) (hv' : Valid adj L S res') (h : Agree adj S R res res') :
    observe L q res = observe L q res' := by
  obtain ⟨θ, l, m, c, P, D⟩ := res
  obtain ⟨θ', l', m', c', P', D'⟩ := res'
  obtain ⟨hθ, hc, hP⟩ := hv
  obtain ⟨hθ', hc', hP'⟩ := hv'
  obtain ⟨hL, hl, hm, hcc, hPP, -⟩ := h
  simp only at hl hm
  subst hl hm
  obtain ⟨o, r⟩ := q
  cases o with
  | none => exact wordRead_agree hopen hθ hθ' hL l m hc hc' hcc r
  | some i =>
    have hi := forall₂_getElem? hPP i
    simp only [observe]
    cases hpi : P[i]? with
    | none =>
      rw [hpi] at hi
      cases hpi' : P'[i]? with
      | none => rfl
      | some p' =>
        rw [hpi'] at hi
        cases hi
    | some p =>
      rw [hpi] at hi
      cases hpi' : P'[i]? with
      | none =>
        rw [hpi'] at hi
        cases hi
      | some p' =>
        rw [hpi'] at hi
        obtain ⟨hpl, hpm, hpo⟩ := Option.rel_some_some.mp hi
        simp only
        rw [← hpl, ← hpm]
        exact wordRead_agree hopen hθ hθ' hL _ _ (hP p (List.mem_of_getElem? hpi))
          (hP' p' (List.mem_of_getElem? hpi')) hpo r

/-! ### The standing -/

variable (adj L) in
/-- [definition] The valid residents, the standing law's sources. -/
def ValidResident (S : Set B) := {res : CarriedResident K M Θ Λ Mo // Valid adj L S res}

variable (adj L) in
/-- [definition] The generators on the valid residents. -/
def transport {S R : Set B} (hopen : ∀ l m, SupportedIn (L.openState l m) S)
    (g : CarryGen Cell Crib (ReceiverFamily K M R)) (s : ValidResident adj L S) :
    ValidResident adj L S :=
  ⟨step adj L S R g s.1, step_valid hopen g s.2⟩

theorem transportWord_agree {S R : Set B} (hopen : ∀ l m, SupportedIn (L.openState l m) S)
    (w : List (CarryGen Cell Crib (ReceiverFamily K M R))) {s s' : ValidResident adj L S}
    (h : Agree adj S R s.1 s'.1) :
    Agree adj S R (Holonics.Foundation.Chronology.transportWord (transport adj L hopen) w s).1
      (Holonics.Foundation.Chronology.transportWord (transport adj L hopen) w s').1 := by
  induction w with
  | nil => exact h
  | cons g w ih => exact step_agree hopen g (Subtype.property _) (Subtype.property _) ih

/-- [proved-derived; formal-checked] **The standing with the carried change** (#62; the reception
carry as the production default, #310). The resident `(Θ, λ, M, carried, pending)` with the
generators ingest, locate keys, refine, compare (staging its deposit), discard, and the commit or
discard of a staged deposit, observed through the admitted faces of the current word on the carried
change and of every pending word on its stored carry, at the contemporary constitution and any epoch, is a `Foundation/Standing.StandingLaw` whose
retention is the continuing collapse (`Diamond::continuing`), keeping the carry whole. -/
def carriedStanding {S R : Set B} {rel : (y z : B) → Θ y z}
    (hrel : ∀ c y z, L.op c y z (rel y z) = 0) (hopen : ∀ l m, SupportedIn (L.openState l m) S) :
    Holonics.Foundation.Standing.StandingLaw (CarryGen Cell Crib (ReceiverFamily K M R))
      (Option ℕ × ReceiverReading K M R) (ValidResident adj L S) (ValidResident adj L S) K where
  transport := transport adj L hopen
  observe q s := observe L q s.1
  retain s := ⟨retain adj rel S R s.1, retain_valid hrel s.2⟩
  reopen q w s := observe L q
    (Holonics.Foundation.Chronology.transportWord (transport adj L hopen) w s).1
  sufficient q w s :=
    (observe_agree hopen q (Subtype.property _) (Subtype.property _)
      (transportWord_agree (s := s) (s' := ⟨retain adj rel S R s.1, retain_valid hrel s.2⟩)
        hopen w (agree_retain rel s.1))).symm

end Resident

end Holonics.HNN.CarriedStanding

#print axioms Holonics.HNN.CarriedStanding.sweep_agrees_on_walk
#print axioms Holonics.HNN.CarriedStanding.windowTicks_agree
#print axioms Holonics.HNN.CarriedStanding.deposit_agree
#print axioms Holonics.HNN.CarriedStanding.step_agree
#print axioms Holonics.HNN.CarriedStanding.observe_agree
#print axioms Holonics.HNN.CarriedStanding.carriedStanding
