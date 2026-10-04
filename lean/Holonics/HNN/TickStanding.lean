import Holonics.HNN.TickFamily

/-!
# HNN.TickStanding: the standing with the carried change, a tick-indexed word and shared loci

[definition] #62 (5975321323, items 1 and 3; `HNN/CarriedStanding`, model limit 2). The resident
of `HNN/CarriedStanding` holds the carried change, and its words read one block operator at every
tick at a class read from the lift, on loci kept one per block edge. The Rust departs from that model
in two ways, and this file states the standing law with both:

* **The word is indexed by the tick.** On a ring with a pumped resonator the element runs at the
  pump's phase at each tick, on the field's elapsed clock, which continues across receptions
  (`hnn::word::Word::opened_at`, `ReceptionCarry`; the resident holds the carried change and its
  tick). Here a carry holds its tick `τ`, and the word opened on it runs the family
  `k ↦ op (cls λ (τ + k)) θ` (`wordOp`), with `cls` any function of the lift and the absolute tick.
  The carry at the word's end stands at `τ + ticks`.
* **The loci are shared across edges.** On the concrete medium a junction is read by every edge out
  of its ring and a channel by every edge among its blocks (`HNN/LocusMap.Reads`), so the
  constitution is not a per-edge function. Here it is any type `Con` with a per-locus agreement
  `agreeOn ℓ θ θ′` (`LocusMap.AgreeOn`). The laws assumed of it (`TickLaw.Lawful`) are the locus
  map's: an edge's operator moves only with the loci it reads (`LocusMap.blockOp_agree`), a
  block's reference only with the loci it reads, a deposit moves each locus from its own state and
  the data on the edges that read it (`LocusMap.deposited`, `locusData`), and the release keeps
  every locus it is told to keep (`LocusMap.agreeOn_release`). Every tick's operator is sparse on
  the declared graph, and a locus is read only along declared edges.
* **The opening and the reading read the constitution.** The Rust's source ports enter the word's
  opening and its receiving map enters the receiver's reading (`Locus::{SourcePort, ReceivingMap}`).
  Here the open state is a function of the constitution, supported on the sources, moving at a
  block only with the loci its opening reads (`openReads`, `open_reads`); each receiver's reading
  covector is read through a linear map of the constitution at its block (`recv`, `readThrough`),
  moving only with the loci it reads (`recvReads`, `recv_reads`), in the faces and in the
  comparison covectors a compare stages alike.

The retained loci are those read by an edge, or by the reference of a block, that a walk from a
source to a receiver passes, by the opening of a source that observes a receiver, or by a
receiver's reading (`Retained`); the collapse releases the others (`retain`). This is the
continuing collapse (`Diamond::continuing`) read on loci: an edge on a walk is in the diamond at
`e_last = 2 |B|` (`Retention.inDiamond_continuing_iff`).

[proved-derived; formal-checked] **The standing** (`tickStanding`). The continuing collapse is a
`Foundation/Standing.StandingLaw` for this resident: every admitted future face, of the current
word on the carried change and of every pending word on its stored carry, after any word of
ingests, re-keyings, refines, compares, discards, and commits and discards of staged deposits, is
read off the collapsed resident. As in `HNN/CarriedStanding` the law is proved through the agreement
the generators keep (`Agree`, `step_agree`, `observe_agree`), here on loci rather than edges:

* every retained locus agrees, so every tick's operator agrees on every walk edge and every
  block's reference agrees on every walk block, whatever the tick (`wordOp_agree`);
* each carry has the same tick and lift and agrees on every block that observes a receiver, so the
  two words run the same family and stay so at every tick (`TickFamily.trajectoryAt_agrees_on_walk`);
* every staged deposit is equal on every declared edge: on a walk edge by
  `TickFamily.depositDataAt_agree`, and off every walk both are empty, since every seed is reached
  from a source (`depositDataAt_off_walk`). So the deposit moves each retained locus alike.

[proved-derived; formal-checked] **A deposit between words never reopens a released locus**
(`released_stays_released`, `step_released`, `step_stagedOff`). After the collapse, along any word
of the generators, every locus it released stays in agreement with its released state. Only a
deposit moves loci; an edge that reads a released locus passes no walk, else the locus would be
retained, and every staged deposit is empty off every walk (a compare keeps this, since its seeds
are reached), so no datum reaches the locus. This needs the quiet laws (`TickLaw.Quiet`): the
agreement on a locus is an equivalence, and a deposit keeps a locus that no datum reaches, as the
concrete locus laws do (`LocusMap.deposit_descends`'s `hΦe`, `hΦc`).

[definition; agent-inferred] **What this leaves to the instance.** The laws of `TickLaw.Lawful` are
hypotheses here. `HNN/MediumStanding` is the instance on the concrete medium: it proves them there,
with the deposit keeping the medium admissible when each locus law keeps its locus admissible, and
shows that the Rust's per-locus rule keeps the loci retained here. The concrete medium has no
resonator operand, so on it `cls` reads only the sheet classes; the resonator's operand is
`HNN/LoadedRing`. The commits composed at held momentum (`ChainedBalance`'s `dep k`) are
`HNN/HeldCommits`.

The proofs of `HNN/CarriedStanding` and `HNN/TickFamily` are unchanged; their headers cite this file. No `sorry`, no `axiom`, no
`native_decide`.
-/

noncomputable section

namespace Holonics.HNN.TickStanding

open Holonics.HNN.Propagation Holonics.HNN.Retention Holonics.HNN.CarriedStanding
open Holonics.HNN.TickFamily
open scoped BigOperators

/-! ## The objects -/

section Objects

variable {B : Type*}

/-- [definition] **The carry** (`ReceptionCarry`): the change at the last word's end, the references
it was read at, the lift it ended on, and the tick of the field's clock it stands at. -/
structure TickCarry (M : B → Type*) (Ref : B → Type*) (Λ : Type*) where
  change : (b : B) → M b
  ref : (b : B) → Ref b
  lift : Λ
  tick : ℕ

/-- [definition] **A pending ratio** (`PendingSlot`): its producing anchor and the carry its word
opened on. -/
structure TickPend (M : B → Type*) (Ref : B → Type*) (Λ Mo : Type*) where
  lift : Λ
  moment : Mo
  opening : TickCarry M Ref Λ

/-- [definition] **The resident**: the constitution, the lift point, the open moment, the carried
change, the pending ratios of the chain in refine order, and the staged deposits. -/
structure TickResident (K : Type*) [Field K] (M : B → Type*) [∀ b, AddCommGroup (M b)]
    [∀ b, Module K (M b)] (Con : Type*) (Ref : B → Type*) (Λ Mo : Type*) where
  loci : Con
  lift : Λ
  moment : Mo
  carried : TickCarry M Ref Λ
  pending : List (TickPend M Ref Λ Mo)
  staged : List ((y z : B) → List (M z × Module.Dual K (M y)))

/-- [definition] **The law**: the block operators at a class, the loci each edge, each block's
reference, each block's opening and each receiver's reading read, and the agreement on a locus,
the references, the receiving map (each receiver's reading covector read through the
constitution, linear per block), the class at a lift and an absolute tick, the moment's open state
at the constitution (its source ports), the word's ticks, the crossing (local to each block, linear
in the change), the absorption at a word's end, the ingest and re-keying, the deposit of staged data
and the release of the loci a keep-predicate does not keep. -/
structure TickLaw (K : Type*) [Field K] (M : B → Type*) [∀ b, AddCommGroup (M b)]
    [∀ b, Module K (M b)] (Con Loc : Type*) (Ref : B → Type*) (Cls Λ Mo Cell Crib : Type*) where
  op : Cls → Con → BlockOp K M
  reads : Loc → B → B → Prop
  refReads : Loc → B → Prop
  openReads : Loc → B → Prop
  recvReads : Loc → B → Prop
  agreeOn : Loc → Con → Con → Prop
  ref : Con → (b : B) → Ref b
  recv : Con → (b : B) → Module.Dual K (M b) →ₗ[K] Module.Dual K (M b)
  cls : Λ → ℕ → Cls
  openState : Con → Λ → Mo → (b : B) → M b
  ticks : Λ → Mo → ℕ
  cross : Λ → Λ → (b : B) → Ref b → Ref b → (M b →ₗ[K] M b)
  absorb : (b : B) → M b →ₗ[K] M b
  ingestStep : Cell → Λ × Mo → Λ × Mo
  rekey : Crib → Λ → Λ
  apply : Con → ((y z : B) → List (M z × Module.Dual K (M y))) → Con
  release : (Loc → Prop) → Con → Con

variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
variable {Con Loc : Type*} {Ref : B → Type*} {Cls Λ Mo Cell Crib : Type*}

/-- [definition] **The laws of the locus map**, assumed of the instance: every operator is sparse on
the declared graph; a locus is read only along declared edges; an edge's operator moves only with
the loci it reads, a block's reference, opening and receiving map only with the loci they read; a
deposit moves each locus from its own state and the data on the edges that read it; and the release
keeps every locus it keeps. -/
structure TickLaw.Lawful (adj : B → B → Prop) [Fintype B]
    (L : TickLaw K M Con Loc Ref Cls Λ Mo Cell Crib) : Prop where
  sparse : ∀ c θ, Sparse adj (L.op c θ)
  reads_adj : ∀ ℓ z y, L.reads ℓ z y → adj z y
  op_reads : ∀ c θ θ' y z, (∀ ℓ, L.reads ℓ z y → L.agreeOn ℓ θ θ') → L.op c θ y z = L.op c θ' y z
  ref_reads : ∀ θ θ' b, (∀ ℓ, L.refReads ℓ b → L.agreeOn ℓ θ θ') → L.ref θ b = L.ref θ' b
  open_reads : ∀ θ θ' l m b, (∀ ℓ, L.openReads ℓ b → L.agreeOn ℓ θ θ') →
    L.openState θ l m b = L.openState θ' l m b
  recv_reads : ∀ θ θ' b, (∀ ℓ, L.recvReads ℓ b → L.agreeOn ℓ θ θ') → L.recv θ b = L.recv θ' b
  apply_local : ∀ θ θ' d d' ℓ, L.agreeOn ℓ θ θ' → (∀ y z, L.reads ℓ z y → d y z = d' y z) →
    L.agreeOn ℓ (L.apply θ d) (L.apply θ' d')
  release_keeps : ∀ (keep : Loc → Prop) θ ℓ, keep ℓ → L.agreeOn ℓ θ (L.release keep θ)

end Objects

/-! ## The resident and its generators -/

section Resident

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
variable {Con Loc : Type*} {Ref : B → Type*} {Cls Λ Mo Cell Crib : Type*}

variable (L : TickLaw K M Con Loc Ref Cls Λ Mo Cell Crib)

/-- [definition] **The word's family**: opened at the clock's tick `τ` at the lift `l`, tick `k`
runs the operator of the class at the absolute tick `τ + k`. -/
def wordOp (θ : Con) (l : Λ) (τ : ℕ) : ℕ → BlockOp K M := fun k => L.op (L.cls l (τ + k)) θ

/-- [definition] **The opening's interior**: the carried change crossed into the references of the
constitution `θ` at the lift `l`. -/
def interior (θ : Con) (l : Λ) (c : TickCarry M Ref Λ) : (b : B) → M b :=
  fun b => L.cross c.lift l b (c.ref b) (L.ref θ b) (c.change b)

/-- [definition] **The word's opening**: the moment's open state at the constitution `θ` plus the
opening's interior. -/
def opening (θ : Con) (l : Λ) (m : Mo) (c : TickCarry M Ref Λ) : (b : B) → M b :=
  L.openState θ l m + interior L θ l c

/-- [definition] **A reading through the receiving map**: each receiver's covector read through the
constitution `θ`'s receiving map at its block. -/
def readThrough (θ : Con) (g : (b : B) → Module.Dual K (M b)) : (b : B) → Module.Dual K (M b) :=
  fun b => L.recv θ b (g b)

/-- [definition] **The deposit's seeds**: the sources and the support of the opening's interior. -/
def seeds (S : Set B) (θ : Con) (l : Λ) (c : TickCarry M Ref Λ) : Set B :=
  S ∪ {b | interior L θ l c b ≠ 0}

/-- [definition] **The carry at a word's end**: the change the word opened on `c` reaches after its
ticks, through the absorption, with the references it ran at, standing at the tick after its last. -/
def endCarry (θ : Con) (l : Λ) (m : Mo) (c : TickCarry M Ref Λ) : TickCarry M Ref Λ where
  change b := L.absorb b (trajectoryAt (wordOp L θ l c.tick) (opening L θ l m c) (L.ticks l m) b)
  ref := L.ref θ
  lift := l
  tick := c.tick + L.ticks l m

variable (adj) in
/-- [definition] **The data a compare stages**: on every edge, what the pending word opened on its
stored carry at the constitution `θ` reads there, in the windows seeded at the sources and the
opening's interior, with each comparison covector read through `θ`'s receiving map. -/
def stagedOf (S R : Set B) (θ : Con) (p : TickPend M Ref Λ Mo)
    (rd : List (ℕ × ((b : B) → Module.Dual K (M b)))) :
    (y z : B) → List (M z × Module.Dual K (M y)) :=
  fun y z => depositDataAt adj (wordOp L θ p.lift p.opening.tick)
    (opening L θ p.lift p.moment p.opening) (seeds L S θ p.lift p.opening) R
    (rd.map fun r => (r.1, readThrough L θ r.2)) z y

variable (adj) in
/-- [definition] **The generators acting on the resident** (one chain in refine order), as in
`HNN/CarriedStanding.step`: refine opens a pending ratio on the carried change, stores that carry
and writes the carry to the end its word reaches; compare stages the `i`-th pending word's deposit
data at the contemporary constitution; discard drops it; a deposit commits a staged deposit. -/
def step (S R : Set B) :
    CarryGen Cell Crib (ReceiverFamily K M R) →
      TickResident K M Con Ref Λ Mo → TickResident K M Con Ref Λ Mo
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
    | some d => { res with loci := L.apply res.loci d, staged := res.staged.eraseIdx i }
  | .discardStaged i, res => { res with staged := res.staged.eraseIdx i }

/-- [definition] A word's admitted reading opened on a carry, at the constitution `θ`, through its
receiving map. -/
def wordRead {R : Set B} (θ : Con) (l : Λ) (m : Mo) (c : TickCarry M Ref Λ)
    (r : ReceiverReading K M R) : K :=
  pair (readThrough L θ r.1.2) (trajectoryAt (wordOp L θ l c.tick) (opening L θ l m c) r.1.1)

/-- [definition] **The faces**: the current word opened on the carried change (`none`) and the
`i`-th pending word on its stored carry (`some i`), at the contemporary constitution. -/
def observe {R : Set B} : Option ℕ × ReceiverReading K M R → TickResident K M Con Ref Λ Mo → K
  | (none, r), res => wordRead L res.loci res.lift res.moment res.carried r
  | (some i, r), res =>
    match res.pending[i]? with
    | none => 0
    | some p => wordRead L res.loci p.lift p.moment p.opening r

variable (adj) in
/-- [definition] **A retained locus**: one read by an edge, or by the reference of a block, that a
walk from a source to a receiver passes; or by the opening of a source that observes a receiver
(`Diamond::source_port`: `is_source(g) ∧ o_g ≤ e`); or by a receiver's reading
(`Diamond::retains`: `ReceivingMap(g)` when `g` is the receiver). -/
def Retained (S R : Set B) (ℓ : Loc) : Prop :=
  (∃ z y, L.reads ℓ z y ∧ OnWalk adj S R z y) ∨
    (∃ b, L.refReads ℓ b ∧ b ∈ reachAll adj S ∧ ObservesAll adj R b) ∨
    (∃ b, L.openReads ℓ b ∧ b ∈ S ∧ ObservesAll adj R b) ∨
    ∃ b, L.recvReads ℓ b ∧ b ∈ R

variable (adj) in
/-- [definition] **The retention**: the continuing collapse releases every locus not retained; the
lift point, the moment, the carries and the staged deposits are kept whole. -/
def retain (S R : Set B) (res : TickResident K M Con Ref Λ Mo) : TickResident K M Con Ref Λ Mo :=
  { res with loci := L.release (Retained adj L S R) res.loci }

variable (adj) in
/-- [definition] **The valid residents**: every carry's change on the blocks reached from the
sources. -/
def Valid (S : Set B) (res : TickResident K M Con Ref Λ Mo) : Prop :=
  SupportedIn res.carried.change (reachAll adj S) ∧
    ∀ p ∈ res.pending, SupportedIn p.opening.change (reachAll adj S)

/-! ### The agreement -/

variable (adj) in
/-- [definition] Two carries agree: equal lifts and ticks, changes equal on every block that
observes a receiver, references equal on every such block reached from a source. -/
def CarryAgree (S R : Set B) (c c' : TickCarry M Ref Λ) : Prop :=
  c.lift = c'.lift ∧ c.tick = c'.tick ∧
    (∀ b, b ∈ reachAll adj S → ObservesAll adj R b → c.ref b = c'.ref b) ∧
    ∀ b, ObservesAll adj R b → c.change b = c'.change b

variable (adj) in
/-- [definition] Two pending ratios agree: equal anchors and agreeing carries. -/
def PendAgree (S R : Set B) (p p' : TickPend M Ref Λ Mo) : Prop :=
  p.lift = p'.lift ∧ p.moment = p'.moment ∧ CarryAgree adj S R p.opening p'.opening

variable (adj) in
/-- [definition] Two staged deposits are equal on every declared edge. -/
def StagedAgree (d d' : (y z : B) → List (M z × Module.Dual K (M y))) : Prop :=
  ∀ y z, adj z y → d y z = d' y z

variable (adj) in
/-- [definition] **The agreement**: every retained locus agrees, equal lift and moment, agreeing
carries, agreeing pending ratios and staged deposits equal on every declared edge. -/
def Agree (S R : Set B) (res res' : TickResident K M Con Ref Λ Mo) : Prop :=
  (∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ res.loci res'.loci) ∧ res.lift = res'.lift ∧
    res.moment = res'.moment ∧ CarryAgree adj S R res.carried res'.carried ∧
    List.Forall₂ (PendAgree adj S R) res.pending res'.pending ∧
    List.Forall₂ (StagedAgree adj (K := K)) res.staged res'.staged

omit [Fintype B] [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)] in
theorem carryAgree_refl {S R : Set B} (c : TickCarry M Ref Λ) : CarryAgree adj S R c c :=
  ⟨rfl, rfl, fun _ _ _ => rfl, fun _ _ => rfl⟩

variable {L}

/-! ### The loci on a walk -/

/-- [proved-derived; formal-checked] **Every tick's operator agrees on every walk edge** when the
retained loci agree, whatever the class and the tick. -/
theorem op_agree (hL : L.Lawful adj) {S R : Set B} {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') (c : Cls) {y z : B}
    (hw : OnWalk adj S R z y) : L.op c θ y z = L.op c θ' y z :=
  hL.op_reads c θ θ' y z fun ℓ hr => hθ ℓ (Or.inl ⟨z, y, hr, hw⟩)

theorem wordOp_agree (hL : L.Lawful adj) {S R : Set B} {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') (l : Λ) (τ k : ℕ) {y z : B}
    (hw : OnWalk adj S R z y) : wordOp L θ l τ k y z = wordOp L θ' l τ k y z :=
  op_agree hL hθ _ hw

/-- [proved-derived; formal-checked] Every block's reference agrees on every walk block. -/
theorem ref_agree (hL : L.Lawful adj) {S R : Set B} {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') {b : B} (hr : b ∈ reachAll adj S)
    (hb : ObservesAll adj R b) : L.ref θ b = L.ref θ' b :=
  hL.ref_reads θ θ' b fun ℓ h => hθ ℓ (Or.inr (Or.inl ⟨b, h, hr, hb⟩))

/-- [proved-derived; formal-checked] Every open state agrees on every block that observes a
receiver: on a source its loci are retained, off the sources it is zero. -/
theorem openState_agree (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') (l : Λ) (m : Mo) {b : B}
    (hb : ObservesAll adj R b) : L.openState θ l m b = L.openState θ' l m b := by
  by_cases hS : b ∈ S
  · exact hL.open_reads θ θ' l m b fun ℓ h => hθ ℓ (Or.inr (Or.inr (Or.inl ⟨b, h, hS, hb⟩)))
  · rw [hopen θ l m b hS, hopen θ' l m b hS]

/-- [proved-derived; formal-checked] Every receiver's receiving map agrees. -/
theorem recv_agree (hL : L.Lawful adj) {S R : Set B} {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') {b : B} (hb : b ∈ R) :
    L.recv θ b = L.recv θ' b :=
  hL.recv_reads θ θ' b fun ℓ h => hθ ℓ (Or.inr (Or.inr (Or.inr ⟨b, h, hb⟩)))

omit [Fintype B] in
theorem readThrough_supported {R : Set B} {θ : Con} {g : (b : B) → Module.Dual K (M b)}
    (hg : SupportedIn g R) : SupportedIn (readThrough L θ g) R := fun b hb => by
  simp [readThrough, hg b hb]

/-- [proved-derived; formal-checked] A reading supported on the receivers reads the same through
two constitutions whose retained loci agree. -/
theorem readThrough_agree (hL : L.Lawful adj) {S R : Set B} {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') {g : (b : B) → Module.Dual K (M b)}
    (hg : SupportedIn g R) : readThrough L θ g = readThrough L θ' g := by
  funext b
  by_cases hb : b ∈ R
  · simp only [readThrough, recv_agree hL hθ hb]
  · simp [readThrough, hg b hb]

omit [Fintype B] in
theorem interior_supported {S : Set B} {θ : Con} {l : Λ} {c : TickCarry M Ref Λ}
    (hc : SupportedIn c.change (reachAll adj S)) :
    SupportedIn (interior L θ l c) (reachAll adj S) := fun b hb => by
  simp [interior, hc b hb]

omit [Fintype B] in
theorem opening_supported {S : Set B} (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    {θ : Con} {l : Λ} {m : Mo} {c : TickCarry M Ref Λ}
    (hc : SupportedIn c.change (reachAll adj S)) :
    SupportedIn (opening L θ l m c) (reachAll adj S) := fun b hb => by
  simp [opening, hopen θ l m b fun hbS => hb (subset_reachAll S hbS),
    interior_supported (L := L) (θ := θ) (l := l) hc b hb]

theorem interior_agree (hL : L.Lawful adj) {S R : Set B} {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') (l : Λ) {c c' : TickCarry M Ref Λ}
    (hc : SupportedIn c.change (reachAll adj S)) (hc' : SupportedIn c'.change (reachAll adj S))
    (hcc : CarryAgree adj S R c c') {b : B} (hb : ObservesAll adj R b) :
    interior L θ l c b = interior L θ' l c' b := by
  by_cases hr : b ∈ reachAll adj S
  · simp only [interior]
    rw [hcc.1, hcc.2.2.1 b hr hb, ref_agree hL hθ hr hb, hcc.2.2.2 b hb]
  · simp [interior, hc b hr, hc' b hr]

theorem opening_agree (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') (l : Λ) (m : Mo)
    {c c' : TickCarry M Ref Λ}
    (hc : SupportedIn c.change (reachAll adj S)) (hc' : SupportedIn c'.change (reachAll adj S))
    (hcc : CarryAgree adj S R c c') {b : B} (hb : ObservesAll adj R b) :
    opening L θ l m c b = opening L θ' l m c' b := by
  simp only [opening, Pi.add_apply, interior_agree hL hθ l hc hc' hcc hb,
    openState_agree hL hopen hθ l m hb]

theorem endCarry_supported (hL : L.Lawful adj) {S : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) (θ : Con) (l : Λ) (m : Mo)
    {c : TickCarry M Ref Λ} (hc : SupportedIn c.change (reachAll adj S)) :
    SupportedIn (endCarry L θ l m c).change (reachAll adj S) := fun b hb => by
  have hx := opening_supported (L := L) (θ := θ) (l := l) (m := m) hopen hc
  have h := (trajectoryAt_agrees_on_walk (R := (∅ : Set B))
    (fun k => hL.sparse _ θ) (fun k => hL.sparse _ θ) (fun _ _ _ _ => rfl) hx hx (fun _ _ => rfl)
    (L.ticks l m) (T := wordOp L θ l c.tick)).1
  simp only [endCarry, h b hb, map_zero]

theorem endCarry_agree (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') (l : Λ) (m : Mo)
    {c c' : TickCarry M Ref Λ}
    (hc : SupportedIn c.change (reachAll adj S)) (hc' : SupportedIn c'.change (reachAll adj S))
    (hcc : CarryAgree adj S R c c') :
    CarryAgree adj S R (endCarry L θ l m c) (endCarry L θ' l m c') := by
  refine ⟨rfl, by simp only [endCarry, hcc.2.1], fun b hr hb => ref_agree hL hθ hr hb,
    fun b hb => ?_⟩
  have h := trajectoryAt_agrees_on_walk (fun k => hL.sparse _ θ) (fun k => hL.sparse _ θ')
    (T := wordOp L θ l c.tick) (T' := wordOp L θ' l c'.tick)
    (fun k y z hw => by rw [← hcc.2.1]; exact wordOp_agree hL hθ l c.tick k hw)
    (opening_supported (L := L) (θ := θ) (l := l) (m := m) hopen hc)
    (opening_supported (L := L) (θ := θ') (l := l) (m := m) hopen hc')
    (fun b hb => opening_agree hL hopen hθ l m hc hc' hcc hb) (L.ticks l m)
  simp only [endCarry, h.2.2 b hb]

theorem seeds_agree (hL : L.Lawful adj) {S R : Set B} {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') (l : Λ) {c c' : TickCarry M Ref Λ}
    (hc : SupportedIn c.change (reachAll adj S)) (hc' : SupportedIn c'.change (reachAll adj S))
    (hcc : CarryAgree adj S R c c') (s : B) (hs : ObservesAll adj R s) :
    s ∈ seeds L S θ l c ↔ s ∈ seeds L S θ' l c' := by
  simp only [seeds, Set.mem_union, Set.mem_ofPred_eq, interior_agree hL hθ l hc hc' hcc hs]

omit [Fintype B] in
theorem seeds_reached {S : Set B} {θ : Con} {l : Λ} {c : TickCarry M Ref Λ}
    (hc : SupportedIn c.change (reachAll adj S)) {s : B} (hs : s ∈ seeds L S θ l c) :
    s ∈ reachAll adj S := by
  rcases hs with hs | hs
  · exact subset_reachAll S hs
  · by_contra h
    exact hs (interior_supported (L := L) (θ := θ) (l := l) hc s h)

omit [Fintype B] in
/-- A block reached from a set of reached blocks is reached. -/
theorem reachAll_of_reachWithin {S sd : Set B} (hsd : ∀ s ∈ sd, s ∈ reachAll adj S) {k : ℕ}
    {z : B} (hz : z ∈ reachWithin adj sd k) : z ∈ reachAll adj S := by
  obtain ⟨s, hs, n, -, hr⟩ := hz
  obtain ⟨t, x, hx, j, -, hxs⟩ := hsd s hs
  exact ⟨j + n, x, hx, j + n, le_rfl, hxs.trans hr⟩

/-- [proved-derived; formal-checked] **Off every walk a deposit reads nothing**: with every seed
reached from a source, an edge's window is empty unless its source block is reached and its target
observes a receiver. -/
theorem depositDataAt_off_walk {S R sd : Set B} (hsd : ∀ s ∈ sd, s ∈ reachAll adj S)
    (T : ℕ → BlockOp K M) (x₀ : (b : B) → M b) (rd : List (ℕ × ((b : B) → Module.Dual K (M b))))
    {z y : B} (hw : ¬ OnWalk adj S R z y) : depositDataAt adj T x₀ sd R rd z y = [] := by
  classical
  rw [depositDataAt, List.flatMap_eq_nil_iff]
  intro r _
  rw [List.map_eq_nil_iff, windowTicks, List.filter_eq_nil_iff]
  intro k _ hk
  simp only [decide_eq_true_eq] at hk
  exact hw ⟨reachAll_of_reachWithin hsd hk.1, ⟨_, hk.2⟩⟩

/-! ### Validity, agreement with the collapse, and the generators -/

theorem step_valid (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (g : CarryGen Cell Crib (ReceiverFamily K M R)) {res : TickResident K M Con Ref Λ Mo}
    (hv : Valid adj S res) : Valid adj S (step adj L S R g res) := by
  obtain ⟨θ, l, m, c, P, D⟩ := res
  obtain ⟨hc, hP⟩ := hv
  cases g with
  | ingest x => exact ⟨hc, hP⟩
  | locateKeys crib => exact ⟨hc, hP⟩
  | refine =>
    refine ⟨endCarry_supported hL hopen θ l m hc, fun p hp => ?_⟩
    rcases List.mem_append.mp hp with hp | hp
    · exact hP p hp
    · rw [List.mem_singleton.mp hp]
      exact hc
  | compare i rd =>
    simp only [step]
    cases P[i]? with
    | none => exact ⟨hc, hP⟩
    | some p => exact ⟨hc, fun q hq => hP q (List.mem_of_mem_eraseIdx hq)⟩
  | discard i => exact ⟨hc, fun q hq => hP q (List.mem_of_mem_eraseIdx hq)⟩
  | deposit i =>
    simp only [step]
    cases D[i]? with
    | none => exact ⟨hc, hP⟩
    | some d => exact ⟨hc, hP⟩
  | discardStaged i => exact ⟨hc, hP⟩

/-- [proved-derived; formal-checked] **A compare stages equal data on every declared edge.** -/
theorem stagedOf_agree (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') {p p' : TickPend M Ref Λ Mo}
    (hp : SupportedIn p.opening.change (reachAll adj S))
    (hp' : SupportedIn p'.opening.change (reachAll adj S)) (hpp : PendAgree adj S R p p')
    (rd : ReceiverFamily K M R) :
    StagedAgree adj (stagedOf adj L S R θ p rd.1) (stagedOf adj L S R θ' p' rd.1) := by
  obtain ⟨hpl, hpm, hpo⟩ := hpp
  intro y z hadj
  simp only [stagedOf]
  by_cases hw : OnWalk adj S R z y
  · have hrd : (rd.1.map fun r => (r.1, readThrough L θ r.2)) =
        rd.1.map fun r => (r.1, readThrough L θ' r.2) :=
      List.map_congr_left fun r hr => by rw [readThrough_agree hL hθ (rd.2 r hr)]
    rw [← hpl, ← hpm, ← hpo.2.1, hrd]
    exact depositDataAt_agree (fun k => hL.sparse _ θ) (fun k => hL.sparse _ θ')
      (fun k y z hw => wordOp_agree hL hθ p.lift p.opening.tick k hw)
      (seeds_agree hL hθ p.lift hp hp' hpo)
      (opening_supported (L := L) (θ := θ) (l := p.lift) (m := p.moment) hopen hp)
      (opening_supported (L := L) (θ := θ') (l := p.lift) (m := p.moment) hopen hp')
      (fun b hb => opening_agree hL hopen hθ p.lift p.moment hp hp' hpo hb)
      (fun r hr => by
        obtain ⟨r₀, hr₀, rfl⟩ := List.mem_map.mp hr
        exact readThrough_supported (rd.2 r₀ hr₀)) hw hadj
  · rw [depositDataAt_off_walk (fun s hs => seeds_reached hp hs) _ _ _ hw,
      depositDataAt_off_walk (fun s hs => seeds_reached hp' hs) _ _ _ hw]

theorem step_agree (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (g : CarryGen Cell Crib (ReceiverFamily K M R)) {res res' : TickResident K M Con Ref Λ Mo}
    (hv : Valid adj S res) (hv' : Valid adj S res') (h : Agree adj L S R res res') :
    Agree adj L S R (step adj L S R g res) (step adj L S R g res') := by
  obtain ⟨θ, l, m, c, P, D⟩ := res
  obtain ⟨θ', l', m', c', P', D'⟩ := res'
  obtain ⟨hc, hP⟩ := hv
  obtain ⟨hc', hP'⟩ := hv'
  obtain ⟨hθ, hl, hm, hcc, hPP, hDD⟩ := h
  simp only at hl hm
  subst hl hm
  cases g with
  | ingest x => exact ⟨hθ, rfl, rfl, hcc, hPP, hDD⟩
  | locateKeys crib => exact ⟨hθ, rfl, rfl, hcc, hPP, hDD⟩
  | refine =>
    exact ⟨hθ, rfl, rfl, endCarry_agree hL hopen hθ l m hc hc' hcc,
      List.rel_append hPP (.cons ⟨rfl, rfl, hcc⟩ .nil), hDD⟩
  | compare i rd =>
    have hi := forall₂_getElem? hPP i
    simp only [step]
    cases hpi : P[i]? with
    | none =>
      rw [hpi] at hi
      cases hpi' : P'[i]? with
      | none => exact ⟨hθ, rfl, rfl, hcc, hPP, hDD⟩
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
        have hpp := Option.rel_some_some.mp hi
        have hnew := stagedOf_agree hL hopen hθ (hP p (List.mem_of_getElem? hpi))
          (hP' p' (List.mem_of_getElem? hpi')) hpp rd
        exact ⟨hθ, rfl, rfl, hcc, forall₂_eraseIdx hPP i, List.rel_append hDD (.cons hnew .nil)⟩
  | discard i => exact ⟨hθ, rfl, rfl, hcc, forall₂_eraseIdx hPP i, hDD⟩
  | deposit i =>
    have hi := forall₂_getElem? hDD i
    simp only [step]
    generalize D[i]? = o at hi ⊢
    generalize D'[i]? = o' at hi ⊢
    cases hi with
    | none => exact ⟨hθ, rfl, rfl, hcc, hPP, hDD⟩
    | some hdd =>
      exact ⟨fun ℓ hℓ => hL.apply_local θ θ' _ _ ℓ (hθ ℓ hℓ)
        fun y z hr => hdd y z (hL.reads_adj ℓ z y hr), rfl, rfl, hcc, hPP,
        forall₂_eraseIdx hDD i⟩
  | discardStaged i => exact ⟨hθ, rfl, rfl, hcc, hPP, forall₂_eraseIdx hDD i⟩

omit [Fintype B] in
theorem retain_valid {S R : Set B} {res : TickResident K M Con Ref Λ Mo}
    (hv : Valid adj S res) : Valid adj S (retain adj L S R res) := hv

theorem agree_retain (hL : L.Lawful adj) {S R : Set B} (res : TickResident K M Con Ref Λ Mo) :
    Agree adj L S R res (retain adj L S R res) := by
  refine ⟨fun ℓ hℓ => hL.release_keeps _ res.loci ℓ hℓ, rfl, rfl, carryAgree_refl _, ?_, ?_⟩
  · exact forall₂_self (s := PendAgree adj S R) (fun _ => ⟨rfl, rfl, carryAgree_refl _⟩) _
  · exact forall₂_self (s := StagedAgree adj) (fun _ _ _ _ => rfl) res.staged

theorem wordRead_agree (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) {θ θ' : Con}
    (hθ : ∀ ℓ, Retained adj L S R ℓ → L.agreeOn ℓ θ θ') (l : Λ) (m : Mo)
    {c c' : TickCarry M Ref Λ}
    (hc : SupportedIn c.change (reachAll adj S)) (hc' : SupportedIn c'.change (reachAll adj S))
    (hcc : CarryAgree adj S R c c') (r : ReceiverReading K M R) :
    wordRead L θ l m c r = wordRead L θ' l m c' r := by
  simp only [wordRead]
  rw [← hcc.2.1, readThrough_agree hL hθ r.2]
  exact readings_agree_on_walk (fun k => hL.sparse _ θ) (fun k => hL.sparse _ θ')
    (fun k y z hw => wordOp_agree hL hθ l c.tick k hw)
    (opening_supported (L := L) (θ := θ) (l := l) (m := m) hopen hc)
    (opening_supported (L := L) (θ := θ') (l := l) (m := m) hopen hc')
    (fun b hb => opening_agree hL hopen hθ l m hc hc' hcc hb)
    (readThrough_supported r.2) r.1.1

theorem observe_agree (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (q : Option ℕ × ReceiverReading K M R) {res res' : TickResident K M Con Ref Λ Mo}
    (hv : Valid adj S res) (hv' : Valid adj S res') (h : Agree adj L S R res res') :
    observe L q res = observe L q res' := by
  obtain ⟨θ, l, m, c, P, D⟩ := res
  obtain ⟨θ', l', m', c', P', D'⟩ := res'
  obtain ⟨hc, hP⟩ := hv
  obtain ⟨hc', hP'⟩ := hv'
  obtain ⟨hθ, hl, hm, hcc, hPP, -⟩ := h
  simp only at hl hm
  subst hl hm
  obtain ⟨o, r⟩ := q
  cases o with
  | none => exact wordRead_agree hL hopen hθ l m hc hc' hcc r
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
        exact wordRead_agree hL hopen hθ _ _ (hP p (List.mem_of_getElem? hpi))
          (hP' p' (List.mem_of_getElem? hpi')) hpo r

/-! ### The standing -/

variable (adj) in
/-- [definition] The valid residents of the law `L`, the standing law's sources. The law is an
argument so that its carrier types are fixed. -/
def ValidResident (_L : TickLaw K M Con Loc Ref Cls Λ Mo Cell Crib) (S : Set B) :=
  {res : TickResident K M Con Ref Λ Mo // Valid adj S res}

variable (adj L) in
/-- [definition] The generators on the valid residents. -/
def transport (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (g : CarryGen Cell Crib (ReceiverFamily K M R)) (s : ValidResident adj L S) :
    ValidResident adj L S :=
  ⟨step adj L S R g s.1, step_valid hL hopen g s.2⟩

theorem transportWord_agree (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (w : List (CarryGen Cell Crib (ReceiverFamily K M R))) {s s' : ValidResident adj L S}
    (h : Agree adj L S R s.1 s'.1) :
    Agree adj L S R (Holonics.Foundation.Chronology.transportWord (transport adj L hL hopen) w s).1
      (Holonics.Foundation.Chronology.transportWord (transport adj L hL hopen) w s').1 := by
  induction w with
  | nil => exact h
  | cons g w ih => exact step_agree hL hopen g (Subtype.property _) (Subtype.property _) ih

/-- [proved-derived; formal-checked] **The standing with a tick-indexed word and shared loci**
(#62; the reception carry as the production default, #310). The resident holding the carried change
at its tick, with the generators ingest, locate keys, refine, compare (staging its deposit), discard,
and the commit or discard of a staged deposit, observed through the admitted faces of the current
word and of every pending word, each running the operator of its absolute tick's class at the
contemporary constitution, at any epoch, is a `Foundation/Standing.StandingLaw` whose retention is
the continuing collapse on loci, keeping the carry whole. -/
def tickStanding (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) :
    Holonics.Foundation.Standing.StandingLaw (CarryGen Cell Crib (ReceiverFamily K M R))
      (Option ℕ × ReceiverReading K M R) (ValidResident adj L S) (ValidResident adj L S) K where
  transport := transport adj L hL hopen
  observe q s := observe L q s.1
  retain s := ⟨retain adj L S R s.1, retain_valid s.2⟩
  reopen q w s := observe L q
    (Holonics.Foundation.Chronology.transportWord (transport adj L hL hopen) w s).1
  sufficient q w s :=
    (observe_agree hL hopen q (Subtype.property _) (Subtype.property _)
      (transportWord_agree (s := s) (s' := ⟨retain adj L S R s.1, retain_valid s.2⟩)
        hL hopen w (agree_retain hL s.1))).symm

/-! ### A deposit between words never reopens a released locus -/

/-- [definition] **The quiet laws**, assumed of the instance for the release's persistence: the
agreement on a locus is reflexive and transitive, and a deposit leaves a locus alone when no datum
reaches it, that is when every edge that reads it carries no data. On the concrete medium the
agreement is equality of the locus's operands and the deposit's locus laws keep a locus on empty
data (`LocusMap.deposit_descends`'s `hΦe`, `hΦc`; `Constitution::deposited`). -/
structure TickLaw.Quiet (L : TickLaw K M Con Loc Ref Cls Λ Mo Cell Crib) : Prop where
  refl : ∀ ℓ θ, L.agreeOn ℓ θ θ
  trans : ∀ ℓ θ₁ θ₂ θ₃, L.agreeOn ℓ θ₁ θ₂ → L.agreeOn ℓ θ₂ θ₃ → L.agreeOn ℓ θ₁ θ₃
  apply_quiet : ∀ θ d ℓ, (∀ y z, L.reads ℓ z y → d y z = []) → L.agreeOn ℓ θ (L.apply θ d)

variable (adj) in
/-- [definition] Every staged deposit carries no data off every walk. -/
def StagedOff (S R : Set B) (res : TickResident K M Con Ref Λ Mo) : Prop :=
  ∀ d ∈ res.staged, ∀ y z, ¬ OnWalk adj S R z y → d y z = []

omit [Fintype B] in
theorem stagedOff_eraseIdx {S R : Set B} {D : List ((y z : B) → List (M z × Module.Dual K (M y)))}
    (h : ∀ d ∈ D, ∀ y z, ¬ OnWalk adj S R z y → d y z = []) (i : ℕ) :
    ∀ d ∈ D.eraseIdx i, ∀ y z, ¬ OnWalk adj S R z y → d y z = [] :=
  fun d hd => h d (List.mem_of_mem_eraseIdx hd)

/-- [proved-derived; formal-checked] Every generator keeps the staged deposits quiet off every walk:
a compare stages data read in windows seeded on reached blocks (`depositDataAt_off_walk`). -/
theorem step_stagedOff {S R : Set B} (g : CarryGen Cell Crib (ReceiverFamily K M R))
    {res : TickResident K M Con Ref Λ Mo} (hv : Valid adj S res) (h : StagedOff adj S R res) :
    StagedOff adj S R (step adj L S R g res) := by
  obtain ⟨θ, l, m, c, P, D⟩ := res
  obtain ⟨hc, hP⟩ := hv
  cases g with
  | ingest x => exact h
  | locateKeys crib => exact h
  | refine => exact h
  | compare i rd =>
    simp only [step]
    cases hpi : P[i]? with
    | none => exact h
    | some p =>
      intro d hd y z hw
      rcases List.mem_append.mp hd with hd | hd
      · exact h d hd y z hw
      · rw [List.mem_singleton.mp hd]
        exact depositDataAt_off_walk
          (fun s hs => seeds_reached (hP p (List.mem_of_getElem? hpi)) hs) _ _ _ hw
  | discard i => exact h
  | deposit i =>
    simp only [step]
    cases D[i]? with
    | none => exact h
    | some d => exact stagedOff_eraseIdx (S := S) (R := R) h i
  | discardStaged i => exact stagedOff_eraseIdx (S := S) (R := R) h i

/-- [proved-derived; formal-checked] **No generator moves a released locus.** On a valid resident
whose staged deposits are quiet off every walk, every generator leaves each locus the collapse
releases in agreement with its state before: only a deposit moves loci, an edge that reads a
released locus passes no walk (else the locus would be retained), so no datum reaches it, and the
quiet law keeps it. -/
theorem step_released (hQ : L.Quiet) {S R : Set B}
    (g : CarryGen Cell Crib (ReceiverFamily K M R)) {res : TickResident K M Con Ref Λ Mo}
    (h : StagedOff adj S R res) {ℓ : Loc} (hℓ : ¬ Retained adj L S R ℓ) :
    L.agreeOn ℓ res.loci (step adj L S R g res).loci := by
  obtain ⟨θ, l, m, c, P, D⟩ := res
  cases g with
  | ingest x => exact hQ.refl ℓ θ
  | locateKeys crib => exact hQ.refl ℓ θ
  | refine => exact hQ.refl ℓ θ
  | compare i rd =>
    simp only [step]
    cases P[i]? with
    | none => exact hQ.refl ℓ θ
    | some p => exact hQ.refl ℓ θ
  | discard i => exact hQ.refl ℓ θ
  | deposit i =>
    simp only [step]
    cases hdi : D[i]? with
    | none => exact hQ.refl ℓ θ
    | some d =>
      exact hQ.apply_quiet θ d ℓ fun y z hr =>
        h d (List.mem_of_getElem? hdi) y z fun hw => hℓ (Or.inl ⟨z, y, hr, hw⟩)
  | discardStaged i => exact hQ.refl ℓ θ

/-- [proved-derived; formal-checked] **A deposit between words never reopens a released locus**
(#62; the reviewer's item on #315). After the continuing collapse, along any word of ingests,
re-keyings, refines, compares, discards, and commits and discards of staged deposits, every locus
the collapse released stays in agreement with its released state. The staged deposits must be quiet
off every walk at the collapse; every compare keeps that (`step_stagedOff`). -/
theorem released_stays_released (hL : L.Lawful adj) (hQ : L.Quiet) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (w : List (CarryGen Cell Crib (ReceiverFamily K M R))) (s : ValidResident adj L S)
    (h : StagedOff adj S R s.1) {ℓ : Loc} (hℓ : ¬ Retained adj L S R ℓ) :
    L.agreeOn ℓ (L.release (Retained adj L S R) s.1.loci)
      (Holonics.Foundation.Chronology.transportWord (transport adj L hL hopen) w
        ⟨retain adj L S R s.1, retain_valid s.2⟩).1.loci := by
  suffices hw : StagedOff adj S R (Holonics.Foundation.Chronology.transportWord
      (transport adj L hL hopen) w ⟨retain adj L S R s.1, retain_valid s.2⟩).1 ∧
      L.agreeOn ℓ (L.release (Retained adj L S R) s.1.loci)
        (Holonics.Foundation.Chronology.transportWord (transport adj L hL hopen) w
          ⟨retain adj L S R s.1, retain_valid s.2⟩).1.loci from hw.2
  induction w with
  | nil => exact ⟨h, hQ.refl ℓ _⟩
  | cons g w ih =>
    obtain ⟨hs, ha⟩ := ih
    exact ⟨step_stagedOff g (Subtype.property _) hs,
      hQ.trans ℓ _ _ _ ha (step_released hQ g hs hℓ)⟩

end Resident

end Holonics.HNN.TickStanding

#print axioms Holonics.HNN.TickStanding.depositDataAt_off_walk
#print axioms Holonics.HNN.TickStanding.stagedOf_agree
#print axioms Holonics.HNN.TickStanding.step_agree
#print axioms Holonics.HNN.TickStanding.observe_agree
#print axioms Holonics.HNN.TickStanding.tickStanding
#print axioms Holonics.HNN.TickStanding.step_released
#print axioms Holonics.HNN.TickStanding.released_stays_released
