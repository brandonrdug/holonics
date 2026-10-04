import Holonics.HNN.FactoredMedium
import Holonics.HNN.WordDiamond

/-!
# HNN.JointStep: the deposit's joint step read on the word's retained loci

[definition] #62 (the reviewer's gap, receipt 5976296910; the main line's rule, record B §8
"Every read a deposit makes past its locus reads the word's diamond"). The Rust's deposit is not a
per-locus law: one certified step `η = 2^k` scales every locus's move, and it is decided jointly.
Its gains read the contrast ports' `1 + ω`, the span factor `F(s)` with its Floquet decision and
the held gain families of each ring (`Constitution::{certify_steps, ring_reaches}`); the standing's
step is held in its lobes, whose crossings and halvings read the standings one contact out, and the
lock's proposal reads the same slices (`lobe`, `LockProposal`); a declared boost on a channel
refuses the step (`ActiveContact`); and the budget `B_Θ` bounds the successor's bits
(`Constitution::bits_within`). Record B §8 rules that each read but the budget reads only the loci
of the word's opened diamond (`Reach::loci`, `Diamond::retained`; its rings the rings whose element
the word holds, `reads_ring`), and that the budget counts the collapse's retained set: the stop rule
makes `B_Θ` a bound on the resident (`hnn::constitution`, module header "The budget and stop
rule"), and the retained set is invariant under the collapse. The Rust carries that rule
(`Constitution::deposited_within`, the budget over `retention::retained`).

Here the joint step is any such deposit:

* **A joint reading** `J θ d : Option Γ` of the constitution `θ` and the staged data `d`. `none` is
  a refusal (an uncertified gain, a refused Floquet decision, a boost, the budget), and a refused
  deposit leaves the constitution as it was (`jointApply`). `some γ` carries everything the step
  decides jointly: the step `η`, the lobe's holds and halvings, the lock's proposal.
* **A per-locus step at each joint value** `stepAt γ`: given `γ`, each locus moves from its own
  state, the data on the edges that read it and the opening's data at the blocks whose opening
  reads it (`StepLocal`), and keeps a locus no datum reaches (`StepQuiet`).
* **The joint reading reads the kept loci alone** (`ReadsOnly keep`): two constitutions agreeing on
  every locus of `keep`, with staged data equal on every declared edge and at every block, give the
  same reading. For
  the Rust, `keep` is the collapse's retained set.
* **The budget over the retained set, the other reads over the diamond** (`budgeted`): the
  diamond's reading `Jd` refuses or decides `γ`, and the budget `within` then admits the successor
  `stepAt γ θ d` or refuses. When `Jd` reads the diamond `diam`, `diam ⊆ keep`, and `within` reads
  `keep` (`BudgetReads`), the budgeted reading reads `keep` alone (`budgeted_readsOnly`): the
  successors of two agreeing pairs agree on `keep`, since the step at each joint value is
  per-locus.

[proved-derived; formal-checked] What this file proves:

1. **The standing with the joint step** (`jointStanding`): when the joint reading reads only the
   retained loci (`Retained`, the continuing collapse read on loci), the deposit keeps the retained
   loci (`jointLaw_applyRetained`), and the continuing collapse is a
   `Foundation/Standing.StandingLaw` for the resident (`TickStanding.tickStandingOf`).
2. **Any collapse keeping the read loci changes no step and no refusal** (`joint_keeps_sufficient`,
   `joint_reading_unchanged`). When the joint reading reads only a set `keep` containing every
   retained locus, releasing every locus outside `keep` changes, after any word of the generators,
   no admitted face of the current word or of any pending word, and no staged deposit's joint
   reading: every refusal stays a refusal and every joint value stays the same. The staged deposits
   must be quiet off every walk at the collapse (`StagedOff`), as in
   `TickStanding.released_stays_released`, and the agreement on a locus must be an equivalence.
3. **A released locus stays released** under the joint step (`joint_released_stays_released`).
4. **On the factored medium under the certified step** (`certifiedJointLaw`): every locus's factors
   move by the joint `η` times its own data's moves (`FactoredMedium.certifiedStep`), the joint
   reading any function of the loci the Rust's per-locus rule retains (`LocusMap.Retained` at
   `2|B|`). The Rust's collapse changes no face and no joint reading
   (`certified_joint_rust_collapse_sufficient`, `certified_joint_rust_reading_unchanged`), with no
   hypothesis on the moves. With the budget over that retained set and the other reads over a
   diamond inside it, the collapse changes no step and no refusal
   (`certified_budgeted_readsOnly`, `certified_budgeted_rust_unchanged`), and with the reads over
   the word's opened diamonds no hypothesis on the diamond (`certified_word_rust_unchanged`).

[agent-inferred] **What it leaves open.** That the Rust's `Reach::loci` lies within the loci its
collapse retains is `HNN/WordDiamond` (`word_diamond_retained`: every opened diamond, seeded at the
sources and a support they reach and observed from admitted receivers, lies in the continuing
collapse's retained set), so `certified_word_rust_unchanged` takes the reads on the opened diamonds
with no inclusion hypothesis. That the joint reading's non-budget reads stay on the opened diamond
and its budget on the retained set (`Constitution::deposited_within`) are the Rust's construction,
checked by its fixtures (`tests/retention.rs`), and remain hypotheses here. The carried
statistics and remainders in the locus's state (a factor family's `h_x′`, a linear locus's
successor Gram and chart, the standing's carried remainder) are owed in #62. The step's certified
descent is `Holon/Deposition`. The source port's deposit reads the opening's data the staged deposit
carries (`TickStanding.TickStage`, `RingLoci.port_gradient`).

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.JointStep

open Holonics.HNN.Propagation Holonics.HNN.Retention Holonics.HNN.CarriedStanding
open Holonics.HNN.TickFamily Holonics.HNN.TickStanding

/-! ## 1. The joint step -/

section Joint

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
variable {Con Loc : Type*} {Ref : B → Type*} {Cls Λ Mo Cell Crib Γ : Type*}

set_option hygiene false in
/-- The staged data of one deposit. -/
local notation "Data" => TickStage K M Λ Mo

/-- [definition] **The joint deposit**: the joint reading decides; a refusal leaves the
constitution, and a joint value `γ` moves every locus by the step at `γ`. -/
def jointApply (J : Con → Data → Option Γ) (stepAt : Γ → Con → Data → Con) (θ : Con)
    (d : Data) : Con :=
  match J θ d with
  | none => θ
  | some γ => stepAt γ θ d

/-- [definition] **The law with the joint step**: the law `L` with its deposit replaced by the
joint deposit. -/
def jointLaw (L : TickLaw K M Con Loc Ref Cls Λ Mo Cell Crib) (J : Con → Data → Option Γ)
    (stepAt : Γ → Con → Data → Con) : TickLaw K M Con Loc Ref Cls Λ Mo Cell Crib :=
  { L with apply := jointApply J stepAt }

variable (L : TickLaw K M Con Loc Ref Cls Λ Mo Cell Crib)

/-- [definition] **The step at each joint value is per-locus**: given the joint value, a locus
moves from its own state, the data on the edges that read it and the opening's data at the blocks
whose opening reads it. -/
def StepLocal (stepAt : Γ → Con → Data → Con) : Prop :=
  ∀ γ θ θ' d d' ℓ, L.agreeOn ℓ θ θ' → (∀ y z, L.reads ℓ z y → d.edges y z = d'.edges y z) →
    (∀ b, L.openReads ℓ b → d.opens b = d'.opens b) → L.agreeOn ℓ (stepAt γ θ d) (stepAt γ θ' d')

/-- [definition] **The step at each joint value keeps a locus no datum reaches.** -/
def StepQuiet (stepAt : Γ → Con → Data → Con) : Prop :=
  ∀ γ θ d ℓ, (∀ y z, L.reads ℓ z y → d.edges y z = []) → (∀ b, L.openReads ℓ b → d.opens b = []) →
    L.agreeOn ℓ θ (stepAt γ θ d)

variable (adj) in
/-- [definition] **The joint reading reads the loci `keep` alone**: constitutions agreeing on every
locus of `keep`, with staged data equal on every declared edge and at every block, read the
same. -/
def ReadsOnly (keep : Loc → Prop) (J : Con → Data → Option Γ) : Prop :=
  ∀ θ θ' d d', (∀ ℓ, keep ℓ → L.agreeOn ℓ θ θ') → StagedAgree adj (K := K) d d' → J θ d = J θ' d'

/-- [definition] The agreement on a locus is an equivalence. -/
structure Equiv : Prop where
  refl : ∀ ℓ θ, L.agreeOn ℓ θ θ
  symm : ∀ ℓ θ θ', L.agreeOn ℓ θ θ' → L.agreeOn ℓ θ' θ
  trans : ∀ ℓ θ₁ θ₂ θ₃, L.agreeOn ℓ θ₁ θ₂ → L.agreeOn ℓ θ₂ θ₃ → L.agreeOn ℓ θ₁ θ₃

variable {L} {J : Con → Data → Option Γ} {stepAt : Γ → Con → Data → Con}

/-- [proved-derived; formal-checked] The joint law keeps the local laws of `L`: only the deposit
changed. -/
theorem jointLaw_local (hL : L.Local adj) : (jointLaw L J stepAt).Local adj :=
  ⟨hL.sparse, hL.reads_adj, hL.op_reads, hL.ref_reads, hL.open_reads, hL.recv_reads,
    hL.release_keeps⟩

omit [Fintype B] in
/-- [proved-derived; formal-checked] **The joint deposit on two agreeing pairs**: where the joint
reading agrees, every locus the step at each joint value moves alike moves alike, and a refusal
leaves both. -/
theorem jointApply_agree {θ θ' : Con} {d d' : Data} (hJ : J θ d = J θ' d') {ℓ : Loc}
    (hθ : L.agreeOn ℓ θ θ') (hγ : ∀ γ, L.agreeOn ℓ (stepAt γ θ d) (stepAt γ θ' d')) :
    L.agreeOn ℓ (jointApply J stepAt θ d) (jointApply J stepAt θ' d') := by
  unfold jointApply
  rw [hJ]
  cases J θ' d' with
  | none => exact hθ
  | some γ => exact hγ γ

/-- [proved-derived; formal-checked] **The joint deposit keeps the retained loci** when its reading
reads only retained loci and its step at each joint value is per-locus. -/
theorem jointLaw_applyRetained (hL : L.Local adj) {S R : Set B}
    (hJ : ReadsOnly adj L (Retained adj L S R) J) (hstep : StepLocal L stepAt) :
    (jointLaw L J stepAt).ApplyRetained adj S R :=
  fun θ θ' d d' hθ hdd ℓ hℓ =>
    jointApply_agree (hJ θ θ' d d' hθ hdd) (hθ ℓ hℓ) fun γ =>
      hstep γ θ θ' d d' ℓ (hθ ℓ hℓ) (fun y z hr => hdd.1 y z (hL.reads_adj ℓ z y hr))
        fun b _ => hdd.2 b

/-- [proved-derived; formal-checked] **The standing with the joint step** (#62): the continuing
collapse on loci is a `Foundation/Standing.StandingLaw` for the resident whose deposit is the joint
step, when the joint reading reads only retained loci. -/
def jointStanding (hL : L.Local adj) {S R : Set B}
    (hJ : ReadsOnly adj L (Retained adj L S R) J) (hstep : StepLocal L stepAt)
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) :
    Holonics.Foundation.Standing.StandingLaw (CarryGen Cell Crib (ReceiverFamily K M R))
      (Option ℕ × ReceiverReading K M R) (ValidResident adj (jointLaw L J stepAt) S)
      (ValidResident adj (jointLaw L J stepAt) S) K :=
  tickStandingOf (jointLaw_local hL) (jointLaw_applyRetained hL hJ hstep) hopen

/-! ### A collapse keeping the read loci -/

/-- [definition] **A staged deposit's joint reading** on the resident: the reading of its `i`-th
staged deposit at the contemporary constitution (`none` when there is none). -/
def depositReading (J : Con → Data → Option Γ) (res : TickResident K M Con Ref Λ Mo) (i : ℕ) :
    Option (Option Γ) :=
  res.staged[i]?.map (J res.loci)

variable (adj L) in
/-- [definition] The pair invariant of a collapse keeping `keep`: the standing's agreement, every
locus of `keep` agreeing, and both residents' staged deposits quiet off every walk. -/
def KeepAgree (keep : Loc → Prop) (S R : Set B) (res res' : TickResident K M Con Ref Λ Mo) :
    Prop :=
  Agree adj L S R res res' ∧ (∀ ℓ, keep ℓ → L.agreeOn ℓ res.loci res'.loci) ∧
    StagedOff adj S R res ∧ StagedOff adj S R res'

omit [Fintype B] in
theorem retained_jointLaw {S R : Set B} {ℓ : Loc} :
    Retained adj (jointLaw L J stepAt) S R ℓ ↔ Retained adj L S R ℓ := Iff.rfl

/-- [proved-derived; formal-checked] **Every generator keeps the pair invariant** under the joint
step: a deposit's joint readings agree, because they read only `keep`; a retained locus then moves
alike by the per-locus step, and a kept locus off every walk is reached by no datum on either side,
so the quiet step keeps it on both. -/
theorem step_keepAgree (hL : L.Local adj) (hE : Equiv L) {keep : Loc → Prop} {S R : Set B}
    (hk : ∀ ℓ, Retained adj L S R ℓ → keep ℓ) (hJ : ReadsOnly adj L keep J)
    (hstep : StepLocal L stepAt) (hq : StepQuiet L stepAt)
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (g : CarryGen Cell Crib (ReceiverFamily K M R)) {res res' : TickResident K M Con Ref Λ Mo}
    (hv : Valid adj S res) (hv' : Valid adj S res')
    (h : KeepAgree adj (jointLaw L J stepAt) keep S R res res') :
    KeepAgree adj (jointLaw L J stepAt) keep S R (step adj (jointLaw L J stepAt) S R g res)
      (step adj (jointLaw L J stepAt) S R g res') := by
  obtain ⟨hA, hkeep, hoff, hoff'⟩ := h
  -- the deposit at the pair: the joint readings agree, and each kept locus moves alike
  have hdep : ∀ d d', StagedAgree adj d d' →
      ((∀ y z, ¬ OnWalk adj S R z y → d.edges y z = []) ∧
        ∀ b, ¬ (b ∈ S ∧ ObservesAll adj R b) → d.opens b = []) →
      ((∀ y z, ¬ OnWalk adj S R z y → d'.edges y z = []) ∧
        ∀ b, ¬ (b ∈ S ∧ ObservesAll adj R b) → d'.opens b = []) →
      ∀ ℓ, keep ℓ → L.agreeOn ℓ (jointApply J stepAt res.loci d)
        (jointApply J stepAt res'.loci d') := by
    intro d d' hdd hd hd' ℓ hℓ
    refine jointApply_agree (hJ _ _ _ _ hkeep hdd) (hkeep ℓ hℓ) fun γ => ?_
    by_cases hr : Retained adj L S R ℓ
    · exact hstep γ _ _ _ _ ℓ (hkeep ℓ hℓ) (fun y z hrd => hdd.1 y z (hL.reads_adj ℓ z y hrd))
        fun b _ => hdd.2 b
    · have hoffℓ : ∀ (e : Data), (∀ y z, ¬ OnWalk adj S R z y → e.edges y z = []) →
          ∀ y z, L.reads ℓ z y → e.edges y z = [] :=
        fun e he y z hrd => he y z fun hw => hr (Or.inl ⟨z, y, hrd, hw⟩)
      have hoffo : ∀ (e : Data), (∀ b, ¬ (b ∈ S ∧ ObservesAll adj R b) → e.opens b = []) →
          ∀ b, L.openReads ℓ b → e.opens b = [] :=
        fun e he b hrb => he b fun hb => hr (Or.inr (Or.inr (Or.inl ⟨b, hrb, hb.1, hb.2⟩)))
      exact hE.trans ℓ _ _ _ (hE.symm ℓ _ _ (hq γ _ d ℓ (hoffℓ d hd.1) (hoffo d hd.2)))
        (hE.trans ℓ _ _ _ (hkeep ℓ hℓ) (hq γ _ d' ℓ (hoffℓ d' hd'.1) (hoffo d' hd'.2)))
  refine ⟨step_agree (jointLaw_local hL) hopen g ?ret hv hv' hA, ?kept,
    step_stagedOff g hv hoff, step_stagedOff g hv' hoff'⟩
  case ret =>
    -- the retained loci: the readings agree, and the step at each joint value is per-locus
    intro d d' hdd ℓ hℓ
    refine jointApply_agree (hJ _ _ _ _ hkeep hdd) (hkeep ℓ (hk ℓ hℓ)) fun γ => ?_
    exact hstep γ _ _ _ _ ℓ (hkeep ℓ (hk ℓ hℓ)) (fun y z hrd => hdd.1 y z (hL.reads_adj ℓ z y hrd))
      fun b _ => hdd.2 b
  case kept =>
    -- the kept loci
    obtain ⟨θ, l, m, c, P, D⟩ := res
    obtain ⟨θ', l', m', c', P', D'⟩ := res'
    have hDD := hA.2.2.2.2.2
    cases g with
    | ingest x => exact hkeep
    | locateKeys crib => exact hkeep
    | refine => exact hkeep
    | compare i rd =>
      simp only [TickStanding.step]
      cases P[i]? <;> cases P'[i]? <;> exact hkeep
    | discard i => exact hkeep
    | deposit i =>
      have hi := forall₂_getElem? hDD i
      simp only [TickStanding.step]
      cases hdi : D[i]? with
      | none =>
        rw [hdi] at hi
        cases hdi' : D'[i]? with
        | none => exact hkeep
        | some d' =>
          rw [hdi'] at hi
          cases hi
      | some d =>
        rw [hdi] at hi
        cases hdi' : D'[i]? with
        | none =>
          rw [hdi'] at hi
          cases hi
        | some d' =>
          rw [hdi'] at hi
          exact hdep d d' (Option.rel_some_some.mp hi) (hoff d (List.mem_of_getElem? hdi))
            (hoff' d' (List.mem_of_getElem? hdi'))
    | discardStaged i => exact hkeep

/-- [proved-derived; formal-checked] **The pair invariant along any word.** -/
theorem transportOf_keepAgree (hL : L.Local adj) (hE : Equiv L) {keep : Loc → Prop}
    {S R : Set B} (hk : ∀ ℓ, Retained adj L S R ℓ → keep ℓ) (hJ : ReadsOnly adj L keep J)
    (hstep : StepLocal L stepAt) (hq : StepQuiet L stepAt)
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (w : List (CarryGen Cell Crib (ReceiverFamily K M R)))
    {s s' : ValidResident adj (jointLaw L J stepAt) S}
    (h : KeepAgree adj (jointLaw L J stepAt) keep S R s.1 s'.1) :
    KeepAgree adj (jointLaw L J stepAt) keep S R
      (Holonics.Foundation.Chronology.transportWord
        (transportOf adj (jointLaw L J stepAt) (jointLaw_local hL) hopen) w s).1
      (Holonics.Foundation.Chronology.transportWord
        (transportOf adj (jointLaw L J stepAt) (jointLaw_local hL) hopen) w s').1 := by
  induction w with
  | nil => exact h
  | cons g w ih =>
    exact step_keepAgree hL hE hk hJ hstep hq hopen g (Subtype.property _) (Subtype.property _) ih

theorem keepAgree_release (hL : L.Local adj) {keep : Loc → Prop} {S R : Set B}
    (hk : ∀ ℓ, Retained adj L S R ℓ → keep ℓ) (res : TickResident K M Con Ref Λ Mo)
    (hoff : StagedOff adj S R res) :
    KeepAgree adj (jointLaw L J stepAt) keep S R res { res with loci := L.release keep res.loci } :=
  ⟨⟨fun ℓ hℓ => hL.release_keeps keep res.loci ℓ (hk ℓ hℓ), rfl, rfl,
      TickStanding.carryAgree_refl _,
      forall₂_self (s := TickStanding.PendAgree adj S R)
        (fun _ => ⟨rfl, rfl, TickStanding.carryAgree_refl _⟩) _,
      forall₂_self (s := TickStanding.StagedAgree adj) (fun _ => ⟨fun _ _ _ => rfl, fun _ => rfl⟩)
        res.staged⟩,
    fun ℓ hℓ => hL.release_keeps keep res.loci ℓ hℓ, hoff, hoff⟩

/-- [proved-derived; formal-checked] **A collapse keeping the read loci is sufficient under the
joint step**: releasing every locus outside `keep`, which contains every retained locus and every
locus the joint reading reads, changes no admitted face of the current word or of any pending word
after any word of the generators. -/
theorem joint_keeps_sufficient (hL : L.Local adj) (hE : Equiv L) {keep : Loc → Prop}
    {S R : Set B} (hk : ∀ ℓ, Retained adj L S R ℓ → keep ℓ) (hJ : ReadsOnly adj L keep J)
    (hstep : StepLocal L stepAt) (hq : StepQuiet L stepAt)
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (q : Option ℕ × ReceiverReading K M R) (w : List (CarryGen Cell Crib (ReceiverFamily K M R)))
    (s : ValidResident adj (jointLaw L J stepAt) S) (hoff : StagedOff adj S R s.1) :
    observe (jointLaw L J stepAt) q (Holonics.Foundation.Chronology.transportWord
        (transportOf adj (jointLaw L J stepAt) (jointLaw_local hL) hopen) w
        ⟨{ s.1 with loci := L.release keep s.1.loci }, s.2⟩).1 =
      observe (jointLaw L J stepAt) q (Holonics.Foundation.Chronology.transportWord
        (transportOf adj (jointLaw L J stepAt) (jointLaw_local hL) hopen) w s).1 :=
  (observe_agree (jointLaw_local hL) hopen q (Subtype.property _) (Subtype.property _)
    (transportOf_keepAgree hL hE hk hJ hstep hq hopen w (s := s)
      (s' := ⟨{ s.1 with loci := L.release keep s.1.loci }, s.2⟩)
      (keepAgree_release hL hk s.1 hoff)).1).symm

omit [Fintype B] in
/-- [proved-derived; formal-checked] Under the pair invariant every staged deposit's joint reading
agrees. -/
theorem depositReading_of_keepAgree {keep : Loc → Prop} {S R : Set B}
    (hJ : ReadsOnly adj L keep J) {res res' : TickResident K M Con Ref Λ Mo}
    (h : KeepAgree adj (jointLaw L J stepAt) keep S R res res') (i : ℕ) :
    depositReading J res i = depositReading J res' i := by
  obtain ⟨⟨-, -, -, -, -, hDD⟩, hkeep, -, -⟩ := h
  have hi := forall₂_getElem? hDD i
  unfold depositReading
  revert hi
  generalize res.staged[i]? = o
  generalize res'.staged[i]? = o'
  intro hi
  cases hi with
  | none => rfl
  | some hdd => exact congrArg some (hJ _ _ _ _ hkeep hdd)

/-- [proved-derived; formal-checked] **A collapse keeping the read loci changes no refusal and no
joint value**: after any word of the generators, every staged deposit's joint reading on the
collapsed resident is the uncollapsed one's, a refusal (`some none`) included. -/
theorem joint_reading_unchanged (hL : L.Local adj) (hE : Equiv L) {keep : Loc → Prop}
    {S R : Set B} (hk : ∀ ℓ, Retained adj L S R ℓ → keep ℓ) (hJ : ReadsOnly adj L keep J)
    (hstep : StepLocal L stepAt) (hq : StepQuiet L stepAt)
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (w : List (CarryGen Cell Crib (ReceiverFamily K M R)))
    (s : ValidResident adj (jointLaw L J stepAt) S) (hoff : StagedOff adj S R s.1) (i : ℕ) :
    depositReading J (Holonics.Foundation.Chronology.transportWord
        (transportOf adj (jointLaw L J stepAt) (jointLaw_local hL) hopen) w
        ⟨{ s.1 with loci := L.release keep s.1.loci }, s.2⟩).1 i =
      depositReading J (Holonics.Foundation.Chronology.transportWord
        (transportOf adj (jointLaw L J stepAt) (jointLaw_local hL) hopen) w s).1 i := by
  exact (depositReading_of_keepAgree hJ (transportOf_keepAgree hL hE hk hJ hstep hq hopen w
    (s := s) (s' := ⟨{ s.1 with loci := L.release keep s.1.loci }, s.2⟩)
    (keepAgree_release hL hk s.1 hoff)) i).symm

/-- [proved-derived; formal-checked] **A deposit between words never reopens a released locus**
under the joint step: its step at each joint value is quiet, and a refusal moves nothing. -/
theorem joint_released_stays_released (hL : L.Local adj) (hE : Equiv L) {S R : Set B}
    (hq : StepQuiet L stepAt) (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S)
    (w : List (CarryGen Cell Crib (ReceiverFamily K M R)))
    (s : ValidResident adj (jointLaw L J stepAt) S) (h : StagedOff adj S R s.1) {ℓ : Loc}
    (hℓ : ¬ Retained adj L S R ℓ) :
    L.agreeOn ℓ (L.release (Retained adj L S R) s.1.loci)
      (Holonics.Foundation.Chronology.transportWord
        (transportOf adj (jointLaw L J stepAt) (jointLaw_local hL) hopen) w
        ⟨retain adj (jointLaw L J stepAt) S R s.1, retain_valid s.2⟩).1.loci :=
  released_stays_releasedOf (L := jointLaw L J stepAt) (jointLaw_local hL)
    ⟨hE.refl, hE.trans, fun θ d ℓ hd ho => by
      show L.agreeOn ℓ θ (jointApply J stepAt θ d)
      unfold jointApply
      cases J θ d with
      | none => exact hE.refl ℓ θ
      | some γ => exact hq γ θ d ℓ hd ho⟩ hopen w s h hℓ

/-! ### The budget over the retained set, the other reads over the diamond -/

/-- [definition] **The budgeted joint reading** (`Constitution::bits_within` and the stop rule,
`B_Θ`): the diamond's reading `Jd` refuses or decides a joint value `γ`; the budget `within` then
admits the successor `stepAt γ θ d` or refuses the deposit (`none`), and the predecessor stays. -/
def budgeted (Jd : Con → Data → Option Γ) (within : Con → Bool) (stepAt : Γ → Con → Data → Con) :
    Con → Data → Option Γ :=
  fun θ d => (Jd θ d).bind fun γ => if within (stepAt γ θ d) then some γ else none

variable (L) in
/-- [definition] **The budget reads the loci `keep` alone**: two constitutions agreeing on every
locus of `keep` are both within the budget or both past it. -/
def BudgetReads (keep : Loc → Prop) (within : Con → Bool) : Prop :=
  ∀ θ θ', (∀ ℓ, keep ℓ → L.agreeOn ℓ θ θ') → within θ = within θ'

/-- [proved-derived; formal-checked] **The budgeted reading reads the kept loci alone** when the
budget reads `keep`, the other reads read the diamond `diam` inside `keep`, and the step at each
joint value is per-locus: the successors of two agreeing pairs agree on `keep`, so the budget reads
them alike. -/
theorem budgeted_readsOnly (hL : L.Local adj) {Jd : Con → Data → Option Γ} {within : Con → Bool}
    {diam keep : Loc → Prop} (hdk : ∀ ℓ, diam ℓ → keep ℓ) (hd : ReadsOnly adj L diam Jd)
    (hb : BudgetReads L keep within) (hstep : StepLocal L stepAt) :
    ReadsOnly adj L keep (budgeted Jd within stepAt) := by
  intro θ θ' d d' hθ hdd
  unfold budgeted
  rw [hd θ θ' d d' (fun ℓ h => hθ ℓ (hdk ℓ h)) hdd]
  cases Jd θ' d' with
  | none => rfl
  | some γ =>
    simp only [Option.bind_some]
    rw [hb _ _ fun ℓ hℓ =>
      hstep γ θ θ' d d' ℓ (hθ ℓ hℓ) (fun y z hr => hdd.1 y z (hL.reads_adj ℓ z y hr))
        fun b _ => hdd.2 b]

end Joint

/-! ## 2. The certified joint step on the factored medium -/

section Certified

open Holonics.HNN.FactoredMedium Holonics.HNN.LocusMap Holonics.HNN.MediumStanding
open Holonics.HNN.Word Holonics.HNN.TickBlocks

universe u

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {FE : Ring → Type u} [∀ r, NormedAddCommGroup (FE r)] [∀ r, InnerProductSpace ℝ (FE r)]
  [∀ r, FiniteDimensional ℝ (FE r)]
variable {FC : Contact → Type u} [∀ a, NormedAddCommGroup (FC a)]
  [∀ a, InnerProductSpace ℝ (FC a)] [∀ a, FiniteDimensional ℝ (FC a)]
variable {endRing : Contact × Bool → Ring}
variable {Λ Mo Cell Crib : Type*}
variable {h₀ : ℝ} {cls : Λ → ℕ → Ring → ρ → ℝ}
  {openState : Λ → Mo → (b : Ring ⊕ Contact) → BlockM endRing V Ch b} {ticks : Λ → Mo → ℕ}
  {cross : Λ → Λ → (b : Ring ⊕ Contact) → MediumRef Ring Ch b → MediumRef Ring Ch b →
    (BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b)}
  {absorb : (b : Ring ⊕ Contact) → BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b}
  {ingestStep : Cell → Λ × Mo → Λ × Mo} {rekey : Crib → Λ → Λ}
  {ge : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r → (y z : Ring ⊕ Contact) →
    BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y) →
    ElementFactors (V := V) (FE := FE) (ρ := ρ) r}
  {gc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a → (y z : Ring ⊕ Contact) →
    BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y) →
    ChannelFactors (Ch := Ch) (FC := FC) a}

set_option quotPrecheck false in
/-- The factored medium's law with the certified step at the steps `η` (one per element and one per
channel, decided jointly). -/
local notation "CLη" η:arg => factoredLaw (Cell := Cell) (Crib := Crib) h₀ cls openState ticks cross
  absorb ingestStep rekey (fun r => certifiedStep (fun _ _ => (η : (Ring → ℝ) × (Contact → ℝ)).1 r)
    (ge r)) (fun a => certifiedStep (fun _ _ => (η : (Ring → ℝ) × (Contact → ℝ)).2 a) (gc a))

set_option quotPrecheck false in
/-- The factored medium's law at the unit step, whose deposit the joint step replaces. -/
local notation "CL1" => CLη ((fun _ => 1, fun _ => 1) : (Ring → ℝ) × (Contact → ℝ))

/-- [definition] **The certified joint step on the factored medium** (`Constitution::deposited`
with `certify_steps`): the joint reading `J` refuses (`none`) or decides a step per element and per
channel (`some η`: the certified `2^k`, halved where the lobe holds a family); each locus's factors
then move by its step times its own data's moves (`certifiedStep`). -/
def certifiedJointLaw
    (J : FactoredAt ρ V Ch FE FC endRing h₀ → TickStage ℝ (BlockM endRing V Ch) Λ Mo →
      Option ((Ring → ℝ) × (Contact → ℝ))) :
    TickLaw ℝ (BlockM endRing V Ch) (FactoredAt ρ V Ch FE FC endRing h₀) (Locus Ring Contact)
      (MediumRef Ring Ch) (Ring → ρ → ℝ) Λ Mo Cell Crib :=
  jointLaw CL1 J fun η => (CLη η).apply

set_option quotPrecheck false in
-- The certified joint law at the section's operands.
local notation "CJ" J:arg => certifiedJointLaw (Cell := Cell) (Crib := Crib) (h₀ := h₀) (cls := cls)
  (openState := openState) (ticks := ticks) (cross := cross) (absorb := absorb)
  (ingestStep := ingestStep) (rekey := rekey) (ge := ge) (gc := gc) J

/-- [proved-derived; formal-checked] The agreement on the factors' loci is an equivalence. -/
theorem factored_equiv : Equiv (CL1) where
  refl ℓ φ := fagreeOn_refl φ.1 ℓ
  symm ℓ φ φ' h := by
    cases ℓ with
    | element r => exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩
    | junction r => exact Eq.symm h
    | channel a => exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun s => (h.2.2.2 s).symm⟩
    | conductance a => exact Eq.symm h
  trans _ _ _ _ h₁ h₂ := fagreeOn_trans h₁ h₂

/-- [proved-derived; formal-checked] The certified step at each joint value is per-locus. -/
theorem certified_stepLocal : StepLocal (CL1) fun η => (CLη η).apply :=
  fun η θ θ' d d' ℓ hθ hd ho =>
    (factoredLaw_lawful (Cell := Cell) (Crib := Crib) (h₀ := h₀) (cls := cls)
      (openState := openState) (ticks := ticks) (cross := cross) (absorb := absorb)
      (ingestStep := ingestStep) (rekey := rekey)
      (Ψe := fun r => certifiedStep (fun _ _ => η.1 r) (ge r))
      (Ψc := fun a => certifiedStep (fun _ _ => η.2 a) (gc a))).apply_local θ θ' d d' ℓ hθ hd ho

/-- [proved-derived; formal-checked] The certified step at each joint value keeps a locus no datum
reaches. -/
theorem certified_stepQuiet : StepQuiet (CL1) fun η => (CLη η).apply :=
  fun η θ d ℓ hd ho =>
    (factoredLaw_quiet (Cell := Cell) (Crib := Crib) (h₀ := h₀) (cls := cls)
      (openState := openState) (ticks := ticks) (cross := cross) (absorb := absorb)
      (ingestStep := ingestStep) (rekey := rekey)
      (Ψe := fun r => certifiedStep (fun _ _ => η.1 r) (ge r))
      (Ψc := fun a => certifiedStep (fun _ _ => η.2 a) (gc a))
      (fun r p => certifiedStep_quiet _ (ge r) p)
      (fun a p => certifiedStep_quiet _ (gc a) p)).apply_quiet θ d ℓ hd ho

set_option quotPrecheck false in
-- The loci the Rust's per-locus rule retains under the continuing diamond.
local notation "RUST" S:arg R:arg =>
  LocusMap.Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact))

/-- [proved-derived; formal-checked] **The Rust's collapse is sufficient under the certified joint
step** (#62; record B §8): with the joint reading any function of the loci the Rust's per-locus rule
retains and of the staged data, releasing every other locus changes no admitted face of the current
word or of any pending word, after any word of the generators. -/
theorem certified_joint_rust_collapse_sufficient
    {J : FactoredAt ρ V Ch FE FC endRing h₀ → TickStage ℝ (BlockM endRing V Ch) Λ Mo →
      Option ((Ring → ℝ) × (Contact → ℝ))} {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (hopen : ∀ l m, SupportedIn (openState l m) S)
    (hJ : ReadsOnly (blockAdj endRing) (CL1) (RUST S R) J)
    (q : Option ℕ × ReceiverReading ℝ (BlockM endRing V Ch) R)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) (CJ J) S)
    (hoff : StagedOff (blockAdj endRing) S R s.1) :
    observe (CJ J) q
        (Holonics.Foundation.Chronology.transportWord
          (transportOf (blockAdj endRing) (CJ J)
            (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w
          ⟨{ s.1 with loci := (CL1).release (RUST S R) s.1.loci }, s.2⟩).1 =
      observe (CJ J) q
        (Holonics.Foundation.Chronology.transportWord
          (transportOf (blockAdj endRing) (CJ J)
            (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w s).1 :=
  joint_keeps_sufficient (keep := RUST S R) factoredLaw_lawful.toLocal factored_equiv
    (fun _ hℓ => retained_rust_factored hS hR hℓ) hJ certified_stepLocal certified_stepQuiet
    (fun _ => hopen) q w s hoff

/-- [proved-derived; formal-checked] **The Rust's collapse changes no refusal and no joint step**
under the certified joint step: after any word of the generators, every staged deposit's joint
reading on the collapsed resident is the uncollapsed one's. -/
theorem certified_joint_rust_reading_unchanged
    {J : FactoredAt ρ V Ch FE FC endRing h₀ → TickStage ℝ (BlockM endRing V Ch) Λ Mo →
      Option ((Ring → ℝ) × (Contact → ℝ))} {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (hopen : ∀ l m, SupportedIn (openState l m) S)
    (hJ : ReadsOnly (blockAdj endRing) (CL1) (RUST S R) J)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) (CJ J) S)
    (hoff : StagedOff (blockAdj endRing) S R s.1) (i : ℕ) :
    depositReading J (Holonics.Foundation.Chronology.transportWord
        (transportOf (blockAdj endRing) (CJ J)
          (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w
        ⟨{ s.1 with loci := (CL1).release (RUST S R) s.1.loci }, s.2⟩).1 i =
      depositReading J (Holonics.Foundation.Chronology.transportWord
        (transportOf (blockAdj endRing) (CJ J)
          (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w s).1 i :=
  joint_reading_unchanged (keep := RUST S R) factoredLaw_lawful.toLocal factored_equiv
    (fun _ hℓ => retained_rust_factored hS hR hℓ) hJ certified_stepLocal certified_stepQuiet
    (fun _ => hopen) w s hoff i

/-- [proved-derived; formal-checked] **The certified joint reading with its budget over the retained
set** (record B §8; the stop rule bounds the resident, and the collapse's retained set is invariant
under the collapse): with the budget reading the loci the Rust's rule retains and the other reads
(the gains, the Floquet decisions, the held families, the boost gate, the lobe and the lock) reading
the word's diamond `diam` inside them, the budgeted reading reads the retained loci alone. -/
theorem certified_budgeted_readsOnly
    {Jd : FactoredAt ρ V Ch FE FC endRing h₀ → TickStage ℝ (BlockM endRing V Ch) Λ Mo →
      Option ((Ring → ℝ) × (Contact → ℝ))} {within : FactoredAt ρ V Ch FE FC endRing h₀ → Bool}
    {diam : Locus Ring Contact → Prop} {S R : Set (Ring ⊕ Contact)}
    (hdk : ∀ ℓ, diam ℓ → (RUST S R) ℓ) (hd : ReadsOnly (blockAdj endRing) (CL1) diam Jd)
    (hb : BudgetReads (CL1) (RUST S R) within) :
    ReadsOnly (blockAdj endRing) (CL1) (RUST S R)
      (budgeted Jd within fun η => (CLη η).apply) :=
  budgeted_readsOnly factoredLaw_lawful.toLocal hdk hd hb
    (certified_stepLocal (ge := ge) (gc := gc))

/-- [proved-derived; formal-checked] **The Rust's collapse changes no step and no refusal under the
budgeted certified step** (#62; record B §8): the budget over the retained set and the other reads
over the diamond inside it, releasing every locus the Rust's rule does not retain changes, after
any word of the generators, no admitted face and no staged deposit's joint reading, a refusal by
the budget or by any other read included. -/
theorem certified_budgeted_rust_unchanged
    {Jd : FactoredAt ρ V Ch FE FC endRing h₀ → TickStage ℝ (BlockM endRing V Ch) Λ Mo →
      Option ((Ring → ℝ) × (Contact → ℝ))} {within : FactoredAt ρ V Ch FE FC endRing h₀ → Bool}
    {diam : Locus Ring Contact → Prop} {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (hopen : ∀ l m, SupportedIn (openState l m) S)
    (hdk : ∀ ℓ, diam ℓ → (RUST S R) ℓ) (hd : ReadsOnly (blockAdj endRing) (CL1) diam Jd)
    (hb : BudgetReads (CL1) (RUST S R) within)
    (q : Option ℕ × ReceiverReading ℝ (BlockM endRing V Ch) R)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing)
      (CJ (budgeted Jd within fun η => (CLη η).apply)) S)
    (hoff : StagedOff (blockAdj endRing) S R s.1) (i : ℕ) :
    observe (CJ (budgeted Jd within fun η => (CLη η).apply)) q
        (Holonics.Foundation.Chronology.transportWord
          (transportOf (blockAdj endRing)
            (CJ (budgeted Jd within fun η => (CLη η).apply))
            (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w
          ⟨{ s.1 with loci := (CL1).release (RUST S R) s.1.loci }, s.2⟩).1 =
      observe (CJ (budgeted Jd within fun η => (CLη η).apply))
        q (Holonics.Foundation.Chronology.transportWord
          (transportOf (blockAdj endRing)
            (CJ (budgeted Jd within fun η => (CLη η).apply))
            (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w s).1 ∧
    depositReading (budgeted Jd within fun η => (CLη η).apply)
        (Holonics.Foundation.Chronology.transportWord
          (transportOf (blockAdj endRing)
            (CJ (budgeted Jd within fun η => (CLη η).apply))
            (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w
          ⟨{ s.1 with loci := (CL1).release (RUST S R) s.1.loci }, s.2⟩).1 i =
      depositReading (budgeted Jd within fun η => (CLη η).apply)
        (Holonics.Foundation.Chronology.transportWord
          (transportOf (blockAdj endRing)
            (CJ (budgeted Jd within fun η => (CLη η).apply))
            (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w s).1 i :=
  have hJ := certified_budgeted_readsOnly (ge := ge) (gc := gc) hdk hd hb
  ⟨certified_joint_rust_collapse_sufficient hS hR hopen hJ q w s hoff,
    certified_joint_rust_reading_unchanged hS hR hopen hJ w s hoff i⟩

/-- [proved-derived; formal-checked] **The release law with no hypothesis on the diamond** (#62;
record B §8; `HNN/WordDiamond`): with the joint reading's non-budget reads over the word's opened
diamonds (`Reach::loci`: seeded at the sources and a carried support they reach, observed from
receivers among the admitted ones, at any epoch bound) and the budget over the retained set,
releasing every locus the Rust's rule does not retain changes, after any word of the generators,
no admitted face and no staged deposit's joint reading, a refusal included. -/
theorem certified_word_rust_unchanged
    {Jd : FactoredAt ρ V Ch FE FC endRing h₀ → TickStage ℝ (BlockM endRing V Ch) Λ Mo →
      Option ((Ring → ℝ) × (Contact → ℝ))} {within : FactoredAt ρ V Ch FE FC endRing h₀ → Bool}
    {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (hopen : ∀ l m, SupportedIn (openState l m) S)
    (hd : ReadsOnly (blockAdj endRing) (CL1) (WordDiamond.OpenedDiamond endRing S R) Jd)
    (hb : BudgetReads (CL1) (RUST S R) within)
    (q : Option ℕ × ReceiverReading ℝ (BlockM endRing V Ch) R)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing)
      (CJ (budgeted Jd within fun η => (CLη η).apply)) S)
    (hoff : StagedOff (blockAdj endRing) S R s.1) (i : ℕ) :
    observe (CJ (budgeted Jd within fun η => (CLη η).apply)) q
        (Holonics.Foundation.Chronology.transportWord
          (transportOf (blockAdj endRing)
            (CJ (budgeted Jd within fun η => (CLη η).apply))
            (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w
          ⟨{ s.1 with loci := (CL1).release (RUST S R) s.1.loci }, s.2⟩).1 =
      observe (CJ (budgeted Jd within fun η => (CLη η).apply))
        q (Holonics.Foundation.Chronology.transportWord
          (transportOf (blockAdj endRing)
            (CJ (budgeted Jd within fun η => (CLη η).apply))
            (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w s).1 ∧
    depositReading (budgeted Jd within fun η => (CLη η).apply)
        (Holonics.Foundation.Chronology.transportWord
          (transportOf (blockAdj endRing)
            (CJ (budgeted Jd within fun η => (CLη η).apply))
            (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w
          ⟨{ s.1 with loci := (CL1).release (RUST S R) s.1.loci }, s.2⟩).1 i =
      depositReading (budgeted Jd within fun η => (CLη η).apply)
        (Holonics.Foundation.Chronology.transportWord
          (transportOf (blockAdj endRing)
            (CJ (budgeted Jd within fun η => (CLη η).apply))
            (jointLaw_local factoredLaw_lawful.toLocal) (fun _ => hopen)) w s).1 i :=
  certified_budgeted_rust_unchanged (ge := ge) (gc := gc) hS hR hopen
    (fun ℓ h => (WordDiamond.word_diamond_retained S R ℓ).mp h) hd hb q w s hoff i

end Certified

end Holonics.HNN.JointStep

#print axioms Holonics.HNN.JointStep.jointLaw_applyRetained
#print axioms Holonics.HNN.JointStep.jointStanding
#print axioms Holonics.HNN.JointStep.step_keepAgree
#print axioms Holonics.HNN.JointStep.depositReading_of_keepAgree
#print axioms Holonics.HNN.JointStep.joint_keeps_sufficient
#print axioms Holonics.HNN.JointStep.joint_reading_unchanged
#print axioms Holonics.HNN.JointStep.joint_released_stays_released
#print axioms Holonics.HNN.JointStep.factored_equiv
#print axioms Holonics.HNN.JointStep.certified_joint_rust_collapse_sufficient
#print axioms Holonics.HNN.JointStep.certified_joint_rust_reading_unchanged
#print axioms Holonics.HNN.JointStep.budgeted_readsOnly
#print axioms Holonics.HNN.JointStep.certified_budgeted_readsOnly
#print axioms Holonics.HNN.JointStep.certified_budgeted_rust_unchanged
#print axioms Holonics.HNN.JointStep.certified_word_rust_unchanged
