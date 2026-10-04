import Holonics.HNN.TickStanding
import Holonics.HNN.LocusMap

/-!
# HNN.MediumStanding: the standing law on the concrete medium

[definition] #62 (owed by `HNN/TickStanding`, "What this leaves to the instance").
`HNN/TickStanding` proves the standing law for any constitution with a per-locus agreement, under
the locus map's laws as hypotheses (`TickLaw.Lawful`, `TickLaw.Quiet`). This file is its instance
on the concrete medium of `HNN/Word` and `HNN/LocusMap`, and it proves those laws there.

* **The constitution** is an admissible `Word.Medium` at the declared tick length `h₀`
  (`MediumAt`). The tick length is declared and never released (`FieldDeclaration::step`), so the
  instance holds it fixed.
* **The operator** at the sheet classes `c` is the tick's block operator of the medium read at
  `c` (`LocusMap.withSheets`, `TickBlocks.blockOp`). The class at a lift and an absolute tick is any
  function `cls`. The medium has no resonator operand, so here `cls` reads only the sheet classes;
  the resonator's pumped edge is `HNN/LoadedRing`.
* **The loci** are `LocusMap.Locus`, read by `LocusMap.Reads` and agreed by `LocusMap.AgreeOn`.
* **The references** are those the Rust's reception carry holds (`ReceptionCarry`,
  `PowerForm::opening`): each contact's conductance `G_a` and storage `C_a` (the transmitted wave,
  `transmitted`, and the rate held at its momentum, `held_rate`). A ring holds none, since the
  medium has no resonator (`MediumRef`). So a contact block reads its channel and its conductance
  (`RefReads`).
* **The deposit** is `LocusMap.deposited`, each locus moved by its own law `Φe`, `Φc` from the
  data on the edges that read it (`locusOf`, the form of `LocusMap.locusData`).
* **The release** is `LocusMap.release`.
* **The opening and the reading read no locus**: the open state is the instance's `openState` at
  every constitution, and the receiving map is the identity (`openReads`, `recvReads` empty). The
  source ports and the receiving maps as loci are `HNN/RingLoci`.

[proved-derived; formal-checked] What is proved.

1. **The deposit keeps the medium admissible** when each locus law keeps its locus admissible
   (`deposited_admissible`). The admissibility of `Word.Medium.Admissible` splits per locus: an
   element's passive `W_s` and skew slices (`ElementAdmissible`), a channel's positive and symmetric
   `C`, `K` and positive `D` (`ChannelAdmissible`); the junctions, conductances, embeddings and tick
   length are declared and `deposited` keeps them. The Rust keeps each learned operand in factor
   form (`W_s = −f fᵀ`, `A_ρ = u_ρ v_ρᵀ − v_ρ u_ρᵀ`, `C = c cᵀ`, `K = b bᵀ`, `D = F Fᵀ`), which
   satisfies these per-locus laws for every factor step: `HNN/FactoredMedium` states the medium
   with the factors as its state and proves this file's results there for every per-locus factor
   law.
2. **The locus map's laws hold on the medium** (`mediumLaw_lawful`): every tick's operator is
   sparse (`TickBlocks.blockOp_sparse`), every reading edge is declared (`LocusMap.reads_adj`), an
   edge's operator moves only with the loci it reads (`LocusMap.blockOp_agree`), a contact's
   references only with its channel and conductance, the deposit is local per locus, and the
   release keeps what it keeps (`LocusMap.agreeOn_release`).
3. **The quiet laws hold** (`mediumLaw_quiet`) for locus laws that keep a locus on empty data,
   `LocusMap.deposit_descends`'s `hΦe`, `hΦc`: the agreement on a locus is an equivalence
   (`agreeOn_refl`, `agreeOn_symm`, `agreeOn_trans`).
4. **The standing on the medium** (`mediumStanding`) is `TickStanding.tickStanding` at this law, and
   a deposit between words never reopens a released locus (`medium_released_stays_released`).
5. **The Rust's rule is sufficient** (`rust_collapse_sufficient`). The standing law's retention
   keeps the fewest loci (`TickStanding.Retained`). Releasing any set of loci that keeps those is
   equally sufficient (`agree_release_of_keeps`, `keeps_sufficient`, for any lawful `TickLaw`). The
   Rust's per-locus rule at `e_last = 2 |B|` (`LocusMap.Retained`, `Diamond::retains` under
   `Diamond::continuing`) keeps them (`retained_rust`), when the seeded contact blocks come with
   their end rings and no receiver is a contact block, the hypotheses of
   `LocusMap.retained_of_reads`. So the collapse the Rust runs changes no admitted face of the
   current word or of any pending word after any word of generators.

What it does not cover is elsewhere: the loci with no `Word.Medium` operand (`SourcePort(g)`,
`Standing(g)`, `ReceivingMap(g)`) are `HNN/RingLoci`, and the loaded ring block joined to the
medium (the resonator's edge alone is `HNN/LoadedRing`) is `HNN/LoadedMedium`.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.MediumStanding

open Holonics.HNN.Propagation Holonics.HNN.Retention Holonics.HNN.CarriedStanding
open Holonics.HNN.TickFamily Holonics.HNN.TickStanding
open Holonics.HNN.Word Holonics.HNN.TickBlocks Holonics.HNN.LocusMap

universe u

/-! ## 1. The agreement on a locus is an equivalence -/

section Agreement

variable {Ring Contact ρ : Type u}
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)] [∀ a, InnerProductSpace ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}

theorem agreeOn_refl (μ : Medium endRing V Ch ρ) (ℓ : Locus Ring Contact) : AgreeOn μ μ ℓ := by
  cases ℓ with
  | element r => exact ⟨rfl, rfl, rfl, rfl⟩
  | junction r => exact rfl
  | channel a => exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  | conductance a => exact rfl

theorem agreeOn_symm {μ μ' : Medium endRing V Ch ρ} {ℓ : Locus Ring Contact}
    (h : AgreeOn μ μ' ℓ) : AgreeOn μ' μ ℓ := by
  cases ℓ with
  | element r => exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
  | junction r => exact Eq.symm h
  | channel a => exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun s => (h.2.2.2 s).symm⟩
  | conductance a => exact Eq.symm h

theorem agreeOn_trans {μ₁ μ₂ μ₃ : Medium endRing V Ch ρ} {ℓ : Locus Ring Contact}
    (h₁ : AgreeOn μ₁ μ₂ ℓ) (h₂ : AgreeOn μ₂ μ₃ ℓ) : AgreeOn μ₁ μ₃ ℓ := by
  cases ℓ with
  | element r =>
    exact ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1, h₁.2.2.2.trans h₂.2.2.2⟩
  | junction r => exact Eq.trans h₁ h₂
  | channel a =>
    exact ⟨h₁.1.trans h₂.1, h₁.2.1.trans h₂.2.1, h₁.2.2.1.trans h₂.2.2.1,
      fun s => (h₁.2.2.2 s).trans (h₂.2.2.2 s)⟩
  | conductance a => exact Eq.trans h₁ h₂

end Agreement

/-! ## 2. The deposit keeps the medium admissible -/

section Admissible

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}

/-- [definition] **An element's learned operands are admissible**: `W_s` passive and every slice
skew (`Medium.Admissible.Ws_passive`, `A_skew`). -/
def ElementAdmissible {r : Ring} (p : (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r)) :
    Prop :=
  (∀ v, inner ℝ v (p.1 v) ≤ 0) ∧ ∀ i v, inner ℝ v (p.2.1 i v) = 0

/-- [definition] **A channel's learned operands are admissible**: `C`, `D`, `K` positive and `C`,
`K` symmetric (`Medium.Admissible.C_psd`, `D_psd`, `K_psd`, `C_symm`, `K_symm`). -/
def ChannelAdmissible {a : Contact}
    (p : (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a)) : Prop :=
  (∀ v, 0 ≤ inner ℝ v (p.1 v)) ∧ (∀ v, 0 ≤ inner ℝ v (p.2.1 v)) ∧ (∀ v, 0 ≤ inner ℝ v (p.2.2 v)) ∧
    (∀ x y, inner ℝ (p.1 x) y = inner ℝ x (p.1 y)) ∧
      ∀ x y, inner ℝ (p.2.2 x) y = inner ℝ x (p.2.2 y)

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ] in
theorem element_admissible {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (r : Ring) :
    ElementAdmissible (μ.Ws r, μ.A r, μ.Wc r) :=
  ⟨hμ.Ws_passive r, hμ.A_skew r⟩

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ] in
theorem channel_admissible {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (a : Contact) :
    ChannelAdmissible (μ.C a, μ.D a, μ.K a) :=
  ⟨hμ.C_psd a, hμ.D_psd a, hμ.K_psd a, hμ.C_symm a, hμ.K_symm a⟩

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ] in
/-- [proved-derived; formal-checked] **The deposit keeps the medium admissible** when each locus
law keeps its locus admissible: the declared operands stay, and the learned ones are each moved by
their own law (`Constitution::deposited`). -/
theorem deposited_admissible
    {Φe : (r : Ring) → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r) →
      EdgeData endRing V Ch → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r)}
    {Φc : (a : Contact) → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) →
      EdgeData endRing V Ch → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a)}
    (hΦe : ∀ r p dat, ElementAdmissible p → ElementAdmissible (Φe r p dat))
    (hΦc : ∀ a p dat, ChannelAdmissible p → ChannelAdmissible (Φc a p dat))
    {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    (dat : Locus Ring Contact → EdgeData endRing V Ch) :
    (deposited Φe Φc dat μ).Admissible where
  Ws_passive r := (hΦe r _ _ (element_admissible hμ r)).1
  A_skew r := (hΦe r _ _ (element_admissible hμ r)).2
  C_psd a := (hΦc a _ _ (channel_admissible hμ a)).1
  D_psd a := (hΦc a _ _ (channel_admissible hμ a)).2.1
  K_psd a := (hΦc a _ _ (channel_admissible hμ a)).2.2.1
  C_symm a := (hΦc a _ _ (channel_admissible hμ a)).2.2.2.1
  K_symm a := (hΦc a _ _ (channel_admissible hμ a)).2.2.2.2
  Y_pos := hμ.Y_pos
  G_pos := hμ.G_pos
  h_pos := hμ.h_pos
  channel := hμ.channel

end Admissible

/-! ## 3. The law on the medium -/

section Law

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}

variable (endRing V Ch ρ) in
/-- [definition] **The constitution**: an admissible medium at the declared tick length `h₀`. -/
def MediumAt (h₀ : ℝ) : Type u := {μ : Medium endRing V Ch ρ // μ.Admissible ∧ μ.h = h₀}

variable (Ring Ch) in
/-- [definition] **The references a block holds** (`ReceptionCarry`): a contact's conductance and
storage; a ring none, since the medium has no resonator. -/
def MediumRef : Ring ⊕ Contact → Type u
  | .inl _ => PUnit.{u + 1}
  | .inr a => ULift.{u} ℝ × (Ch a →L[ℝ] Ch a)

/-- [definition] The references of a medium. -/
def mediumRef (μ : Medium endRing V Ch ρ) : (b : Ring ⊕ Contact) → MediumRef Ring Ch b
  | .inl _ => PUnit.unit
  | .inr a => (ULift.up (μ.G a), μ.C a)

/-- [definition] **The loci a block's references read**: a contact block reads its channel and its
conductance. -/
def RefReads : Locus Ring Contact → Ring ⊕ Contact → Prop
  | .element _, _ => False
  | .junction _, _ => False
  | .channel a, b => b = .inr a
  | .conductance a, b => b = .inr a

open Classical in
/-- [definition] **The data a locus deposits from**: the staged data on the edges that read it
(`LocusMap.locusData`). -/
def locusOf (d : EdgeData endRing V Ch) (ℓ : Locus Ring Contact) : EdgeData endRing V Ch :=
  fun y z => if Reads endRing ℓ z y then d y z else []

variable {Λ Mo Cell Crib : Type*}

/-- [definition] **The law on the medium**: the block operator at the sheet classes, the locus map,
the references of the reception carry, the per-locus deposit and the release; the class at a lift
and an absolute tick, the moment's open state, the word's ticks, the crossing, the absorption, the
ingest and the re-keying are the instance's. -/
def mediumLaw (h₀ : ℝ) (cls : Λ → ℕ → Ring → ρ → ℝ)
    (openState : Λ → Mo → (b : Ring ⊕ Contact) → BlockM endRing V Ch b) (ticks : Λ → Mo → ℕ)
    (cross : Λ → Λ → (b : Ring ⊕ Contact) → MediumRef Ring Ch b → MediumRef Ring Ch b →
      (BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b))
    (absorb : (b : Ring ⊕ Contact) → BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b)
    (ingestStep : Cell → Λ × Mo → Λ × Mo) (rekey : Crib → Λ → Λ)
    {Φe : (r : Ring) → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r) →
      EdgeData endRing V Ch → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r)}
    {Φc : (a : Contact) → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) →
      EdgeData endRing V Ch → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a)}
    (hΦe : ∀ r p dat, ElementAdmissible p → ElementAdmissible (Φe r p dat))
    (hΦc : ∀ a p dat, ChannelAdmissible p → ChannelAdmissible (Φc a p dat)) :
    TickLaw ℝ (BlockM endRing V Ch) (MediumAt ρ V Ch endRing h₀) (Locus Ring Contact)
      (MediumRef Ring Ch) (Ring → ρ → ℝ) Λ Mo Cell Crib where
  op c θ := blockOp (withSheets_admissible θ.2.1 c)
  reads := Reads endRing
  refReads := RefReads
  openReads _ _ := False
  recvReads _ _ := False
  agreeOn ℓ θ θ' := AgreeOn θ.1 θ'.1 ℓ
  ref θ := mediumRef θ.1
  recv _ _ := LinearMap.id
  cls := cls
  openState _ := openState
  ticks := ticks
  cross := cross
  absorb := absorb
  ingestStep := ingestStep
  rekey := rekey
  apply θ d := ⟨deposited Φe Φc (locusOf d) θ.1, deposited_admissible hΦe hΦc θ.2.1 _, θ.2.2⟩
  release keep θ := ⟨release keep θ.1, release_admissible θ.2.1 keep, θ.2.2⟩

variable {h₀ : ℝ} {cls : Λ → ℕ → Ring → ρ → ℝ}
  {openState : Λ → Mo → (b : Ring ⊕ Contact) → BlockM endRing V Ch b} {ticks : Λ → Mo → ℕ}
  {cross : Λ → Λ → (b : Ring ⊕ Contact) → MediumRef Ring Ch b → MediumRef Ring Ch b →
    (BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b)}
  {absorb : (b : Ring ⊕ Contact) → BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b}
  {ingestStep : Cell → Λ × Mo → Λ × Mo} {rekey : Crib → Λ → Λ}
  {Φe : (r : Ring) → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r) →
    EdgeData endRing V Ch → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r)}
  {Φc : (a : Contact) → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) →
    EdgeData endRing V Ch → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a)}
  (hΦe : ∀ r p dat, ElementAdmissible p → ElementAdmissible (Φe r p dat))
  (hΦc : ∀ a p dat, ChannelAdmissible p → ChannelAdmissible (Φc a p dat))

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem locusOf_congr {d d' : EdgeData endRing V Ch} {ℓ : Locus Ring Contact}
    (h : ∀ y z, Reads endRing ℓ z y → d y z = d' y z) : locusOf d ℓ = locusOf d' ℓ := by
  classical
  funext y z
  simp only [locusOf]
  split_ifs with hr
  · exact h y z hr
  · rfl

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem locusOf_quiet {d : EdgeData endRing V Ch} {ℓ : Locus Ring Contact}
    (h : ∀ y z, Reads endRing ℓ z y → d y z = []) : locusOf d ℓ = fun _ _ => [] := by
  classical
  funext y z
  simp only [locusOf]
  split_ifs with hr
  · exact h y z hr
  · rfl

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
/-- [proved-derived; formal-checked] **The deposit is local per locus**: two media agreeing on a
locus, deposited with data agreeing on every edge that reads it, agree on it. -/
theorem deposited_local {μ μ' : Medium endRing V Ch ρ} {d d' : EdgeData endRing V Ch}
    {ℓ : Locus Ring Contact} (hμ : AgreeOn μ μ' ℓ)
    (hd : ∀ y z, Reads endRing ℓ z y → d y z = d' y z) :
    AgreeOn (deposited Φe Φc (locusOf d) μ) (deposited Φe Φc (locusOf d') μ') ℓ := by
  have hdat := locusOf_congr (ℓ := ℓ) hd
  cases ℓ with
  | element r =>
    obtain ⟨hW, hA, hσ, hc⟩ := hμ
    have key : Φe r (μ.Ws r, μ.A r, μ.Wc r) (locusOf d (.element r)) =
        Φe r (μ'.Ws r, μ'.A r, μ'.Wc r) (locusOf d' (.element r)) := by rw [hW, hA, hc, hdat]
    exact ⟨congrArg Prod.fst key, congrArg (fun p => p.2.1) key, hσ, congrArg (fun p => p.2.2) key⟩
  | junction r => exact hμ
  | channel a =>
    obtain ⟨hC, hD, hK, he⟩ := hμ
    have key : Φc a (μ.C a, μ.D a, μ.K a) (locusOf d (.channel a)) =
        Φc a (μ'.C a, μ'.D a, μ'.K a) (locusOf d' (.channel a)) := by rw [hC, hD, hK, hdat]
    exact ⟨congrArg Prod.fst key, congrArg (fun p => p.2.1) key, congrArg (fun p => p.2.2) key, he⟩
  | conductance a => exact hμ

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
/-- [proved-derived; formal-checked] **A deposit keeps a locus no datum reaches**, for locus laws
that keep a locus on empty data. -/
theorem deposited_quiet
    (hΦe0 : ∀ r p, Φe r p (fun _ _ => []) = p) (hΦc0 : ∀ a p, Φc a p (fun _ _ => []) = p)
    (μ : Medium endRing V Ch ρ) {d : EdgeData endRing V Ch} {ℓ : Locus Ring Contact}
    (h : ∀ y z, Reads endRing ℓ z y → d y z = []) :
    AgreeOn μ (deposited Φe Φc (locusOf d) μ) ℓ := by
  have hdat := locusOf_quiet (ℓ := ℓ) h
  cases ℓ with
  | element r =>
    have key : Φe r (μ.Ws r, μ.A r, μ.Wc r) (locusOf d (.element r)) = (μ.Ws r, μ.A r, μ.Wc r) := by
      rw [hdat, hΦe0]
    exact ⟨(congrArg Prod.fst key).symm, (congrArg (fun p => p.2.1) key).symm, rfl,
      (congrArg (fun p => p.2.2) key).symm⟩
  | junction r => exact rfl
  | channel a =>
    have key : Φc a (μ.C a, μ.D a, μ.K a) (locusOf d (.channel a)) = (μ.C a, μ.D a, μ.K a) := by
      rw [hdat, hΦc0]
    exact ⟨(congrArg Prod.fst key).symm, (congrArg (fun p => p.2.1) key).symm,
      (congrArg (fun p => p.2.2) key).symm, fun _ => rfl⟩
  | conductance a => exact rfl

/-- [proved-derived; formal-checked] **The locus map's laws hold on the medium.** -/
theorem mediumLaw_lawful :
    (mediumLaw (Cell := Cell) (Crib := Crib) h₀ cls openState ticks cross absorb ingestStep rekey
      hΦe hΦc).Lawful (blockAdj endRing) where
  sparse c θ := blockOp_sparse _
  reads_adj ℓ z y h := LocusMap.reads_adj h
  op_reads c θ θ' y z h :=
    blockOp_agree (withSheets_admissible θ.2.1 c) (withSheets_admissible θ'.2.1 c)
      (θ.2.2.trans θ'.2.2.symm) fun ℓ hr => agreeOn_withSheets (h ℓ hr) c
  ref_reads θ θ' b h := by
    cases b with
    | inl r => rfl
    | inr a =>
      have hG : θ.1.G a = θ'.1.G a := h (.conductance a) rfl
      have hC : θ.1.C a = θ'.1.C a := (h (.channel a) rfl).1
      show (ULift.up (θ.1.G a), θ.1.C a) = (ULift.up (θ'.1.G a), θ'.1.C a)
      rw [hG, hC]
  open_reads _ _ _ _ _ _ := rfl
  recv_reads _ _ _ _ := rfl
  apply_local θ θ' d d' ℓ hθ hd := deposited_local hθ hd
  release_keeps keep θ ℓ hk := agreeOn_symm (agreeOn_release hk)

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] **The quiet laws hold on the medium** for locus laws that keep
a locus on empty data. -/
theorem mediumLaw_quiet
    (hΦe0 : ∀ r p, Φe r p (fun _ _ => []) = p) (hΦc0 : ∀ a p, Φc a p (fun _ _ => []) = p) :
    (mediumLaw (Cell := Cell) (Crib := Crib) h₀ cls openState ticks cross absorb ingestStep rekey
      hΦe hΦc).Quiet where
  refl ℓ θ := agreeOn_refl θ.1 ℓ
  trans _ _ _ _ h₁ h₂ := agreeOn_trans h₁ h₂
  apply_quiet θ _ _ h := deposited_quiet hΦe0 hΦc0 θ.1 h

end Law

/-! ## 4. Any release that keeps the retained loci is sufficient -/

section Keeps

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
variable {Con Loc : Type*} {Ref : B → Type*} {Cls Λ Mo Cell Crib : Type*}
variable {L : TickLaw K M Con Loc Ref Cls Λ Mo Cell Crib}

/-- [proved-derived; formal-checked] Releasing every locus outside a set that keeps the retained
loci leaves the resident in agreement. -/
theorem agree_release_of_keeps (hL : L.Lawful adj) {S R : Set B} {keep : Loc → Prop}
    (hk : ∀ ℓ, TickStanding.Retained adj L S R ℓ → keep ℓ)
    (res : TickResident K M Con Ref Λ Mo) :
    Agree adj L S R res { res with loci := L.release keep res.loci } := by
  refine ⟨fun ℓ hℓ => hL.release_keeps keep res.loci ℓ (hk ℓ hℓ), rfl, rfl, carryAgree_refl _, ?_,
    ?_⟩
  · exact forall₂_self (s := TickStanding.PendAgree adj S R)
      (fun _ => ⟨rfl, rfl, carryAgree_refl _⟩) _
  · exact forall₂_self (s := TickStanding.StagedAgree adj) (fun _ _ _ _ => rfl) res.staged

/-- [proved-derived; formal-checked] **Any release that keeps the retained loci is sufficient**:
after any word of the generators, every admitted face of the current word and of every pending word
reads the same on the released resident as on the resident. -/
theorem keeps_sufficient (hL : L.Lawful adj) {S R : Set B}
    (hopen : ∀ θ l m, SupportedIn (L.openState θ l m) S) {keep : Loc → Prop}
    (hk : ∀ ℓ, TickStanding.Retained adj L S R ℓ → keep ℓ)
    (q : Option ℕ × ReceiverReading K M R) (w : List (CarryGen Cell Crib (ReceiverFamily K M R)))
    (s : ValidResident adj L S) :
    observe L q (Holonics.Foundation.Chronology.transportWord (transport adj L hL hopen) w
        ⟨{ s.1 with loci := L.release keep s.1.loci }, s.2⟩).1 =
      observe L q (Holonics.Foundation.Chronology.transportWord (transport adj L hL hopen) w s).1 :=
  (observe_agree hL hopen q (Subtype.property _) (Subtype.property _)
    (transportWord_agree (s := s) (s' := ⟨{ s.1 with loci := L.release keep s.1.loci }, s.2⟩)
      hL hopen w (agree_release_of_keeps hL hk s.1))).symm

end Keeps

/-! ## 5. The standing on the medium, and the Rust's rule -/

section Standing

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}
variable {Λ Mo Cell Crib : Type*}
variable {h₀ : ℝ} {cls : Λ → ℕ → Ring → ρ → ℝ}
  {openState : Λ → Mo → (b : Ring ⊕ Contact) → BlockM endRing V Ch b} {ticks : Λ → Mo → ℕ}
  {cross : Λ → Λ → (b : Ring ⊕ Contact) → MediumRef Ring Ch b → MediumRef Ring Ch b →
    (BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b)}
  {absorb : (b : Ring ⊕ Contact) → BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b}
  {ingestStep : Cell → Λ × Mo → Λ × Mo} {rekey : Crib → Λ → Λ}
  {Φe : (r : Ring) → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r) →
    EdgeData endRing V Ch → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r)}
  {Φc : (a : Contact) → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) →
    EdgeData endRing V Ch → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a)}
  {hΦe : ∀ r p dat, ElementAdmissible p → ElementAdmissible (Φe r p dat)}
  {hΦc : ∀ a p dat, ChannelAdmissible p → ChannelAdmissible (Φc a p dat)}

/-- The medium's law at the section's operands. -/
local notation "ML" => mediumLaw (Cell := Cell) (Crib := Crib) h₀ cls openState ticks cross absorb
  ingestStep rekey hΦe hΦc

/-- [proved-derived; formal-checked] **The standing on the concrete medium** (#62): the tick-indexed
standing law of `HNN/TickStanding` at the medium's law. -/
def mediumStanding {S R : Set (Ring ⊕ Contact)} (hopen : ∀ l m, SupportedIn (openState l m) S) :
    Holonics.Foundation.Standing.StandingLaw
      (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R))
      (Option ℕ × ReceiverReading ℝ (BlockM endRing V Ch) R) (ValidResident (blockAdj endRing) ML S)
      (ValidResident (blockAdj endRing) ML S) ℝ :=
  tickStanding (L := ML) (adj := blockAdj endRing) (S := S) (R := R) (mediumLaw_lawful hΦe hΦc)
    (fun _ => hopen)

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] The law's release is `LocusMap.release`. -/
theorem mediumLaw_release (keep : Locus Ring Contact → Prop) (θ : MediumAt ρ V Ch endRing h₀) :
    ((ML).release keep θ).1 = release keep θ.1 := rfl

/-- [proved-derived; formal-checked] **On the medium a deposit between words never reopens a
released locus**, for locus laws that keep a locus on empty data. -/
theorem medium_released_stays_released
    (hΦe0 : ∀ r p, Φe r p (fun _ _ => []) = p) (hΦc0 : ∀ a p, Φc a p (fun _ _ => []) = p)
    {S R : Set (Ring ⊕ Contact)} (hopen : ∀ l m, SupportedIn (openState l m) S)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) ML S)
    (h : StagedOff (blockAdj endRing) S R s.1) {ℓ : Locus Ring Contact}
    (hℓ : ¬ TickStanding.Retained (blockAdj endRing) ML S R ℓ) :
    AgreeOn (release (TickStanding.Retained (blockAdj endRing) ML S R) s.1.loci.1)
      (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) ML (mediumLaw_lawful hΦe hΦc) (fun _ => hopen)) w
        ⟨retain (blockAdj endRing) ML S R s.1, retain_valid s.2⟩).1.loci.1 ℓ :=
  released_stays_released (mediumLaw_lawful hΦe hΦc) (mediumLaw_quiet hΦe hΦc hΦe0 hΦc0)
    (fun _ => hopen) w s h hℓ

/-- [proved-derived; formal-checked] **The Rust's rule keeps the retained loci.** Under
`Diamond::continuing` (`e_last = 2 |B|`), when the seeded contact blocks come with their end rings
and no receiver is a contact block, every locus the standing law retains is retained by
`Diamond::retains` (`LocusMap.Retained`): a locus read on a walk edge by `retained_of_reads`, a
contact's channel and conductance read by its references on a walk block by `channel_of_edge`. -/
theorem retained_rust {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {ℓ : Locus Ring Contact}
    (h : TickStanding.Retained (blockAdj endRing) ML S R ℓ) :
    LocusMap.Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact)) ℓ := by
  rcases h with ⟨z, y, hr, hw⟩ | ⟨b, hrb, hreach, hobs⟩ | ⟨b, hrb, -⟩ | ⟨b, hrb, -⟩
  · exact retained_of_reads hS hR hr ((inDiamond_continuing_iff S R z y).mpr hw)
  · have hd := (inDiamond_continuing_iff (adj := blockAdj endRing) S R b b).mpr ⟨hreach, hobs⟩
    cases ℓ with
    | element r => exact absurd hrb id
    | junction r => exact absurd hrb id
    | channel a =>
      obtain rfl : b = .inr a := hrb
      exact channel_of_edge hS hR (Or.inl rfl) (Or.inl rfl) hd
    | conductance a =>
      obtain rfl : b = .inr a := hrb
      exact Or.inl (channel_of_edge hS hR (Or.inl rfl) (Or.inl rfl) hd)
  · exact absurd hrb id
  · exact absurd hrb id

/-- [proved-derived; formal-checked] **The collapse the Rust runs is sufficient on the medium**
(`hnn::retention::collapse` under `Diamond::continuing`). Releasing every locus the Rust's
per-locus rule does not retain at `e_last = 2 |B|` (`LocusMap.release` at `LocusMap.Retained`,
`mediumLaw_release`) changes no admitted face of the current word or of any pending word, after any
word of the generators. -/
theorem rust_collapse_sufficient {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (hopen : ∀ l m, SupportedIn (openState l m) S)
    (q : Option ℕ × ReceiverReading ℝ (BlockM endRing V Ch) R)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) ML S) :
    observe ML q (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) ML (mediumLaw_lawful hΦe hΦc) (fun _ => hopen)) w
        ⟨{ s.1 with loci := (ML).release (LocusMap.Retained endRing S R
            (2 * Fintype.card (Ring ⊕ Contact))) s.1.loci }, s.2⟩).1 =
      observe ML q (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) ML (mediumLaw_lawful hΦe hΦc) (fun _ => hopen)) w s).1 :=
  keeps_sufficient (mediumLaw_lawful hΦe hΦc) (fun _ => hopen)
    (fun _ hℓ => retained_rust hS hR hℓ) q w s

end Standing

end Holonics.HNN.MediumStanding

#print axioms Holonics.HNN.MediumStanding.deposited_admissible
#print axioms Holonics.HNN.MediumStanding.mediumLaw_lawful
#print axioms Holonics.HNN.MediumStanding.mediumLaw_quiet
#print axioms Holonics.HNN.MediumStanding.mediumStanding
#print axioms Holonics.HNN.MediumStanding.mediumLaw_release
#print axioms Holonics.HNN.MediumStanding.medium_released_stays_released
#print axioms Holonics.HNN.MediumStanding.keeps_sufficient
#print axioms Holonics.HNN.MediumStanding.retained_rust
#print axioms Holonics.HNN.MediumStanding.rust_collapse_sufficient
