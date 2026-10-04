import Holonics.HNN.JointStep

/-!
# HNN.LocusStatistics: the carried statistics and remainders stand in the locus's state

[definition] #62 (owed by `HNN/FactoredMedium` and `HNN/JointStep`: "the carried statistics and
remainders in the locus's state"). The Rust's deposit at a locus reads more than the locus's factors
(`hnn::constitution`, "Loci"):

```text
factor family x     Δh_x = Σ_t w |f_t|² ,      Δx = η_x G_x / h_x′ ,   h_x′ = h_x + Δh_x
linear locus U      ΔH_U = Σ_t w f_t f_tᵀ ,    ΔW_U = η_U Σ_t w g_t (H_U′⁻¹ f_t)ᵀ ,  X̂ ≈ H_U′⁻¹
every lattice entry its carried remainder and its clock
```

(`Constitution::{ring_scales, contact_scales}`, `NormalLaw::{gram, deposited}`,
`SolvedChart::deposited`, the carries and clocks). Each is carried at its own locus and moved only
by the data that reached it, and the release (`Constitution::release`) zeroes a released
element's and channel's factors, resets a released contrast port's Gram to its prior, keeps the
factor statistics `h_x` and drops the released loci's carried remainders and clocks.

This file puts that state in the locus's state:

* **A law with per-locus carried state** (`withState`): any law `L` on `Con` and a state `St ℓ` at
  each locus give a law on `Con × Π ℓ, St ℓ` whose operators, references, openings, receiving maps
  and reads are `L`'s, whose agreement on `ℓ` is `L`'s and the equality of the states at `ℓ`, whose
  deposit is any `A`, and whose release is `L`'s with a released locus's state replaced by
  `rel ℓ` of it (`releaseState`), any `rel`: the Rust's reset to the prior, its kept `h_x` and its
  dropped carries are each one.
* **The factored medium with carried locus state** (`carriedLaw`): each element's state `SE r` and
  each channel's `SC a` (a junction and a conductance carry none), deposited jointly with the
  factors by per-locus laws `Ψe r : ElementFactors r × SE r → data → ElementFactors r × SE r`
  (`carriedDeposit`), so a factor's move may read its locus's carried statistics, Grams, charts and
  remainders.
* **The carried step** (`carriedStep`): a family's state is its factor `x` and its statistic `h`;
  the statistic moves by the data's own terms, `h′ = h + Σ e`, and the factor by `η · X(h′, Σ g)`,
  a chart of the successor statistic applied to the summed moves. `X(h′, G) = h′⁻¹ G` is a factor
  family's step, `X(H′, G) = G H′⁻¹` a linear locus's.

[proved-derived; formal-checked] What is proved.

1. **The carried state keeps the locus map's laws** (`withState_local`, `withState_equiv`,
   `retained_withState`): the reads are `L`'s, so the retained set is `L`'s.
2. **The factored medium with carried locus state is lawful** (`carriedLaw_lawful`) for every pair
   of per-locus laws and every release of the states, and **quiet** (`carriedLaw_quiet`) for laws
   that keep a locus on empty data. Its deposit at each joint value is per-locus and quiet
   (`carried_stepLocal`, `carried_stepQuiet`).
3. **The Rust's collapse changes no face and no joint reading with the statistics in the state**
   (`carried_rust_collapse_sufficient`, `carried_rust_reading_unchanged`): with any joint reading of
   the loci the Rust's rule retains (`LocusMap.Retained S R (2|B|)`, statistics included) and of the
   staged data, releasing every other locus, its factors and its state, changes after any word no
   admitted face and no staged deposit's joint reading, a refusal included; a released locus stays
   released (`carried_released_stays_released`). The budgeted reading with its other reads over the
   word's opened diamonds is such a reading (`carried_word_readsOnly`).
4. **The carried step is quiet and keeps its metric positive** (`carriedStep_quiet`,
   `familyStatistic_pos`, `family_step_aligned`): on empty data the factor and statistic stay; a
   positive statistic with nonnegative data terms stays positive, `h′ ≥ h > 0`, so the family's unit
   step `D = G/h′` is aligned, `⟨G, D⟩ = |G|²/h′ ≥ 0`
   (`Holon/Deposition.factor_unit_step_alignment`).

[agent-inferred] An element carries several families (the passive factor and the slices; the
standing and the pair port are their own loci, `HNN/RingLoci`) and a contrast port: `SE r` is their
product and `Ψe r` steps each, so the per-locus law here is that product. The base law's own deposit
is replaced (`withState` takes `A`), so the factored law under it is taken at the identity factor
laws. The Rust deposits only at the loci data reached and moves no lattice clock or carry elsewhere,
which is the quiet hypothesis. Positivity of a linear locus's carried Gram is
`HNN/LatticeDeposit.carried_gram_posDef`.

The computational object is the helical pair interaction's medium; of the winding guide's six
general objects this touches the **pair** (a channel's carried statistics) and **faces and
placement** (the retained loci); the helix, the cell holonomy, the tube and the tower thread stay
attached.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LocusStatistics

open Holonics.HNN.Propagation Holonics.HNN.Retention Holonics.HNN.CarriedStanding
open Holonics.HNN.TickFamily Holonics.HNN.TickStanding Holonics.HNN.JointStep

/-! ## 1. A law with per-locus carried state -/

section Generic

variable {B : Type*} [Fintype B] {adj : B → B → Prop}
variable {K : Type*} [Field K] {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module K (M b)]
variable {Con Loc : Type*} {Ref : B → Type*} {Cls Λ Mo Cell Crib : Type*}
variable {St : Loc → Type*}

open Classical in
/-- [definition] **The release of the carried state**: a kept locus keeps its state, a released
locus's state becomes `rel ℓ` of it (the prior, the zero, or the state itself). -/
def releaseState (rel : ∀ ℓ, St ℓ → St ℓ) (keep : Loc → Prop) (s : ∀ ℓ, St ℓ) : ∀ ℓ, St ℓ :=
  fun ℓ => if keep ℓ then s ℓ else rel ℓ (s ℓ)

theorem releaseState_keep {rel : ∀ ℓ, St ℓ → St ℓ} {keep : Loc → Prop} (s : ∀ ℓ, St ℓ) {ℓ : Loc}
    (hk : keep ℓ) : releaseState rel keep s ℓ = s ℓ := by
  classical
  simp [releaseState, hk]

/-- [definition] **The law with per-locus carried state**: `L`'s operators, references, openings,
receiving maps and reads on the constitution, the agreement on a locus with the equality of its
state, the deposit `A` on both, and `L`'s release with `releaseState` on the states. -/
def withState (L : TickLaw K M Con Loc Ref Cls Λ Mo Cell Crib)
    (A : Con × (∀ ℓ, St ℓ) → TickStage K M Λ Mo → Con × (∀ ℓ, St ℓ))
    (rel : ∀ ℓ, St ℓ → St ℓ) : TickLaw K M (Con × ∀ ℓ, St ℓ) Loc Ref Cls Λ Mo Cell Crib where
  op c θ := L.op c θ.1
  reads := L.reads
  refReads := L.refReads
  openReads := L.openReads
  recvReads := L.recvReads
  agreeOn ℓ θ θ' := L.agreeOn ℓ θ.1 θ'.1 ∧ θ.2 ℓ = θ'.2 ℓ
  ref θ := L.ref θ.1
  recv θ := L.recv θ.1
  cls := L.cls
  openState θ := L.openState θ.1
  ticks := L.ticks
  cross := L.cross
  absorb := L.absorb
  ingestStep := L.ingestStep
  rekey := L.rekey
  apply := A
  release keep θ := (L.release keep θ.1, releaseState rel keep θ.2)

variable {L : TickLaw K M Con Loc Ref Cls Λ Mo Cell Crib}
  {A : Con × (∀ ℓ, St ℓ) → TickStage K M Λ Mo → Con × (∀ ℓ, St ℓ)} {rel : ∀ ℓ, St ℓ → St ℓ}

/-- [proved-derived; formal-checked] **The carried state keeps the local laws**: only the
agreement gains the state's equality, and the release keeps a kept locus's state. -/
theorem withState_local (hL : L.Local adj) : (withState L A rel).Local adj where
  sparse c θ := hL.sparse c θ.1
  reads_adj := hL.reads_adj
  op_reads c θ θ' y z h := hL.op_reads c θ.1 θ'.1 y z fun ℓ hr => (h ℓ hr).1
  ref_reads θ θ' b h := hL.ref_reads θ.1 θ'.1 b fun ℓ hr => (h ℓ hr).1
  open_reads θ θ' l m b h := hL.open_reads θ.1 θ'.1 l m b fun ℓ hr => (h ℓ hr).1
  recv_reads θ θ' b h := hL.recv_reads θ.1 θ'.1 b fun ℓ hr => (h ℓ hr).1
  release_keeps keep θ ℓ hk :=
    ⟨hL.release_keeps keep θ.1 ℓ hk, (releaseState_keep θ.2 hk).symm⟩

omit [Fintype B] in
/-- [proved-derived; formal-checked] The agreement with the state is an equivalence. -/
theorem withState_equiv (hE : Equiv L) : Equiv (withState L A rel) where
  refl ℓ θ := ⟨hE.refl ℓ θ.1, rfl⟩
  symm ℓ _ _ h := ⟨hE.symm ℓ _ _ h.1, h.2.symm⟩
  trans ℓ _ _ _ h₁ h₂ := ⟨hE.trans ℓ _ _ _ h₁.1 h₂.1, h₁.2.trans h₂.2⟩

omit [Fintype B] in
/-- [proved-derived; formal-checked] **The retained set is `L`'s**: the reads are. -/
theorem retained_withState {S R : Set B} {ℓ : Loc} :
    Retained adj (withState L A rel) S R ℓ ↔ Retained adj L S R ℓ := Iff.rfl

end Generic

/-! ## 2. The factored medium with carried locus state -/

section Carried

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
variable (SE : Ring → Type u) (SC : Contact → Type u)

/-- [definition] **The carried state at a locus**: an element's `SE r` (its families' statistics,
its contrast port's Gram and chart, its entries' remainders), a channel's `SC a`; a junction and a
conductance are declared and carry none. -/
def LocusSt : Locus Ring Contact → Type u
  | .element r => SE r
  | .junction _ => PUnit
  | .channel a => SC a
  | .conductance _ => PUnit

variable {SE SC}
variable {Λ Mo Cell Crib : Type*} {h₀ : ℝ}

/-- [definition] **The deposit with the carried state** (`Constitution::deposited`): each element's
factors and state move together by its own law from the data that reached it, and each channel's;
the declared operands stay. -/
def carriedDeposit
    (Ψe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r →
      EdgeData endRing V Ch → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r)
    (Ψc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a × SC a →
      EdgeData endRing V Ch → ChannelFactors (Ch := Ch) (FC := FC) a × SC a)
    (dat : Locus Ring Contact → EdgeData endRing V Ch)
    (θ : FactoredAt ρ V Ch FE FC endRing h₀ × ∀ ℓ, LocusSt SE SC ℓ) :
    FactoredAt ρ V Ch FE FC endRing h₀ × ∀ ℓ, LocusSt SE SC ℓ :=
  (⟨fdeposited (fun r p d => (Ψe r (p, θ.2 (.element r)) d).1)
      (fun a p d => (Ψc a (p, θ.2 (.channel a)) d).1) dat θ.1.1,
    declared_fdeposited θ.1.2.1, θ.1.2.2⟩,
    fun ℓ => match ℓ with
      | .element r =>
        (Ψe r ((θ.1.1.f r, θ.1.1.u r, θ.1.1.v r, θ.1.1.Wc r), θ.2 (.element r))
          (dat (.element r))).2
      | .junction r => θ.2 (.junction r)
      | .channel a =>
        (Ψc a ((θ.1.1.c a, θ.1.1.b a, θ.1.1.F a), θ.2 (.channel a)) (dat (.channel a))).2
      | .conductance a => θ.2 (.conductance a))

variable {cls : Λ → ℕ → Ring → ρ → ℝ}
  {openState : Λ → Mo → (b : Ring ⊕ Contact) → BlockM endRing V Ch b} {ticks : Λ → Mo → ℕ}
  {cross : Λ → Λ → (b : Ring ⊕ Contact) → MediumRef Ring Ch b → MediumRef Ring Ch b →
    (BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b)}
  {absorb : (b : Ring ⊕ Contact) → BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b}
  {ingestStep : Cell → Λ × Mo → Λ × Mo} {rekey : Crib → Λ → Λ}

set_option quotPrecheck false in
/-- The factored law at the identity factor laws, whose deposit the carried state replaces. -/
local notation "FL0" => factoredLaw (Cell := Cell) (Crib := Crib) h₀ cls openState ticks cross
  absorb ingestStep rekey (fun _ p _ => p) (fun _ p _ => p)

variable (h₀ cls openState ticks cross absorb ingestStep rekey) in
/-- [definition] **The factored medium with carried locus state**: the factored medium's law with
each locus's state beside its factors, deposited jointly by per-locus laws `Ψe`, `Ψc`, and released
by `rel`. -/
def carriedLaw
    (Ψe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r →
      EdgeData endRing V Ch → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r)
    (Ψc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a × SC a →
      EdgeData endRing V Ch → ChannelFactors (Ch := Ch) (FC := FC) a × SC a)
    (rel : ∀ ℓ, LocusSt SE SC ℓ → LocusSt SE SC ℓ) :
    TickLaw ℝ (BlockM endRing V Ch) (FactoredAt ρ V Ch FE FC endRing h₀ × ∀ ℓ, LocusSt SE SC ℓ)
      (Locus Ring Contact) (MediumRef Ring Ch) (Ring → ρ → ℝ) Λ Mo Cell Crib :=
  withState FL0 (fun θ d => carriedDeposit Ψe Ψc (locusOf d.edges) θ) rel

variable
  {Ψe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r →
    EdgeData endRing V Ch → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r}
  {Ψc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a × SC a →
    EdgeData endRing V Ch → ChannelFactors (Ch := Ch) (FC := FC) a × SC a}
  {rel : ∀ ℓ, LocusSt SE SC ℓ → LocusSt SE SC ℓ}

set_option quotPrecheck false in
/-- The carried law at the section's operands. -/
local notation "CL" => carriedLaw (Cell := Cell) (Crib := Crib) h₀ cls openState ticks cross
  absorb ingestStep rekey Ψe Ψc rel

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (FE r)] [∀ a, FiniteDimensional ℝ (FC a)] in
/-- [proved-derived; formal-checked] **The deposit with the carried state is local per locus**: a
locus's factors and state move from its own factors and state and the data on the edges that read
it. -/
theorem carriedDeposit_local
    {Ψe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r →
      EdgeData endRing V Ch → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r}
    {Ψc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a × SC a →
      EdgeData endRing V Ch → ChannelFactors (Ch := Ch) (FC := FC) a × SC a}
    {θ θ' : FactoredAt ρ V Ch FE FC endRing h₀ × ∀ ℓ, LocusSt SE SC ℓ}
    {d d' : EdgeData endRing V Ch} {ℓ : Locus Ring Contact}
    (hθ : FAgreeOn θ.1.1 θ'.1.1 ℓ ∧ θ.2 ℓ = θ'.2 ℓ)
    (hd : ∀ y z, Reads endRing ℓ z y → d y z = d' y z) :
    FAgreeOn (carriedDeposit Ψe Ψc (locusOf d) θ).1.1 (carriedDeposit Ψe Ψc (locusOf d') θ').1.1 ℓ ∧
      (carriedDeposit Ψe Ψc (locusOf d) θ).2 ℓ = (carriedDeposit Ψe Ψc (locusOf d') θ').2 ℓ := by
  have hdat := locusOf_congr (ℓ := ℓ) hd
  obtain ⟨hφ, hs⟩ := hθ
  cases ℓ with
  | element r =>
    obtain ⟨hf, hu, hv, hσ, hc⟩ := hφ
    have key : Ψe r ((θ.1.1.f r, θ.1.1.u r, θ.1.1.v r, θ.1.1.Wc r), θ.2 (.element r))
          (locusOf d (.element r)) =
        Ψe r ((θ'.1.1.f r, θ'.1.1.u r, θ'.1.1.v r, θ'.1.1.Wc r), θ'.2 (.element r))
          (locusOf d' (.element r)) := by
      rw [hf, hu, hv, hc, hdat]
      exact congrArg (fun s => Ψe r (_, s) _) hs
    exact ⟨⟨congrArg (fun p => p.1.1) key, congrArg (fun p => p.1.2.1) key,
      congrArg (fun p => p.1.2.2.1) key, hσ, congrArg (fun p => p.1.2.2.2) key⟩,
      congrArg Prod.snd key⟩
  | junction r => exact ⟨hφ, hs⟩
  | channel a =>
    obtain ⟨hc, hb, hF, he⟩ := hφ
    have key : Ψc a ((θ.1.1.c a, θ.1.1.b a, θ.1.1.F a), θ.2 (.channel a))
          (locusOf d (.channel a)) =
        Ψc a ((θ'.1.1.c a, θ'.1.1.b a, θ'.1.1.F a), θ'.2 (.channel a))
          (locusOf d' (.channel a)) := by
      rw [hc, hb, hF, hdat]
      exact congrArg (fun s => Ψc a (_, s) _) hs
    exact ⟨⟨congrArg (fun p => p.1.1) key, congrArg (fun p => p.1.2.1) key,
      congrArg (fun p => p.1.2.2) key, he⟩, congrArg Prod.snd key⟩
  | conductance a => exact ⟨hφ, hs⟩

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (FE r)] [∀ a, FiniteDimensional ℝ (FC a)] in
/-- [proved-derived; formal-checked] **A deposit keeps a locus no datum reaches**, factors and
state, for per-locus laws that keep a locus on empty data. -/
theorem carriedDeposit_quiet
    {Ψe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r →
      EdgeData endRing V Ch → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r}
    {Ψc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a × SC a →
      EdgeData endRing V Ch → ChannelFactors (Ch := Ch) (FC := FC) a × SC a}
    (hΨe0 : ∀ r p, Ψe r p (fun _ _ => []) = p) (hΨc0 : ∀ a p, Ψc a p (fun _ _ => []) = p)
    (θ : FactoredAt ρ V Ch FE FC endRing h₀ × ∀ ℓ, LocusSt SE SC ℓ)
    {d : EdgeData endRing V Ch} {ℓ : Locus Ring Contact}
    (h : ∀ y z, Reads endRing ℓ z y → d y z = []) :
    FAgreeOn θ.1.1 (carriedDeposit Ψe Ψc (locusOf d) θ).1.1 ℓ ∧
      θ.2 ℓ = (carriedDeposit Ψe Ψc (locusOf d) θ).2 ℓ := by
  have hdat := locusOf_quiet (ℓ := ℓ) h
  cases ℓ with
  | element r =>
    have key : Ψe r ((θ.1.1.f r, θ.1.1.u r, θ.1.1.v r, θ.1.1.Wc r), θ.2 (.element r))
        (locusOf d (.element r)) =
        ((θ.1.1.f r, θ.1.1.u r, θ.1.1.v r, θ.1.1.Wc r), θ.2 (.element r)) := by
      rw [hdat]; exact hΨe0 r _
    exact ⟨⟨(congrArg (fun p => p.1.1) key).symm, (congrArg (fun p => p.1.2.1) key).symm,
      (congrArg (fun p => p.1.2.2.1) key).symm, rfl, (congrArg (fun p => p.1.2.2.2) key).symm⟩,
      (congrArg Prod.snd key).symm⟩
  | junction r => exact ⟨rfl, rfl⟩
  | channel a =>
    have key : Ψc a ((θ.1.1.c a, θ.1.1.b a, θ.1.1.F a), θ.2 (.channel a))
        (locusOf d (.channel a)) = ((θ.1.1.c a, θ.1.1.b a, θ.1.1.F a), θ.2 (.channel a)) := by
      rw [hdat]; exact hΨc0 a _
    exact ⟨⟨(congrArg (fun p => p.1.1) key).symm, (congrArg (fun p => p.1.2.1) key).symm,
      (congrArg (fun p => p.1.2.2) key).symm, fun _ => rfl⟩, (congrArg Prod.snd key).symm⟩
  | conductance a => exact ⟨rfl, rfl⟩

/-- [proved-derived; formal-checked] **The factored medium with carried locus state is lawful**,
for every pair of per-locus laws and every release of the states. -/
theorem carriedLaw_lawful : (CL).Lawful (blockAdj endRing) :=
  { withState_local factoredLaw_lawful.toLocal with
    apply_local := fun _ _ _ _ _ hθ hd _ => carriedDeposit_local hθ fun y z hr =>
      hd y z hr }

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] The agreement with the carried state is an equivalence. -/
theorem carried_equiv : Equiv (CL) where
  refl ℓ θ := ⟨fagreeOn_refl θ.1.1 ℓ, rfl⟩
  symm ℓ θ θ' h := by
    refine ⟨?_, h.2.symm⟩
    obtain ⟨h, -⟩ := h
    cases ℓ with
    | element r => exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.1.symm, h.2.2.2.2.symm⟩
    | junction r => exact Eq.symm h
    | channel a => exact ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, fun s => (h.2.2.2 s).symm⟩
    | conductance a => exact Eq.symm h
  trans _ _ _ _ h₁ h₂ := ⟨fagreeOn_trans h₁.1 h₂.1, h₁.2.trans h₂.2⟩

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] **The carried law is quiet** for per-locus laws that keep a
locus on empty data. -/
theorem carriedLaw_quiet (hΨe0 : ∀ r p, Ψe r p (fun _ _ => []) = p)
    (hΨc0 : ∀ a p, Ψc a p (fun _ _ => []) = p) : (CL).Quiet where
  refl := carried_equiv.refl
  trans := carried_equiv.trans
  apply_quiet θ _ _ h _ := carriedDeposit_quiet hΨe0 hΨc0 θ h

/-! ### The joint step with the carried state -/

variable {Γ : Type*}
  {Ψe' : Γ → (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r →
    EdgeData endRing V Ch → ElementFactors (V := V) (FE := FE) (ρ := ρ) r × SE r}
  {Ψc' : Γ → (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a × SC a →
    EdgeData endRing V Ch → ChannelFactors (Ch := Ch) (FC := FC) a × SC a}

set_option quotPrecheck false in
/-- The deposit at each joint value `γ`: the per-locus laws at `γ`. -/
local notation "STEP" => fun (γ : Γ) (θ : FactoredAt ρ V Ch FE FC endRing h₀ ×
  ∀ ℓ, LocusSt SE SC ℓ) (d : TickStage ℝ (BlockM endRing V Ch) Λ Mo) =>
  carriedDeposit (Ψe' γ) (Ψc' γ) (locusOf d.edges) θ

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] The deposit at each joint value is per-locus. -/
theorem carried_stepLocal : StepLocal (CL) (STEP) :=
  fun _ _ _ _ _ _ hθ hd _ => carriedDeposit_local hθ fun y z hr => hd y z hr

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] The deposit at each joint value keeps a locus no datum reaches,
when every joint value's laws do. -/
theorem carried_stepQuiet (hΨe0 : ∀ γ r p, Ψe' γ r p (fun _ _ => []) = p)
    (hΨc0 : ∀ γ a p, Ψc' γ a p (fun _ _ => []) = p) : StepQuiet (CL) (STEP) :=
  fun γ θ _ _ hd _ => carriedDeposit_quiet (hΨe0 γ) (hΨc0 γ) θ hd

set_option quotPrecheck false in
-- The loci the Rust's per-locus rule retains under the continuing diamond.
local notation "RUST" S:arg R:arg =>
  LocusMap.Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact))

/-- [proved-derived; formal-checked] The loci the carried law retains are among the Rust's: its
reads are the factored medium's. -/
theorem retained_rust_carried {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {ℓ : Locus Ring Contact}
    (h : Retained (blockAdj endRing) (CL) S R ℓ) : (RUST S R) ℓ :=
  retained_rust_factored (Cell := Cell) (Crib := Crib) (h₀ := h₀) (cls := cls)
    (openState := openState) (ticks := ticks) (cross := cross) (absorb := absorb)
    (ingestStep := ingestStep) (rekey := rekey) (Ψe := fun _ p _ => p) (Ψc := fun _ p _ => p)
    hS hR (retained_withState.mp h)

/-- [proved-derived; formal-checked] **The budgeted reading with the statistics in the state reads
the retained loci alone** (`Constitution::deposited_within`; record B §8): the other reads over the
word's opened diamonds (`HNN/WordDiamond`) and the budget over the retained set, statistics
included. -/
theorem carried_word_readsOnly
    {Jd : FactoredAt ρ V Ch FE FC endRing h₀ × (∀ ℓ, LocusSt SE SC ℓ) →
      TickStage ℝ (BlockM endRing V Ch) Λ Mo → Option Γ}
    {within : FactoredAt ρ V Ch FE FC endRing h₀ × (∀ ℓ, LocusSt SE SC ℓ) → Bool}
    {S R : Set (Ring ⊕ Contact)}
    (hd : ReadsOnly (blockAdj endRing) (CL) (WordDiamond.OpenedDiamond endRing S R) Jd)
    (hb : BudgetReads (CL) (RUST S R) within) :
    ReadsOnly (blockAdj endRing) (CL) (RUST S R) (budgeted Jd within (STEP)) :=
  budgeted_readsOnly carriedLaw_lawful.toLocal
    (fun ℓ h => (WordDiamond.word_diamond_retained S R ℓ).mp h) hd hb carried_stepLocal

set_option quotPrecheck false in
-- The joint law on the carried medium.
local notation "CJ" J:arg => jointLaw (CL) J (STEP)

/-- [proved-derived; formal-checked] **The Rust's collapse changes no face with the statistics in
the state** (#62; record B §8): with the joint reading any function of the loci the Rust's rule
retains (their factors and carried statistics, Grams, charts and remainders) and of the staged data,
and the deposit at each joint value per-locus and quiet, releasing every other locus changes no
admitted face after any word. -/
theorem carried_rust_collapse_sufficient
    {J : FactoredAt ρ V Ch FE FC endRing h₀ × (∀ ℓ, LocusSt SE SC ℓ) →
      TickStage ℝ (BlockM endRing V Ch) Λ Mo → Option Γ} {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (hopen : ∀ l m, SupportedIn (openState l m) S)
    (hΨe0 : ∀ γ r p, Ψe' γ r p (fun _ _ => []) = p)
    (hΨc0 : ∀ γ a p, Ψc' γ a p (fun _ _ => []) = p)
    (hJ : ReadsOnly (blockAdj endRing) (CL) (RUST S R) J)
    (q : Option ℕ × ReceiverReading ℝ (BlockM endRing V Ch) R)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) (CJ J) S) (hoff : StagedOff (blockAdj endRing) S R s.1) :
    observe (CJ J) q (Holonics.Foundation.Chronology.transportWord
        (transportOf (blockAdj endRing) (CJ J) (jointLaw_local carriedLaw_lawful.toLocal)
          (fun _ => hopen)) w
        ⟨{ s.1 with loci := (CL).release (RUST S R) s.1.loci }, s.2⟩).1 =
      observe (CJ J) q (Holonics.Foundation.Chronology.transportWord
        (transportOf (blockAdj endRing) (CJ J) (jointLaw_local carriedLaw_lawful.toLocal)
          (fun _ => hopen)) w s).1 :=
  joint_keeps_sufficient carriedLaw_lawful.toLocal carried_equiv
    (fun _ hℓ => retained_rust_carried hS hR hℓ) hJ carried_stepLocal
    (carried_stepQuiet hΨe0 hΨc0) (fun _ => hopen) q w s hoff

/-- [proved-derived; formal-checked] **The Rust's collapse changes no joint reading with the
statistics in the state** (#62; record B §8): every staged deposit's joint reading, a refusal
included, is the same after any word whether or not the loci outside the Rust's retained set were
released. -/
theorem carried_rust_reading_unchanged
    {J : FactoredAt ρ V Ch FE FC endRing h₀ × (∀ ℓ, LocusSt SE SC ℓ) →
      TickStage ℝ (BlockM endRing V Ch) Λ Mo → Option Γ} {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (hopen : ∀ l m, SupportedIn (openState l m) S)
    (hΨe0 : ∀ γ r p, Ψe' γ r p (fun _ _ => []) = p)
    (hΨc0 : ∀ γ a p, Ψc' γ a p (fun _ _ => []) = p)
    (hJ : ReadsOnly (blockAdj endRing) (CL) (RUST S R) J)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) (CJ J) S) (hoff : StagedOff (blockAdj endRing) S R s.1)
    (i : ℕ) :
    depositReading J (Holonics.Foundation.Chronology.transportWord
        (transportOf (blockAdj endRing) (CJ J) (jointLaw_local carriedLaw_lawful.toLocal)
          (fun _ => hopen)) w
        ⟨{ s.1 with loci := (CL).release (RUST S R) s.1.loci }, s.2⟩).1 i =
      depositReading J (Holonics.Foundation.Chronology.transportWord
        (transportOf (blockAdj endRing) (CJ J) (jointLaw_local carriedLaw_lawful.toLocal)
          (fun _ => hopen)) w s).1 i :=
  joint_reading_unchanged carriedLaw_lawful.toLocal carried_equiv
    (fun _ hℓ => retained_rust_carried hS hR hℓ) hJ carried_stepLocal
    (carried_stepQuiet hΨe0 hΨc0) (fun _ => hopen) w s hoff i

/-- [proved-derived; formal-checked] **A released locus stays released with its state**: a deposit
between words never reopens a locus the collapse released, its factors and its carried state. -/
theorem carried_released_stays_released
    {J : FactoredAt ρ V Ch FE FC endRing h₀ × (∀ ℓ, LocusSt SE SC ℓ) →
      TickStage ℝ (BlockM endRing V Ch) Λ Mo → Option Γ} {S R : Set (Ring ⊕ Contact)}
    (hopen : ∀ l m, SupportedIn (openState l m) S)
    (hΨe0 : ∀ γ r p, Ψe' γ r p (fun _ _ => []) = p)
    (hΨc0 : ∀ γ a p, Ψc' γ a p (fun _ _ => []) = p)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) (CJ J) S) (h : StagedOff (blockAdj endRing) S R s.1)
    {ℓ : Locus Ring Contact} (hℓ : ¬ Retained (blockAdj endRing) (CL) S R ℓ) :
    (CL).agreeOn ℓ ((CL).release (Retained (blockAdj endRing) (CL) S R) s.1.loci)
      (Holonics.Foundation.Chronology.transportWord
        (transportOf (blockAdj endRing) (CJ J) (jointLaw_local carriedLaw_lawful.toLocal)
          (fun _ => hopen)) w
        ⟨retain (blockAdj endRing) (CJ J) S R s.1, retain_valid s.2⟩).1.loci :=
  joint_released_stays_released carriedLaw_lawful.toLocal carried_equiv
    (carried_stepQuiet hΨe0 hΨc0) (fun _ => hopen) w s h hℓ

end Carried

/-! ## 3. The carried step of a family -/

section Step

universe u

variable {Ring Contact : Type u} {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)]
  [∀ r, InnerProductSpace ℝ (V r)] {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] {endRing : Contact × Bool → Ring} [Fintype Ring]
  [Fintype Contact]

open Holonics.HNN.Word Holonics.HNN.TickBlocks Holonics.HNN.LocusMap

/-- One datum on the edge `y → z`. -/
local notation "Datum" y:arg z:arg => BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y)

/-- [definition] **The carried step of a family** (`Constitution::deposited`,
`NormalLaw::deposited`): the statistic moves by the data's own terms, `h′ = h + Σ e`, and the
factor by the joint step `η` times the chart `X` of the successor statistic applied to the summed
moves, `x′ = x + η X(h′, Σ g)`. -/
def carriedStep {P T : Type*} [AddCommGroup P] [Module ℝ P] [AddCommGroup T]
    (η : P × T → EdgeData endRing V Ch → ℝ) (X : T → P → P)
    (e : P → (y z : Ring ⊕ Contact) → Datum y z → T)
    (g : P → (y z : Ring ⊕ Contact) → Datum y z → P)
    (p : P × T) (dat : EdgeData endRing V Ch) : P × T :=
  (p.1 + η p dat • X (p.2 + ∑ y, ∑ z, ((dat y z).map (e p.1 y z)).sum)
      (∑ y, ∑ z, ((dat y z).map (g p.1 y z)).sum),
    p.2 + ∑ y, ∑ z, ((dat y z).map (e p.1 y z)).sum)

/-- [proved-derived; formal-checked] **The carried step keeps a family no datum reaches**: on empty
data the statistic stays and the summed moves are zero, so for a chart linear in the moves
(`X h 0 = 0`) the factor stays, whatever `η`. -/
theorem carriedStep_quiet {P T : Type*} [AddCommGroup P] [Module ℝ P] [AddCommGroup T]
    (η : P × T → EdgeData endRing V Ch → ℝ) {X : T → P → P} (hX : ∀ h, X h 0 = 0)
    (e : P → (y z : Ring ⊕ Contact) → Datum y z → T)
    (g : P → (y z : Ring ⊕ Contact) → Datum y z → P)
    (p : P × T) : carriedStep η X e g p (fun _ _ => []) = p := by
  simp [carriedStep, hX]

/-- [proved-derived; formal-checked] **The carried statistic stays positive**: a family's statistic
`h > 0` with nonnegative data terms (`w|f|² ≥ 0`) gives `h′ ≥ h > 0`. -/
theorem familyStatistic_pos {P : Type*} [AddCommGroup P] [Module ℝ P]
    (η : P × ℝ → EdgeData endRing V Ch → ℝ) (X : ℝ → P → P)
    {e : P → (y z : Ring ⊕ Contact) → Datum y z → ℝ} (he : ∀ x y z t, 0 ≤ e x y z t)
    (g : P → (y z : Ring ⊕ Contact) → Datum y z → P) {p : P × ℝ} (hp : 0 < p.2)
    (dat : EdgeData endRing V Ch) :
    p.2 ≤ (carriedStep η X e g p dat).2 ∧ 0 < (carriedStep η X e g p dat).2 := by
  have hsum : 0 ≤ ∑ y, ∑ z, ((dat y z).map (e p.1 y z)).sum :=
    Finset.sum_nonneg fun y _ => Finset.sum_nonneg fun z _ =>
      List.sum_nonneg fun a ha => by
        obtain ⟨t, -, rfl⟩ := List.mem_map.mp ha
        exact he _ _ _ t
  exact ⟨le_add_of_nonneg_right hsum, add_pos_of_pos_of_nonneg hp hsum⟩

/-- [proved-derived; formal-checked] **The family's unit step is aligned at its carried
statistic**: with the chart `X(h′, G) = h′⁻¹ G` the factor moves by `η` times `D = G/h′`, and a
positive statistic with nonnegative data terms gives `⟨G, D⟩ = |G|²/h′ ≥ 0`. -/
theorem family_step_aligned {P : Type*} [NormedAddCommGroup P] [InnerProductSpace ℝ P]
    (η : P × ℝ → EdgeData endRing V Ch → ℝ)
    {e : P → (y z : Ring ⊕ Contact) → Datum y z → ℝ} (he : ∀ x y z t, 0 ≤ e x y z t)
    (g : P → (y z : Ring ⊕ Contact) → Datum y z → P) {p : P × ℝ} (hp : 0 < p.2)
    (dat : EdgeData endRing V Ch) :
    (carriedStep η (fun h G => h⁻¹ • G) e g p dat).1 =
        p.1 + η p dat • ((carriedStep η (fun h G => h⁻¹ • G) e g p dat).2⁻¹ •
          ∑ y, ∑ z, ((dat y z).map (g p.1 y z)).sum) ∧
      0 ≤ inner ℝ (∑ y, ∑ z, ((dat y z).map (g p.1 y z)).sum)
        ((carriedStep η (fun h G => h⁻¹ • G) e g p dat).2⁻¹ •
          ∑ y, ∑ z, ((dat y z).map (g p.1 y z)).sum) :=
  ⟨rfl, (Holonics.HolonCore.factor_unit_step_alignment _
    (familyStatistic_pos η (fun h G => h⁻¹ • G) he g hp dat).2).2⟩

end Step

end Holonics.HNN.LocusStatistics

#print axioms Holonics.HNN.LocusStatistics.withState_local
#print axioms Holonics.HNN.LocusStatistics.withState_equiv
#print axioms Holonics.HNN.LocusStatistics.retained_withState
#print axioms Holonics.HNN.LocusStatistics.carriedDeposit_local
#print axioms Holonics.HNN.LocusStatistics.carriedDeposit_quiet
#print axioms Holonics.HNN.LocusStatistics.carriedLaw_lawful
#print axioms Holonics.HNN.LocusStatistics.carried_equiv
#print axioms Holonics.HNN.LocusStatistics.carriedLaw_quiet
#print axioms Holonics.HNN.LocusStatistics.carried_stepLocal
#print axioms Holonics.HNN.LocusStatistics.carried_stepQuiet
#print axioms Holonics.HNN.LocusStatistics.retained_rust_carried
#print axioms Holonics.HNN.LocusStatistics.carried_word_readsOnly
#print axioms Holonics.HNN.LocusStatistics.carried_rust_collapse_sufficient
#print axioms Holonics.HNN.LocusStatistics.carried_rust_reading_unchanged
#print axioms Holonics.HNN.LocusStatistics.carried_released_stays_released
#print axioms Holonics.HNN.LocusStatistics.carriedStep_quiet
#print axioms Holonics.HNN.LocusStatistics.familyStatistic_pos
#print axioms Holonics.HNN.LocusStatistics.family_step_aligned
