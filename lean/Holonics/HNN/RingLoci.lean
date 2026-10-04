import Holonics.HNN.FactoredMedium

/-!
# HNN.RingLoci: a ring's standing, source port and receiving map as loci

[definition] #62 (owed by `HNN/LocusMap` and `HNN/FactoredMedium`: the `Standing(g)`,
`SourcePort(g)` and `ReceivingMap(g)` loci, which have no operand on `Word.Medium`). Each enters the
word at its own place (`hnn::constitution::Locus`, `hnn::retention::Diamond::retains`):

```text
Standing(g)      q_g      the element's sheet classes, through the lock chart
                          Δ_r = −q_r + Σ_(a at r) T_a q_(other end of a),  σ_(r,ρ) = sign Δ_(r,ρ)
                          kept when element(g) or element(neighbour) is      (Diamond::standing)
SourcePort(g)    E_g      the opening at a source ring: x_0(g) = E_g u_g
                          kept when is_source(g) and o_g ≤ e                  (Diamond::source_port)
ReceivingMap(g)  R_g      the receiver's reading: ⟨p, R_g x⟩ = ⟨R_gᵀ p, x⟩
                          kept when g is the receiver, never released          (retention::retained)
```

* **The lock chart** (`LockChart`) is a linear map from ring `r`'s standing (`self r`) and, for
  every contact end `e` at `r`, one from the standing at the contact's other end (`across e`). The
  contrast (`contrast`) is their sum, the sheet classes (`sheets`) its sign with `sign 0 = +1`
  (`HNN/Normal.sheetClass`'s rule). Ring `g` is **near** ring `r` (`Near`) when `g = r` or a
  contact joins them.
* **The constitution** (`RingsAt`) is a factored medium (`HNN/FactoredMedium.FactoredAt`) with,
  per ring, a standing `q_g ∈ Q g`, a source port `E_g : U g → M(g)` and a receiving map read on
  covectors `R_gᵀ : M(g)* → M(g)*`. Its operator is the tick's block operator at the classes the
  standings give (`sheets χ q`), not at a clock-read class: the medium has no operand that the
  clock reads apart from the pump, which is the loaded ring's (`HNN/LoadedRing`), so the class
  here is `Unit`.
* **The opening** at a ring `g` of the declared sources `Src` is `E_g` applied to the moment's
  source input `u_g` (`src`), and zero elsewhere (`ringOpen`). **The reading** at ring `g` is the
  covector read through `R_gᵀ`, and the identity at a contact block (`ringRecv`).
* **The loci** (`RLocus`) are `LocusMap.Locus` and the three ring loci. A standing is read on the
  element edge `r → r` of every ring `r` near `g`; a source port by the opening at its ring when it
  is a source, and its deposit reads that ring's element edge; a receiving map by the reading at its
  ring, and its deposit reads that ring's element edge (`RReads`, `ROpenReads`, `RRecvReads`).
* **The deposit** moves the factors as in `FactoredMedium` and each ring locus by its own law
  from the data on the edges that read it (`ringData`). **The release** zeroes a released ring
  locus and releases the factors as in `FactoredMedium`.

[proved-derived; formal-checked] What is proved.

1. **The classes read only the near standings** (`contrast_congr`, `sheets_congr`).
2. **The locus map's laws hold** (`ringLaw_lawful`) for every factor law and every ring-locus
   law, with the opening's and the reading's laws (`TickLaw.Lawful.open_reads`, `recv_reads`), and
   **the quiet laws** (`ringLaw_quiet`) for laws that keep a locus on empty data.
3. **The opening is supported on the sources** (`ringOpen_supported`) when every declared source
   ring is seeded, so the standing law holds (`ringStanding`), and released loci stay released
   (`ring_released_stays_released`).
4. **The Rust's rule keeps the retained loci** (`retained_rust_ring`) at `e_last = 2|B|`:
   * a standing read on a walk edge `r → r` has `r` near `g`, whose element is in the diamond;
   * a source port is read at a source ring that observes a receiver (directly, or on its walk
     edge), so `is_source(g)` and `o_g ≤ e`;
   * the Rust keeps every receiving map (`retention::retained`, `Constitution::release`), and the
     standing law's own rule retains the receiver's (`retained_receiver`, `Diamond::retains`).
   Hence **the Rust's collapse is sufficient for every per-locus law**
   (`ring_rust_collapse_sufficient`).
5. **Under the certified step released loci stay released with no hypothesis**
   (`certified_ring_released_stays_released`): every ring locus's step has the certified step's
   form (`FactoredMedium.certifiedStep`), which is quiet on empty data.

[agent-inferred] The Rust's source-port step reads the source input `u`, and the staged data on an
edge carry the state and the swept covector, not `u`; here a source port's deposit is any function
of its own state and the data on its ring's element edge. A deposit that also reads the moment
needs the moment in the staged deposit, which `HNN/TickStanding` does not stage; owed in #62.

[open] Each ring-locus law here is a function of the locus's own state and its data. The Rust's
steps at these loci share the deposit's joint certified step, whose scalar reads the medium's reach
(`HNN/FactoredMedium`, module header [open]), so they are not yet per-locus laws. The joint step on
retained loci, with the carried statistics in the locus's state, is owed in #62.

[open] The loaded ring block joined to the medium, so that the class reads the pump's phase, is
owed in #62.

`HNN/FactoredMedium`, `HNN/MediumStanding` and `HNN/LocusMap` are unchanged in their laws. No
`sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.RingLoci

open Holonics.HNN.Propagation Holonics.HNN.Retention Holonics.HNN.CarriedStanding
open Holonics.HNN.TickFamily Holonics.HNN.TickStanding
open Holonics.HNN.Word Holonics.HNN.TickBlocks Holonics.HNN.LocusMap
open Holonics.HNN.MediumStanding Holonics.HNN.FactoredMedium

universe u

/-! ## 1. The lock chart and the sheet classes -/

section Chart

variable {Ring Contact ρ : Type u} [Fintype Contact] [DecidableEq Ring]
variable {Q : Ring → Type u} [∀ g, AddCommGroup (Q g)] [∀ g, Module ℝ (Q g)]
variable {endRing : Contact × Bool → Ring}

variable (endRing ρ Q) in
/-- [definition] **The lock chart** (`hnn::constitution::LockChart`), read on the incidence: ring
`r`'s own standing enters `Δ_r` by `self r` (the Rust's `−1` at `(r, ρ)`), and the standing at the
other end of contact end `e` by `across e` (the Rust's `T_a` forward at the `from` end, transposed
at the `to` end). -/
structure LockChart where
  self : (r : Ring) → Q r →ₗ[ℝ] (ρ → ℝ)
  across : (e : Contact × Bool) → Q (endRing (e.1, !e.2)) →ₗ[ℝ] (ρ → ℝ)

/-- [definition] **The contrast** `Δ_r` at the standings `q`. -/
def contrast (χ : LockChart ρ Q endRing) (q : (g : Ring) → Q g) (r : Ring) : ρ → ℝ :=
  χ.self r (q r) +
    ∑ e : Contact × Bool, if endRing e = r then χ.across e (q (endRing (e.1, !e.2))) else 0

/-- [definition] **The sheet classes** `σ_(r,ρ) = sign Δ_(r,ρ)`, with `sign 0 = +1`. -/
def sheets (χ : LockChart ρ Q endRing) (q : (g : Ring) → Q g) (r : Ring) (i : ρ) : ℝ :=
  if 0 ≤ contrast χ q r i then 1 else -1

variable (endRing) in
/-- [definition] **Ring `g` is near ring `r`**: it is `r`, or the other end of a contact at `r`. -/
def Near (g r : Ring) : Prop :=
  g = r ∨ ∃ e : Contact × Bool, endRing e = r ∧ endRing (e.1, !e.2) = g

/-- [proved-derived; formal-checked] **The contrast reads only the near standings.** -/
theorem contrast_congr {χ : LockChart ρ Q endRing} {q q' : (g : Ring) → Q g} {r : Ring}
    (h : ∀ g, Near endRing g r → q g = q' g) : contrast χ q r = contrast χ q' r := by
  unfold contrast
  rw [h r (Or.inl rfl)]
  congr 1
  refine Finset.sum_congr rfl fun e _ => ?_
  split_ifs with he
  · rw [h _ (Or.inr ⟨e, he, rfl⟩)]
  · rfl

/-- [proved-derived; formal-checked] **The classes read only the near standings.** -/
theorem sheets_congr {χ : LockChart ρ Q endRing} {q q' : (g : Ring) → Q g} {r : Ring}
    (h : ∀ g, Near endRing g r → q g = q' g) : sheets χ q r = sheets χ q' r := by
  funext i
  simp only [sheets, contrast_congr h]

end Chart

/-! ## 2. The loci with the ring loci -/

section Loci

variable {Ring Contact : Type u}

variable (Ring Contact) in
/-- [definition] **The loci with the ring loci**: those of `LocusMap.Locus`, and ring `g`'s
standing `q_g`, source port `E_g` and receiving map `R_g` (`hnn::constitution::Locus`). -/
inductive RLocus
  | base (ℓ : Locus Ring Contact)
  | standing (g : Ring)
  | sourcePort (g : Ring)
  | receivingMap (g : Ring)

variable (endRing : Contact × Bool → Ring) (Src : Set Ring)

/-- [definition] **The block edges that read a locus**: a base locus as in `LocusMap.Reads`; ring
`g`'s standing on the element edge `r → r` of every ring `r` near `g`; a source ring's source port
and every ring's receiving map on its ring's element edge, where their deposits read. -/
def RReads : RLocus Ring Contact → (Ring ⊕ Contact) → (Ring ⊕ Contact) → Prop
  | .base ℓ, z, y => Reads endRing ℓ z y
  | .standing g, z, y => ∃ r, Near endRing g r ∧ z = .inl r ∧ y = .inl r
  | .sourcePort g, z, y => g ∈ Src ∧ z = .inl g ∧ y = .inl g
  | .receivingMap g, z, y => z = .inl g ∧ y = .inl g

/-- [definition] **The loci a block's references read**: those of `MediumStanding.RefReads`. -/
def RRefReads : RLocus Ring Contact → Ring ⊕ Contact → Prop
  | .base ℓ, b => RefReads ℓ b
  | _, _ => False

/-- [definition] **The loci a block's opening reads**: a source ring's source port. -/
def ROpenReads : RLocus Ring Contact → Ring ⊕ Contact → Prop
  | .sourcePort g, b => b = .inl g ∧ g ∈ Src
  | _, _ => False

/-- [definition] **The loci a receiver's reading reads**: its ring's receiving map. -/
def RRecvReads : RLocus Ring Contact → Ring ⊕ Contact → Prop
  | .receivingMap g, b => b = .inl g
  | _, _ => False

variable {endRing Src}

/-- [proved-derived; formal-checked] Every edge that reads a locus is an edge of the block graph. -/
theorem rreads_adj {ℓ : RLocus Ring Contact} {z y : Ring ⊕ Contact}
    (h : RReads endRing Src ℓ z y) : blockAdj endRing z y := by
  cases ℓ with
  | base ℓ => exact LocusMap.reads_adj h
  | standing g =>
    obtain ⟨r, -, rfl, rfl⟩ := h
    exact Or.inl rfl
  | sourcePort g =>
    obtain ⟨-, rfl, rfl⟩ := h
    exact Or.inl rfl
  | receivingMap g =>
    obtain ⟨rfl, rfl⟩ := h
    exact Or.inl rfl

end Loci

/-! ## 3. The law on the medium with the ring loci -/

section Law

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
variable {Q : Ring → Type u} [∀ g, AddCommGroup (Q g)] [∀ g, Module ℝ (Q g)]
variable {U : Ring → Type u} [∀ g, AddCommGroup (U g)] [∀ g, Module ℝ (U g)]
variable {endRing : Contact × Bool → Ring} {Src : Set Ring}

/-- A ring block's state. -/
local notation "MR" g => BlockM endRing V Ch (Sum.inl g)

variable (endRing V Ch ρ FE FC Q U) in
/-- [definition] **The constitution with the ring loci**: a factored medium at the declared tick
length `h₀`, and per ring a standing `q_g`, a source port `E_g` from the source input's space
`U g` to the ring's block, and the receiving map read on the ring block's covectors. -/
structure RingsAt (h₀ : ℝ) : Type u where
  φ : FactoredAt ρ V Ch FE FC endRing h₀
  q : (g : Ring) → Q g
  E : (g : Ring) → U g →ₗ[ℝ] MR g
  Rd : (g : Ring) → Module.Dual ℝ (MR g) →ₗ[ℝ] Module.Dual ℝ (MR g)

/-- [definition] **Two constitutions agree on a locus**: on a base locus their factors and declared
operands (`FactoredMedium.FAgreeOn`), on a ring locus its value. -/
def RAgreeOn {h₀ : ℝ} (θ θ' : RingsAt ρ V Ch FE FC Q U endRing h₀) :
    RLocus Ring Contact → Prop
  | .base ℓ => FAgreeOn θ.φ.1 θ'.φ.1 ℓ
  | .standing g => θ.q g = θ'.q g
  | .sourcePort g => θ.E g = θ'.E g
  | .receivingMap g => θ.Rd g = θ'.Rd g

open Classical in
/-- [definition] **The data a ring locus reads**: the data on the edges that read it. -/
def ringData (d : EdgeData endRing V Ch) (ℓ : RLocus Ring Contact) : EdgeData endRing V Ch :=
  fun y z => if RReads endRing Src ℓ z y then d y z else []

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem ringData_congr {d d' : EdgeData endRing V Ch} {ℓ : RLocus Ring Contact}
    (h : ∀ y z, RReads endRing Src ℓ z y → d y z = d' y z) :
    ringData (Src := Src) d ℓ = ringData (Src := Src) d' ℓ := by
  classical
  funext y z
  simp only [ringData]
  split_ifs with hr
  · exact h y z hr
  · rfl

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem ringData_quiet {d : EdgeData endRing V Ch} {ℓ : RLocus Ring Contact}
    (h : ∀ y z, RReads endRing Src ℓ z y → d y z = []) :
    ringData (Src := Src) d ℓ = fun _ _ => [] := by
  classical
  funext y z
  simp only [ringData]
  split_ifs with hr
  · exact h y z hr
  · rfl

variable {Λ Mo Cell Crib : Type*}

open Classical in
/-- [definition] **The opening** (`Word::opened_at` with the source ports): at a declared source
ring `g`, its source port applied to the moment's source input `u_g`; zero elsewhere. -/
def ringOpen {h₀ : ℝ} (Src : Set Ring) (src : Λ → Mo → (g : Ring) → U g)
    (θ : RingsAt ρ V Ch FE FC Q U endRing h₀) (l : Λ) (m : Mo) :
    (b : Ring ⊕ Contact) → BlockM endRing V Ch b
  | .inl g => if g ∈ Src then θ.E g (src l m g) else 0
  | .inr _ => 0

/-- [definition] **The reading through the receiving map**: at ring `g` its receiving map on
covectors, at a contact block the identity. -/
def ringRecv {h₀ : ℝ} (θ : RingsAt ρ V Ch FE FC Q U endRing h₀) :
    (b : Ring ⊕ Contact) →
      Module.Dual ℝ (BlockM endRing V Ch b) →ₗ[ℝ] Module.Dual ℝ (BlockM endRing V Ch b)
  | .inl g => θ.Rd g
  | .inr _ => LinearMap.id

open Classical in
/-- [definition] **The law on the medium with the ring loci**: the tick's block operator at the
classes the standings give through the lock chart `χ`, the loci with the ring loci, the references
of the reception carry, the opening through the source ports, the reading through the receiving
maps, the factors' and the ring loci's deposits and releases. The class is `Unit`: no operand of
this medium is read at the clock. -/
def ringLaw (h₀ : ℝ) (χ : LockChart ρ Q endRing) (Src : Set Ring)
    (src : Λ → Mo → (g : Ring) → U g) (ticks : Λ → Mo → ℕ)
    (cross : Λ → Λ → (b : Ring ⊕ Contact) → MediumRef Ring Ch b → MediumRef Ring Ch b →
      (BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b))
    (absorb : (b : Ring ⊕ Contact) → BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b)
    (ingestStep : Cell → Λ × Mo → Λ × Mo) (rekey : Crib → Λ → Λ)
    (Ψe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r → EdgeData endRing V Ch →
      ElementFactors (V := V) (FE := FE) (ρ := ρ) r)
    (Ψc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a → EdgeData endRing V Ch →
      ChannelFactors (Ch := Ch) (FC := FC) a)
    (Ψq : (g : Ring) → Q g → EdgeData endRing V Ch → Q g)
    (Ψs : (g : Ring) → (U g →ₗ[ℝ] MR g) → EdgeData endRing V Ch → (U g →ₗ[ℝ] MR g))
    (Ψr : (g : Ring) → (Module.Dual ℝ (MR g) →ₗ[ℝ] Module.Dual ℝ (MR g)) →
      EdgeData endRing V Ch → (Module.Dual ℝ (MR g) →ₗ[ℝ] Module.Dual ℝ (MR g))) :
    TickLaw ℝ (BlockM endRing V Ch) (RingsAt ρ V Ch FE FC Q U endRing h₀) (RLocus Ring Contact)
      (MediumRef Ring Ch) Unit Λ Mo Cell Crib where
  op _ θ := blockOp (withSheets_admissible (toMedium_admissible θ.φ.2.1) (sheets χ θ.q))
  reads := RReads endRing Src
  refReads := RRefReads
  openReads := ROpenReads Src
  recvReads := RRecvReads
  agreeOn ℓ θ θ' := RAgreeOn θ θ' ℓ
  ref θ := mediumRef (toMedium θ.φ.1)
  recv := ringRecv
  cls _ _ := ()
  openState := ringOpen Src src
  ticks := ticks
  cross := cross
  absorb := absorb
  ingestStep := ingestStep
  rekey := rekey
  apply θ d :=
    { φ := ⟨fdeposited Ψe Ψc (locusOf d) θ.φ.1, declared_fdeposited θ.φ.2.1, θ.φ.2.2⟩
      q := fun g => Ψq g (θ.q g) (ringData (Src := Src) d (.standing g))
      E := fun g => Ψs g (θ.E g) (ringData (Src := Src) d (.sourcePort g))
      Rd := fun g => Ψr g (θ.Rd g) (ringData (Src := Src) d (.receivingMap g)) }
  release keep θ :=
    { φ := ⟨frelease (fun ℓ => keep (.base ℓ)) θ.φ.1, declared_frelease θ.φ.2.1, θ.φ.2.2⟩
      q := fun g => if keep (.standing g) then θ.q g else 0
      E := fun g => if keep (.sourcePort g) then θ.E g else 0
      Rd := fun g => if keep (.receivingMap g) then θ.Rd g else 0 }

variable {h₀ : ℝ} {χ : LockChart ρ Q endRing} {src : Λ → Mo → (g : Ring) → U g}
  {ticks : Λ → Mo → ℕ}
  {cross : Λ → Λ → (b : Ring ⊕ Contact) → MediumRef Ring Ch b → MediumRef Ring Ch b →
    (BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b)}
  {absorb : (b : Ring ⊕ Contact) → BlockM endRing V Ch b →ₗ[ℝ] BlockM endRing V Ch b}
  {ingestStep : Cell → Λ × Mo → Λ × Mo} {rekey : Crib → Λ → Λ}
  {Ψe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r → EdgeData endRing V Ch →
    ElementFactors (V := V) (FE := FE) (ρ := ρ) r}
  {Ψc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a → EdgeData endRing V Ch →
    ChannelFactors (Ch := Ch) (FC := FC) a}
  {Ψq : (g : Ring) → Q g → EdgeData endRing V Ch → Q g}
  {Ψs : (g : Ring) → (U g →ₗ[ℝ] BlockM endRing V Ch (.inl g)) → EdgeData endRing V Ch →
    (U g →ₗ[ℝ] BlockM endRing V Ch (.inl g))}
  {Ψr : (g : Ring) →
    (Module.Dual ℝ (BlockM endRing V Ch (.inl g)) →ₗ[ℝ]
      Module.Dual ℝ (BlockM endRing V Ch (.inl g))) →
    EdgeData endRing V Ch →
    (Module.Dual ℝ (BlockM endRing V Ch (.inl g)) →ₗ[ℝ]
      Module.Dual ℝ (BlockM endRing V Ch (.inl g)))}

/-- The law on the medium with the ring loci at the section's operands. -/
local notation "RL" => ringLaw (Cell := Cell) (Crib := Crib) h₀ χ Src src ticks cross absorb
  ingestStep rekey Ψe Ψc Ψq Ψs Ψr

open Classical in
/-- [proved-derived; formal-checked] **The locus map's laws hold on the medium with the ring
loci**, for every factor law and every ring-locus law. -/
theorem ringLaw_lawful : (RL).Lawful (blockAdj endRing) where
  sparse c θ := blockOp_sparse _
  reads_adj ℓ z y h := rreads_adj h
  op_reads _ θ θ' y z h := by
    refine blockOp_agree (withSheets_admissible (toMedium_admissible θ.φ.2.1) (sheets χ θ.q))
      (withSheets_admissible (toMedium_admissible θ'.φ.2.1) (sheets χ θ'.q))
      (θ.φ.2.2.trans θ'.φ.2.2.symm) fun ℓ hr => ?_
    have hb := agreeOn_toMedium (h (.base ℓ) hr)
    cases ℓ with
    | element r =>
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨hb.1, hb.2.1, sheets_congr fun g hg => h (.standing g) ⟨r, hg, rfl, rfl⟩,
        hb.2.2.2⟩
    | junction r => exact hb
    | channel a => exact hb
    | conductance a => exact hb
  ref_reads θ θ' b h := by
    cases b with
    | inl r => rfl
    | inr a =>
      have hG : θ.φ.1.G a = θ'.φ.1.G a := h (.base (.conductance a)) rfl
      have hc : θ.φ.1.c a = θ'.φ.1.c a := (h (.base (.channel a)) rfl).1
      show (ULift.up (θ.φ.1.G a), sq (θ.φ.1.c a)) = (ULift.up (θ'.φ.1.G a), sq (θ'.φ.1.c a))
      rw [hG, hc]
  open_reads θ θ' l m b h := by
    cases b with
    | inl g =>
      show (if g ∈ Src then θ.E g (src l m g) else 0) = if g ∈ Src then θ'.E g (src l m g) else 0
      split_ifs with hg
      · rw [show θ.E g = θ'.E g from h (.sourcePort g) ⟨rfl, hg⟩]
      · rfl
    | inr a => rfl
  recv_reads θ θ' b h := by
    cases b with
    | inl g => exact h (.receivingMap g) rfl
    | inr a => rfl
  apply_local θ θ' d d' ℓ hθ hd := by
    cases ℓ with
    | base ℓ => exact fdeposited_local hθ hd
    | standing g =>
      show Ψq g (θ.q g) _ = Ψq g (θ'.q g) _
      rw [show θ.q g = θ'.q g from hθ, ringData_congr hd]
    | sourcePort g =>
      show Ψs g (θ.E g) _ = Ψs g (θ'.E g) _
      rw [show θ.E g = θ'.E g from hθ, ringData_congr hd]
    | receivingMap g =>
      show Ψr g (θ.Rd g) _ = Ψr g (θ'.Rd g) _
      rw [show θ.Rd g = θ'.Rd g from hθ, ringData_congr hd]
  release_keeps keep θ ℓ hk := by
    cases ℓ with
    | base ℓ => exact fagreeOn_frelease (keep := fun ℓ => keep (.base ℓ)) θ.φ.1 hk
    | standing g => exact (if_pos hk).symm
    | sourcePort g => exact (if_pos hk).symm
    | receivingMap g => exact (if_pos hk).symm

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] **The quiet laws hold on the medium with the ring loci** for
laws that keep a locus on empty data. -/
theorem ringLaw_quiet
    (hΨe0 : ∀ r p, Ψe r p (fun _ _ => []) = p) (hΨc0 : ∀ a p, Ψc a p (fun _ _ => []) = p)
    (hΨq0 : ∀ g p, Ψq g p (fun _ _ => []) = p) (hΨs0 : ∀ g p, Ψs g p (fun _ _ => []) = p)
    (hΨr0 : ∀ g p, Ψr g p (fun _ _ => []) = p) : (RL).Quiet where
  refl ℓ θ := by
    cases ℓ with
    | base ℓ => exact fagreeOn_refl θ.φ.1 ℓ
    | standing g => exact rfl
    | sourcePort g => exact rfl
    | receivingMap g => exact rfl
  trans ℓ _ _ _ h₁ h₂ := by
    cases ℓ with
    | base ℓ => exact fagreeOn_trans h₁ h₂
    | standing g => exact Eq.trans h₁ h₂
    | sourcePort g => exact Eq.trans h₁ h₂
    | receivingMap g => exact Eq.trans h₁ h₂
  apply_quiet θ d ℓ h := by
    cases ℓ with
    | base ℓ => exact fdeposited_quiet hΨe0 hΨc0 θ.φ.1 h
    | standing g =>
      show θ.q g = Ψq g (θ.q g) _
      rw [ringData_quiet h, hΨq0]
    | sourcePort g =>
      show θ.E g = Ψs g (θ.E g) _
      rw [ringData_quiet h, hΨs0]
    | receivingMap g =>
      show θ.Rd g = Ψr g (θ.Rd g) _
      rw [ringData_quiet h, hΨr0]

omit [Fintype Ring] in
open Classical in
/-- [proved-derived; formal-checked] **The opening is supported on the sources** when every declared
source ring is seeded (the Rust's seed rings are its sources). -/
theorem ringOpen_supported {S : Set (Ring ⊕ Contact)}
    (hSrc : ∀ g ∈ Src, (.inl g : Ring ⊕ Contact) ∈ S) :
    ∀ θ l m, SupportedIn ((RL).openState θ l m) S := by
  intro θ l m b hb
  cases b with
  | inl g =>
    show (if g ∈ Src then θ.E g (src l m g) else 0) = 0
    rw [if_neg fun hg => hb (hSrc g hg)]
  | inr a => rfl

/-! ## 4. The standing law, and the Rust's rule -/

/-- [proved-derived; formal-checked] **The standing on the medium with the ring loci** (#62): the
tick-indexed standing law of `HNN/TickStanding` at this law, for any factor and ring-locus laws. -/
def ringStanding {S R : Set (Ring ⊕ Contact)} (hSrc : ∀ g ∈ Src, (.inl g : Ring ⊕ Contact) ∈ S) :
    Holonics.Foundation.Standing.StandingLaw
      (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R))
      (Option ℕ × ReceiverReading ℝ (BlockM endRing V Ch) R) (ValidResident (blockAdj endRing) RL S)
      (ValidResident (blockAdj endRing) RL S) ℝ :=
  tickStanding (L := RL) (adj := blockAdj endRing) (S := S) (R := R) ringLaw_lawful
    (ringOpen_supported hSrc)

/-- [proved-derived; formal-checked] **On the medium with the ring loci a deposit between words
never reopens a released locus**, for laws that keep a locus on empty data. -/
theorem ring_released_stays_released
    (hΨe0 : ∀ r p, Ψe r p (fun _ _ => []) = p) (hΨc0 : ∀ a p, Ψc a p (fun _ _ => []) = p)
    (hΨq0 : ∀ g p, Ψq g p (fun _ _ => []) = p) (hΨs0 : ∀ g p, Ψs g p (fun _ _ => []) = p)
    (hΨr0 : ∀ g p, Ψr g p (fun _ _ => []) = p)
    {S R : Set (Ring ⊕ Contact)} (hSrc : ∀ g ∈ Src, (.inl g : Ring ⊕ Contact) ∈ S)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) RL S)
    (h : StagedOff (blockAdj endRing) S R s.1) {ℓ : RLocus Ring Contact}
    (hℓ : ¬ TickStanding.Retained (blockAdj endRing) RL S R ℓ) :
    RAgreeOn ((RL).release (TickStanding.Retained (blockAdj endRing) RL S R) s.1.loci)
      (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) RL ringLaw_lawful (ringOpen_supported hSrc)) w
        ⟨retain (blockAdj endRing) RL S R s.1, retain_valid s.2⟩).1.loci ℓ :=
  released_stays_released ringLaw_lawful (ringLaw_quiet hΨe0 hΨc0 hΨq0 hΨs0 hΨr0)
    (ringOpen_supported hSrc) w s h hℓ

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] **The receiver's receiving map is retained** by the standing
law's rule (`Diamond::retains`: `ReceivingMap(g)` when `g` is the receiver). -/
theorem retained_receiver {S R : Set (Ring ⊕ Contact)} {g : Ring}
    (hg : (.inl g : Ring ⊕ Contact) ∈ R) :
    TickStanding.Retained (blockAdj endRing) RL S R (.receivingMap g) :=
  Or.inr (Or.inr (Or.inr ⟨.inl g, rfl, hg⟩))

variable (endRing Src) in
/-- [definition] **The Rust's retention rule with the ring loci** (`Diamond::retains`, under
`retention::retained`): a base locus as in `LocusMap.Retained`; a standing when the element of
`g` or of the other end of a contact at `g` is retained (`Diamond::standing`); a source port when
`g` is a source and observes a receiver within `e` (`Diamond::source_port`); a receiving map
always (`retention::retained` keeps every receiving map, and `Constitution::release` never
releases one). -/
def RustRetained (S R : Set (Ring ⊕ Contact)) (e : ℕ) : RLocus Ring Contact → Prop
  | .base ℓ => LocusMap.Retained endRing S R e ℓ
  | .standing g => LocusMap.Retained endRing S R e (.element g) ∨
      ∃ a s, endRing (a, s) = g ∧ LocusMap.Retained endRing S R e (.element (endRing (a, !s)))
  | .sourcePort g => g ∈ Src ∧ ∃ m, Observes (blockAdj endRing) R (.inl g) m ∧ m ≤ e
  | .receivingMap _ => True

omit [DecidableEq Ring] [DecidableEq Contact] in
/-- A ring's element edge on a walk observes a receiver within `2|B|`. -/
theorem observes_of_walk {S R : Set (Ring ⊕ Contact)} {g : Ring}
    (hw : OnWalk (blockAdj endRing) S R (.inl g) (.inl g)) :
    ∃ m, Observes (blockAdj endRing) R (.inl g) m ∧ m ≤ 2 * Fintype.card (Ring ⊕ Contact) := by
  obtain ⟨j, m, -, hm, hle⟩ := (inDiamond_continuing_iff (adj := blockAdj endRing) S R _ _).mpr hw
  exact ⟨m, hm, by omega⟩

/-- [proved-derived; formal-checked] **The Rust's rule keeps the retained loci** on the medium with
the ring loci. A base locus is kept as in `FactoredMedium.retained_rust_factored`. A standing read
on a walk edge `r → r` has `r` near `g`, and the walk edge is in the diamond at `2|B|`, so the
element of `r`, which is `g` or the other end of a contact at `g`, is retained. A source port is
read at a source ring that observes a receiver, on its walk edge or by the opening, so `g` is a
source observing a receiver within `2|B|`. The Rust keeps every receiving map. -/
theorem retained_rust_ring {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {ℓ : RLocus Ring Contact}
    (h : TickStanding.Retained (blockAdj endRing) RL S R ℓ) :
    RustRetained endRing Src S R (2 * Fintype.card (Ring ⊕ Contact)) ℓ := by
  rcases h with ⟨z, y, hr, hw⟩ | ⟨b, hrb, hreach, hobs⟩ | ⟨b, hrb, hbS, hobs⟩ | ⟨b, hrb, -⟩
  · have hd := (inDiamond_continuing_iff (adj := blockAdj endRing) S R z y).mpr hw
    cases ℓ with
    | base ℓ => exact retained_of_reads hS hR hr hd
    | standing g =>
      obtain ⟨r, hg, rfl, rfl⟩ := hr
      have hel : LocusMap.Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact)) (.element r) :=
        retained_of_reads hS hR (ℓ := .element r) ⟨rfl, rfl⟩ hd
      rcases hg with rfl | ⟨⟨a, s⟩, hs, hg⟩
      · exact Or.inl hel
      · refine Or.inr ⟨a, !s, hg, ?_⟩
        rw [Bool.not_not, hs]
        exact hel
    | sourcePort g =>
      obtain ⟨hg, rfl, rfl⟩ := hr
      exact ⟨hg, observes_of_walk hw⟩
    | receivingMap g => trivial
  · cases ℓ with
    | base ℓ =>
      have hd := (inDiamond_continuing_iff (adj := blockAdj endRing) S R b b).mpr ⟨hreach, hobs⟩
      cases ℓ with
      | element r => exact absurd hrb id
      | junction r => exact absurd hrb id
      | channel a =>
        obtain rfl : b = .inr a := hrb
        exact channel_of_edge hS hR (Or.inl rfl) (Or.inl rfl) hd
      | conductance a =>
        obtain rfl : b = .inr a := hrb
        exact Or.inl (channel_of_edge hS hR (Or.inl rfl) (Or.inl rfl) hd)
    | standing g => exact absurd hrb id
    | sourcePort g => exact absurd hrb id
    | receivingMap g => trivial
  · cases ℓ with
    | sourcePort g =>
      obtain ⟨rfl, hg⟩ := hrb
      exact ⟨hg, observes_of_walk ⟨subset_reachAll S hbS, hobs⟩⟩
    | receivingMap g => trivial
    | base ℓ => exact absurd hrb id
    | standing g => exact absurd hrb id
  · cases ℓ with
    | receivingMap g => trivial
    | base ℓ => exact absurd hrb id
    | standing g => exact absurd hrb id
    | sourcePort g => exact absurd hrb id

/-- [proved-derived; formal-checked] **The collapse the Rust runs is sufficient on the medium with
the ring loci, for every factor and ring-locus law** (`hnn::retention::collapse` under
`Diamond::continuing`). Releasing every locus the Rust's rule does not retain at `e_last = 2 |B|`,
the standings and source ports included, changes no admitted face of the current word or of any
pending word, after any word of the generators. -/
theorem ring_rust_collapse_sufficient {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (hSrc : ∀ g ∈ Src, (.inl g : Ring ⊕ Contact) ∈ S)
    (q : Option ℕ × ReceiverReading ℝ (BlockM endRing V Ch) R)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) RL S) :
    observe RL q (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) RL ringLaw_lawful (ringOpen_supported hSrc)) w
        ⟨{ s.1 with loci := (RL).release (RustRetained endRing Src S R
            (2 * Fintype.card (Ring ⊕ Contact))) s.1.loci }, s.2⟩).1 =
      observe RL q (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) RL ringLaw_lawful (ringOpen_supported hSrc)) w s).1 :=
  keeps_sufficient ringLaw_lawful (ringOpen_supported hSrc)
    (fun _ hℓ => retained_rust_ring hS hR hℓ) q w s

/-! ## 5. The certified step -/

variable
    {ηe : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r → EdgeData endRing V Ch → ℝ}
    {ge : (r : Ring) → ElementFactors (V := V) (FE := FE) (ρ := ρ) r → (y z : Ring ⊕ Contact) →
      BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y) →
      ElementFactors (V := V) (FE := FE) (ρ := ρ) r}
    {ηc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a → EdgeData endRing V Ch → ℝ}
    {gc : (a : Contact) → ChannelFactors (Ch := Ch) (FC := FC) a → (y z : Ring ⊕ Contact) →
      BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y) →
      ChannelFactors (Ch := Ch) (FC := FC) a}
    {ηq : (g : Ring) → Q g → EdgeData endRing V Ch → ℝ}
    {gq : (g : Ring) → Q g → (y z : Ring ⊕ Contact) →
      BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y) → Q g}
    {ηs : (g : Ring) → (U g →ₗ[ℝ] BlockM endRing V Ch (.inl g)) → EdgeData endRing V Ch → ℝ}
    {gs : (g : Ring) → (U g →ₗ[ℝ] BlockM endRing V Ch (.inl g)) → (y z : Ring ⊕ Contact) →
      BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y) →
      (U g →ₗ[ℝ] BlockM endRing V Ch (.inl g))}
    {ηr : (g : Ring) →
      (Module.Dual ℝ (BlockM endRing V Ch (.inl g)) →ₗ[ℝ]
        Module.Dual ℝ (BlockM endRing V Ch (.inl g))) →
      EdgeData endRing V Ch → ℝ}
    {gr : (g : Ring) →
      (Module.Dual ℝ (BlockM endRing V Ch (.inl g)) →ₗ[ℝ]
        Module.Dual ℝ (BlockM endRing V Ch (.inl g))) →
      (y z : Ring ⊕ Contact) → BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y) →
      (Module.Dual ℝ (BlockM endRing V Ch (.inl g)) →ₗ[ℝ]
        Module.Dual ℝ (BlockM endRing V Ch (.inl g)))}

/-- The law on the medium with the ring loci under the certified step. -/
local notation "CRL" => ringLaw (Cell := Cell) (Crib := Crib) h₀ χ Src src ticks cross absorb
  ingestStep rekey (fun r => certifiedStep (ηe r) (ge r)) (fun a => certifiedStep (ηc a) (gc a))
  (fun g => certifiedStep (ηq g) (gq g)) (fun g => certifiedStep (ηs g) (gs g))
  (fun g => certifiedStep (ηr g) (gr g))

/-- [proved-derived; formal-checked] **Under the certified step, a deposit between words never
reopens a released locus**, the ring loci included, with no hypothesis on the steps or the moves.
The standing's step `q ← q + η Lᵀ g_σ / h_q` is a certified step: `η` the certified `2^k / h_q`,
each datum's move its term of `Lᵀ g_σ`; the source port's and the receiving map's normal-law steps
likewise. -/
theorem certified_ring_released_stays_released
    {S R : Set (Ring ⊕ Contact)} (hSrc : ∀ g ∈ Src, (.inl g : Ring ⊕ Contact) ∈ S)
    (w : List (CarryGen Cell Crib (ReceiverFamily ℝ (BlockM endRing V Ch) R)))
    (s : ValidResident (blockAdj endRing) CRL S)
    (h : StagedOff (blockAdj endRing) S R s.1) {ℓ : RLocus Ring Contact}
    (hℓ : ¬ TickStanding.Retained (blockAdj endRing) CRL S R ℓ) :
    RAgreeOn ((CRL).release (TickStanding.Retained (blockAdj endRing) CRL S R) s.1.loci)
      (Holonics.Foundation.Chronology.transportWord
        (transport (blockAdj endRing) CRL ringLaw_lawful (ringOpen_supported hSrc)) w
        ⟨retain (blockAdj endRing) CRL S R s.1, retain_valid s.2⟩).1.loci ℓ :=
  ring_released_stays_released (fun r p => certifiedStep_quiet (ηe r) (ge r) p)
    (fun a p => certifiedStep_quiet (ηc a) (gc a) p)
    (fun g p => certifiedStep_quiet (ηq g) (gq g) p)
    (fun g p => certifiedStep_quiet (ηs g) (gs g) p)
    (fun g p => certifiedStep_quiet (ηr g) (gr g) p) hSrc w s h hℓ

end Law

end Holonics.HNN.RingLoci

#print axioms Holonics.HNN.RingLoci.contrast_congr
#print axioms Holonics.HNN.RingLoci.sheets_congr
#print axioms Holonics.HNN.RingLoci.ringLaw_lawful
#print axioms Holonics.HNN.RingLoci.ringLaw_quiet
#print axioms Holonics.HNN.RingLoci.ringOpen_supported
#print axioms Holonics.HNN.RingLoci.ringStanding
#print axioms Holonics.HNN.RingLoci.ring_released_stays_released
#print axioms Holonics.HNN.RingLoci.retained_receiver
#print axioms Holonics.HNN.RingLoci.retained_rust_ring
#print axioms Holonics.HNN.RingLoci.ring_rust_collapse_sufficient
#print axioms Holonics.HNN.RingLoci.certified_ring_released_stays_released
