import Holonics.HNN.TickBlocks
import Holonics.HNN.Retention

/-!
# HNN.LocusMap: which of the medium's operands each block edge reads

[definition] #62, owed by `HNN/TickBlocks` and `HNN/CarriedStanding`: the locus map from the
medium's operands to the block edges, and with it the readOp-family laws of `HNN/Retention` on the
concrete medium. `HNN/TickBlocks` writes one tick at an admissible `Word.Medium` as the sparse block
operator `blockOp` on the ring/contact blocks. This file says which operands move which edge's
operator, names the Rust owner each is read from, proves that the Rust's per-locus retention rule
keeps every locus an edge of the causal diamond reads, and reads the release and deposit laws on
the concrete medium under the Rust's per-locus release. `HNN/Word`, `HNN/TickBlocks`,
`HNN/Retention` and `HNN/CarriedStanding` are unchanged.

| Locus (`hnn::constitution::Locus`) | Operands of `Medium` | Rust owner | Edges `z → y` that read it (`Reads`) | Rust reading site |
|---|---|---|---|---|
| `Element(g)` | `Ws g`, `A g`, `σ g`, `Wc g` | the constitution's ring material: the passive factor `f_g` (`W_s = −f_g f_gᵀ`), the slices, the contrast port `W_c`; `σ` the sheet classes of `Field::standing_contrast` | `g → g` | `Word::tick`, `element_step` on `operands.rings()[g]` (`RingOperands`) |
| `Junction(g)` | `Y g` | `RingDeclaration::admittance`, declared | every edge out of `g` | `Word::junctions`, `participation(operands.weights(g), …)` |
| `Channel(a)` | `C a`, `D a`, `K a`, `channel (a, s)` | the contact material (`C = c cᵀ`, `K = b bᵀ`, `D = F Fᵀ`); the embeddings are `ContactDeclaration::channel`'s matchings (`ContactOperands::selection`), declared | every edge between `a`'s blocks (its own and its two rings') | `Word::tick`, `transit_solve` and `transit_update` on `operands.contacts()[a]` |
| `Conductance(a)` | `G a` | `ContactDeclaration::{admittance, exponent}` at the lift (`ContactOperands::conductance`), declared | every edge out of `a`'s blocks | `Word::junctions` (the weights at `a`'s ends) and the transit |

The tick length `h` (`FieldDeclaration::step`, `Operands::step`) is declared, read on almost every
edge and never released; the locus map takes it equal.

[proved-derived; formal-checked] What is proved.

1. **The locus map** (`blockOp_agree`). Two admissible media at one tick length whose operands
   agree on every locus the edge `z → y` reads have the same block operator on that edge. With the
   change carried on block `z` alone, ring `r`'s anchor reads `Y_r` and the conductance of every
   contact at `r` and is zero unless `z` is `r`'s block; contact `a`'s slip reads its channel, its
   conductance and its ends' anchors and is zero unless `z` is one of `a`'s blocks; ring `r`'s
   element reads its own operands, and its solve of zero data is zero (`anchor_agree`,
   `slip_agree`, `elementSolve_zero`). Every reading edge is an edge of `Word.blockAdj`
   (`reads_adj`). A change of operands therefore moves only the edges that read a moved locus
   (`opSub_reads`), which is where the residual of `fieldTick_variation_exact` (the read of
   `Retention.contemporary_read`) lives.
2. **The Rust's rule is sound** (`retained_of_reads`). Under `Diamond::retains` (`Retained`: an
   element when `r_g + 1 + o_g ≤ e`, a junction when `r_g + o_g ≤ e`, a channel by its ends' minima
   `min(r_g, r_h) + 1 + min(o_g, o_h) ≤ e`, a conductance when its channel or either end's junction
   is), every locus read by an edge of the causal diamond `r_z + 1 + o_y ≤ e` is retained. The
   hypotheses are the Rust's: a seeded contact block comes with its end rings (`EndChange::support`
   seeds both ends of a contact whose state is nonzero), and the receivers are rings
   (`reach_contact`, `obs_contact`). The rule is sound, not tight: a junction at a receiver is kept
   at `r_g ≤ e` although no edge of the diamond reads it, which is lawful.
3. **The release** (`release`, `release_admissible`, `blockOp_release`). `Constitution::release`
   zeroes a released element's `W_s`, slices and `W_c` and a released channel's `C`, `D`, `K`; the
   junctions, conductances, embeddings, sheet classes and tick length are declared and stay. The
   released medium is admissible and agrees with the medium on every edge of the diamond. Hence
   **the release is indistinguishable on the concrete word** at every epoch `t ≤ e`
   (`release_indistinguishable`, from `TickBlocks.fieldTick_release_past_diamond`).
4. **The class family and the continuing chain.** `mediumOp c` reads a medium at the sheet classes
   `c` as `Retention.readOp`'s operand family (`readOp_uniform`, `lociSparse_uniform`). Under the
   continuing rule (`Diamond::continuing`, `e_last = 2 |B|`) the released medium agrees with the
   medium on every walk edge at every class (`mediumOp_release_on_walk`), so over any chain of words,
   each at its own classes and opened on the last one's end plus a source moment, the release
   changes no admitted reading at any epoch (`continuing_release_indistinguishable`, the concrete
   reading of `Retention.continuing_release_indistinguishable`).
5. **The deposit descends per locus** (`deposit_descends`). A locus deposits from the deposit data
   on the edges that read it (`locusData`; `Diamond::element_window`, `Diamond::channel_window`).
   Those data agree on every edge under the release (`depositData_agree`, `locusData_release`), and
   a released locus is reached by none (`locusData_released`), so for locus laws that keep a locus
   no datum reaches, releasing after a deposit is depositing after the release.

[definition; agent-inferred] **Reading the Rust's distances on the block graph.** The Rust runs its
recursions on the rings (`x_h ← min(x_h, x_g + 1)` over the contacts). On `Word.blockAdj` two
rings sharing a contact are one hop apart and a path through a contact block takes two, so the ring
blocks' distances are the Rust's; `Retained` states its rule on them. The Lean seeds are the Rust's
seed rings together with the contact blocks the opening change occupies, so that the opening change
is supported on them.

[open] **What it does not cover, owed in #62.**
* The Rust's loci with no operand on `Word.Medium`: `Resonator(g)` (the pumped element, whose tick
  runs at the pump's phase: `HNN/CarriedStanding`'s second model limit), `SourcePort(g)` (it enters
  the moment, not the tick), `Standing(g)` (it enters only through the sheet classes `σ`, and the
  Rust keeps it when the element of `g` or of a neighbour is kept) and `ReceivingMap(g)` (never
  released). Their retention rules are stated in the Rust only.
* The standing law over the concrete resident is not here. The concrete loci are shared by
  several edges (a junction by every edge out of its ring, a channel by every edge among its
  blocks); `HNN/TickStanding` states the standing law on shared loci, and `HNN/MediumStanding` is
  its instance on this medium, with the per-locus deposit of item 5.

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.LocusMap

open Holonics.Geometry.AffineSwing
open Holonics.HNN.Propagation
open Holonics.HNN.Word
open Holonics.HNN.TickBlocks
open Holonics.HNN.Retention
open scoped BigOperators

universe u

/-! ## 1. The loci and the edges that read them -/

/-- [definition] **The loci of the medium** (`hnn::constitution::Locus`, the ones a word's tick
reads): ring `r`'s element and junction, contact `a`'s channel and conductance. -/
inductive Locus (Ring Contact : Type u)
  | element (r : Ring)
  | junction (r : Ring)
  | channel (a : Contact)
  | conductance (a : Contact)

section Reads

variable {Ring Contact : Type u} (endRing : Contact × Bool → Ring)

/-- [definition] **The blocks of contact `a`**: its own block and its two rings' blocks. -/
def Ends (a : Contact) (b : Ring ⊕ Contact) : Prop :=
  b = .inr a ∨ ∃ s, b = .inl (endRing (a, s))

/-- [definition] **The block edges `z → y` that read a locus.** Ring `r`'s element is read on its
own edge `r → r`; its junction on every edge out of `r`; contact `a`'s channel on every edge
between its blocks; its conductance on every edge out of its blocks. -/
def Reads : Locus Ring Contact → (Ring ⊕ Contact) → (Ring ⊕ Contact) → Prop
  | .element r, z, y => z = .inl r ∧ y = .inl r
  | .junction r, z, y => z = .inl r ∧ blockAdj endRing z y
  | .channel a, z, y => Ends endRing a z ∧ Ends endRing a y
  | .conductance a, z, y => Ends endRing a z ∧ blockAdj endRing z y

variable {endRing}

theorem ends_adj {a : Contact} {z y : Ring ⊕ Contact} (hz : Ends endRing a z)
    (hy : Ends endRing a y) : blockAdj endRing z y := by
  rcases hz with rfl | ⟨s, rfl⟩ <;> rcases hy with rfl | ⟨s', rfl⟩
  · rfl
  · exact ⟨s', rfl⟩
  · exact ⟨s, rfl⟩
  · exact Or.inr ⟨a, s, s', rfl, rfl⟩

/-- [proved-derived; formal-checked] Every edge that reads a locus is an edge of the block graph. -/
theorem reads_adj {ℓ : Locus Ring Contact} {z y : Ring ⊕ Contact} (h : Reads endRing ℓ z y) :
    blockAdj endRing z y := by
  cases ℓ with
  | element r => obtain ⟨rfl, rfl⟩ := h; exact Or.inl rfl
  | junction r => exact h.2
  | channel a => exact ends_adj h.1 h.2
  | conductance a => exact h.2

end Reads

section Agree

variable {Ring Contact ρ : Type u}
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)] [∀ a, InnerProductSpace ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}

/-- [definition] **Two media agree on a locus**: on ring `r`'s element `W_s`, the slices `A`, the
sheet classes `σ` and `W_c`; on its junction `Y_r`; on contact `a`'s channel `C`, `D`, `K` and its
two embeddings; on its conductance `G_a`. -/
def AgreeOn (μ μ' : Medium endRing V Ch ρ) : Locus Ring Contact → Prop
  | .element r => μ.Ws r = μ'.Ws r ∧ μ.A r = μ'.A r ∧ μ.σ r = μ'.σ r ∧ μ.Wc r = μ'.Wc r
  | .junction r => μ.Y r = μ'.Y r
  | .channel a => μ.C a = μ'.C a ∧ μ.D a = μ'.D a ∧ μ.K a = μ'.K a ∧
      ∀ s, μ.channel (a, s) = μ'.channel (a, s)
  | .conductance a => μ.G a = μ'.G a

/-- [definition] Ring `r`'s junction anchor reads the same operands: `Y_r` and the conductance of
every contact at `r`. -/
def JunctionAgree (μ μ' : Medium endRing V Ch ρ) (r : Ring) : Prop :=
  μ.Y r = μ'.Y r ∧ ∀ e, endRing e = r → μ.G e.1 = μ'.G e.1

end Agree

/-! ## 2. The locus map: an edge's block operator reads only the loci of that edge -/

section Map

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}

omit [Fintype Ring] [DecidableEq Contact] [Fintype ρ] [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem ringAnchor_congr {Y Y' : Ring → ℝ} {G G' : Contact → ℝ} (s : (r : Ring) → V r)
    (arr : (e : Contact × Bool) → V (endRing e)) {r : Ring} (hY : Y r = Y' r)
    (hG : ∀ e, endRing e = r → G e.1 = G' e.1) :
    ringAnchor Y G s arr r = ringAnchor Y' G' s arr r := by
  have hf : (fun p : Port endRing r => G p.1.1) = fun p => G' p.1.1 :=
    funext fun p => hG p.1 p.2
  simp only [ringAnchor, hY, hf]

omit [Fintype Ring] [Fintype Contact] [Fintype ρ] [∀ r, InnerProductSpace ℝ (V r)] [∀ r, FiniteDimensional ℝ (V r)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem blockZero_single {z b : Ring ⊕ Contact} (v : BlockM endRing V Ch z) (hb : b ≠ z) :
    BlockZero (ofBlocks (Pi.single z v)) b := by
  rw [blockZero_iff, toBlocks_ofBlocks, Pi.single_eq_of_ne hb]

omit [Fintype Ring] [Fintype ρ] [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
/-- The anchor of ring `r` under the change carried on block `z` alone reads `r`'s junction only
when `z` is `r`'s block; otherwise it is zero. -/
theorem anchor_agree {μ μ' : Medium endRing V Ch ρ} {z : Ring ⊕ Contact}
    (v : BlockM endRing V Ch z) {r : Ring} (h : z = .inl r → JunctionAgree μ μ' r) :
    ringAnchor μ.Y μ.G (ofBlocks (Pi.single z v)).s (ofBlocks (Pi.single z v)).arr r =
      ringAnchor μ'.Y μ'.G (ofBlocks (Pi.single z v)).s (ofBlocks (Pi.single z v)).arr r := by
  by_cases hz : z = .inl r
  · exact ringAnchor_congr _ _ (h hz).1 (h hz).2
  · have hb := blockZero_single v (Ne.symm hz)
    rw [ringAnchor_zero _ _ _ r hb, ringAnchor_zero _ _ _ r hb]

omit [Fintype Ring] [Fintype ρ] [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem endOut_agree {μ μ' : Medium endRing V Ch ρ} {z : Ring ⊕ Contact}
    (v : BlockM endRing V Ch z) (e : Contact × Bool)
    (h : z = .inl (endRing e) → JunctionAgree μ μ' (endRing e)) :
    endOut μ.Y μ.G (ofBlocks (Pi.single z v)).s (ofBlocks (Pi.single z v)).arr e =
      endOut μ'.Y μ'.G (ofBlocks (Pi.single z v)).s (ofBlocks (Pi.single z v)).arr e := by
  simp only [endOut, anchor_agree v h]

omit [Fintype Ring] [Fintype ρ] [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem storageWave_agree {μ μ' : Medium endRing V Ch ρ} {z : Ring ⊕ Contact}
    (v : BlockM endRing V Ch z) {r : Ring} (h : z = .inl r → JunctionAgree μ μ' r) :
    storageWave μ.Y μ.G (ofBlocks (Pi.single z v)).s (ofBlocks (Pi.single z v)).arr r =
      storageWave μ'.Y μ'.G (ofBlocks (Pi.single z v)).s (ofBlocks (Pi.single z v)).arr r := by
  simp only [storageWave, anchor_agree v h]

omit [Fintype Ring] [Fintype ρ] [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem contrast_agree {μ μ' : Medium endRing V Ch ρ} {z : Ring ⊕ Contact}
    (v : BlockM endRing V Ch z) {r : Ring} (h : z = .inl r → JunctionAgree μ μ' r) :
    contrast μ.Y μ.G (ofBlocks (Pi.single z v)).s (ofBlocks (Pi.single z v)).arr r =
      contrast μ'.Y μ'.G (ofBlocks (Pi.single z v)).s (ofBlocks (Pi.single z v)).arr r := by
  simp only [contrast, anchor_agree v h]

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem elementSolve_congr {μ μ' : Medium endRing V Ch ρ} {r : Ring}
    (h : AgreeOn μ μ' (.element r)) (b c : V r) : elementSolve μ r b c = elementSolve μ' r b c := by
  obtain ⟨hWs, hA, hσ, hWc⟩ := h
  simp only [elementSolve, hWs, hA, hσ, hWc]

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] in
theorem elementSolve_zero {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (r : Ring) :
    elementSolve μ r 0 0 = 0 :=
  ((elementSolve_spec hμ r 0 0).2 0 (by simp [ElementStep])).symm

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem transitSolve_congr {μ μ' : Medium endRing V Ch ρ} {a : Contact} (hC : μ.C a = μ'.C a)
    (hD : μ.D a = μ'.D a) (hK : μ.K a = μ'.K a) (hG : μ.G a = μ'.G a) (hh : μ.h = μ'.h)
    (u w αg αh : Ch a) : transitSolve μ a u w αg αh = transitSolve μ' a u w αg αh := by
  simp only [transitSolve, hC, hD, hK, hG, hh]

omit [Fintype Ring] [Fintype ρ] in
/-- The slip of contact `a` under the change carried on block `z` alone reads `a`'s channel and
conductance and its ends' junctions only when `z` is one of `a`'s blocks; otherwise it is zero. -/
theorem slip_agree {μ μ' : Medium endRing V Ch ρ} (hμ : μ.Admissible) (hμ' : μ'.Admissible)
    (hh : μ.h = μ'.h) {z : Ring ⊕ Contact} (v : BlockM endRing V Ch z) (a : Contact)
    (hin : Ends endRing a z → AgreeOn μ μ' (.channel a) ∧ AgreeOn μ μ' (.conductance a) ∧
      ∀ s, z = .inl (endRing (a, s)) → JunctionAgree μ μ' (endRing (a, s))) :
    tickSlip μ (ofBlocks (Pi.single z v)) a = tickSlip μ' (ofBlocks (Pi.single z v)) a := by
  by_cases hz : Ends endRing a z
  · obtain ⟨⟨hC, hD, hK, hch⟩, hG, hj⟩ := hin hz
    simp only [tickSlip]
    rw [endOut_agree v (a, true) (hj true), endOut_agree v (a, false) (hj false), hch true,
      hch false]
    exact transitSolve_congr hC hD hK hG hh _ _ _ _
  · have hc : ∀ (ν : Medium endRing V Ch ρ), ν.Admissible →
        tickSlip ν (ofBlocks (Pi.single z v)) a = 0 := fun ν hν =>
      tickSlip_zero hν _ a (blockZero_single v fun h => hz (Or.inl h.symm))
        (blockZero_single v fun h => hz (Or.inr ⟨true, h.symm⟩))
        (blockZero_single v fun h => hz (Or.inr ⟨false, h.symm⟩))
    rw [hc μ hμ, hc μ' hμ']

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] **The locus map.** Two admissible media at one tick length
whose operands agree on every locus the edge `z → y` reads (`Reads`) have the same block operator
on that edge. -/
theorem blockOp_agree {μ μ' : Medium endRing V Ch ρ} (hμ : μ.Admissible) (hμ' : μ'.Admissible)
    (hh : μ.h = μ'.h) {y z : Ring ⊕ Contact}
    (hread : ∀ ℓ, Reads endRing ℓ z y → AgreeOn μ μ' ℓ) : blockOp hμ y z = blockOp hμ' y z := by
  refine LinearMap.ext fun v => ?_
  change tickMap μ (Pi.single z v) y = tickMap μ' (Pi.single z v) y
  simp only [tickMap]
  set X := ofBlocks (Pi.single z v) with hX
  have hjun : ∀ r, z = .inl r → blockAdj endRing z y → JunctionAgree μ μ' r := by
    intro r hz hadj
    refine ⟨hread (.junction r) ⟨hz, hadj⟩, fun e he => hread (.conductance e.1) ⟨?_, hadj⟩⟩
    exact Or.inr ⟨e.2, by rw [hz, ← he]⟩
  have hslip : ∀ a, Ends endRing a y → tickSlip μ X a = tickSlip μ' X a := by
    intro a hy
    refine slip_agree hμ hμ' hh v a fun hz => ⟨hread (.channel a) ⟨hz, hy⟩,
      hread (.conductance a) ⟨hz, ends_adj hz hy⟩, fun s hs => hjun _ hs (ends_adj hz hy)⟩
  cases y with
  | inl r =>
    have hjr : z = .inl r → JunctionAgree μ μ' r := fun hz => hjun r hz (by rw [hz]; exact Or.inl rfl)
    refine Prod.ext ?_ (funext fun p => ?_)
    · change elementSolve μ r (storageWave μ.Y μ.G X.s X.arr r) (contrast μ.Y μ.G X.s X.arr r) =
        elementSolve μ' r (storageWave μ'.Y μ'.G X.s X.arr r) (contrast μ'.Y μ'.G X.s X.arr r)
      rw [storageWave_agree v hjr, contrast_agree v hjr]
      by_cases hz : z = .inl r
      · exact elementSolve_congr (hread (.element r) ⟨hz, rfl⟩) _ _
      · have hb := blockZero_single v (Ne.symm hz)
        have hs : storageWave μ'.Y μ'.G X.s X.arr r = 0 := by
          rw [storageWave, ringAnchor_zero _ _ X r hb, hb.1]
          simp [Holonics.Geometry.AffineSwing.swing]
        have hc : contrast μ'.Y μ'.G X.s X.arr r = 0 := by
          rw [contrast, ringAnchor_zero _ _ X r hb, hb.1, sub_zero]
        rw [hs, hc, elementSolve_zero hμ, elementSolve_zero hμ']
    · obtain ⟨⟨a, s⟩, he⟩ := p
      subst he
      change (fieldTick μ X).arr (a, s) = (fieldTick μ' X).arr (a, s)
      have hy : Ends endRing a (.inl (endRing (a, s))) := Or.inr ⟨s, rfl⟩
      by_cases hz : Ends endRing a z
      · obtain ⟨-, -, -, hch⟩ := hread (.channel a) ⟨hz, hy⟩
        have hG : μ.G a = μ'.G a := hread (.conductance a) ⟨hz, ends_adj hz hy⟩
        have ho := endOut_agree v (a, s) fun h => hjun _ h (ends_adj hz hy)
        cases s with
        | true =>
          change arriveG _ _ _ _ = arriveG _ _ _ _
          rw [ho, hslip a hy, hch true, hG]
        | false =>
          change arriveH _ _ _ _ = arriveH _ _ _ _
          rw [ho, hslip a hy, hch false, hG]
      · have hb := blockZero_single v fun h => hz (Or.inr ⟨s, h.symm⟩)
        have hc : ∀ (ν : Medium endRing V Ch ρ), ν.Admissible →
            tickSlip ν X a = 0 ∧ endOut ν.Y ν.G X.s X.arr (a, s) = 0 := fun ν hν =>
          ⟨tickSlip_zero hν _ a (blockZero_single v fun h => hz (Or.inl h.symm))
            (blockZero_single v fun h => hz (Or.inr ⟨true, h.symm⟩))
            (blockZero_single v fun h => hz (Or.inr ⟨false, h.symm⟩)),
            endOut_zero _ _ X (a, s) hb⟩
        obtain ⟨h1, h2⟩ := hc μ hμ
        obtain ⟨h1', h2'⟩ := hc μ' hμ'
        cases s with
        | true =>
          change arriveG _ _ _ _ = arriveG _ _ _ _
          rw [h1, h2, h1', h2']
          simp [arriveG]
        | false =>
          change arriveH _ _ _ _ = arriveH _ _ _ _
          rw [h1, h2, h1', h2']
          simp [arriveH]
  | inr a =>
    have hy : Ends endRing a (.inr a) := Or.inl rfl
    refine Prod.ext ?_ ?_
    · change X.u a + μ.h • tickSlip μ X a = X.u a + μ'.h • tickSlip μ' X a
      rw [hh, hslip a hy]
    · change (2 : ℝ) • tickSlip μ X a - X.w a = (2 : ℝ) • tickSlip μ' X a - X.w a
      rw [hslip a hy]

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] **A change of operands moves only the edges that read it.**
The residual of `TickBlocks.fieldTick_variation_exact` (the read of `Retention.contemporary_read`)
sums `T′ − T` only over edges reading a locus on which the two media differ. -/
theorem opSub_reads {μ μ' : Medium endRing V Ch ρ} (hμ : μ.Admissible) (hμ' : μ'.Admissible)
    (hh : μ.h = μ'.h) {y z : Ring ⊕ Contact}
    (hread : ∀ ℓ, Reads endRing ℓ z y → AgreeOn μ μ' ℓ) :
    opSub (blockOp hμ') (blockOp hμ) y z = 0 := by
  simp [opSub, blockOp_agree hμ hμ' hh hread]

end Map

/-! ## 3. The retention rule per locus, and its soundness -/

section Rule

variable {Ring Contact : Type u} (endRing : Contact × Bool → Ring)

/-- [definition] Ring `r`'s junction is retained (`Diamond::junction`): `r_r + o_r ≤ e`. -/
def JunctionRetained (S R : Set (Ring ⊕ Contact)) (e : ℕ) (r : Ring) : Prop :=
  ∃ j m, (.inl r : Ring ⊕ Contact) ∈ reachWithin (blockAdj endRing) S j ∧
    Observes (blockAdj endRing) R (.inl r) m ∧ j + m ≤ e

/-- [definition] Contact `a`'s channel is retained (`Diamond::channel`):
`min(r_g, r_h) + 1 + min(o_g, o_h) ≤ e` over its two end rings. -/
def ChannelRetained (S R : Set (Ring ⊕ Contact)) (e : ℕ) (a : Contact) : Prop :=
  ∃ j m s s', (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ reachWithin (blockAdj endRing) S j ∧
    Observes (blockAdj endRing) R (.inl (endRing (a, s'))) m ∧ j + 1 + m ≤ e

/-- [definition] **The Rust's retention rule per locus** (`hnn::retention::Diamond::retains`):
an element when `r_g + 1 + o_g ≤ e`, a junction when `r_g + o_g ≤ e`, a channel by its ends'
minima, a conductance when its channel or either end's junction is retained. -/
def Retained (S R : Set (Ring ⊕ Contact)) (e : ℕ) : Locus Ring Contact → Prop
  | .element r => InDiamond (blockAdj endRing) S R e (.inl r) (.inl r)
  | .junction r => JunctionRetained endRing S R e r
  | .channel a => ChannelRetained endRing S R e a
  | .conductance a =>
      ChannelRetained endRing S R e a ∨ ∃ s, JunctionRetained endRing S R e (endRing (a, s))

variable {endRing}

/-- A contact block is reached no later than one of its end rings, when every seeded contact
block comes with its end rings (`EndChange::support`). -/
theorem reach_contact {S : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    {a : Contact} {j : ℕ} (h : (.inr a : Ring ⊕ Contact) ∈ reachWithin (blockAdj endRing) S j) :
    ∃ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ reachWithin (blockAdj endRing) S j := by
  obtain ⟨x, hx, n, hn, hr⟩ := h
  suffices key : ∀ b n, ReachIn (blockAdj endRing) x b n → b = .inr a →
      ∃ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ reachWithin (blockAdj endRing) S n by
    obtain ⟨s, hs⟩ := key _ n hr rfl
    exact ⟨s, reachWithin_mono hn hs⟩
  intro b n hr
  induction hr with
  | refl =>
    intro hb
    subst hb
    exact ⟨true, _, hS a hx true, 0, le_rfl, ReachIn.refl _⟩
  | @tail y b n hxy hadj ih =>
    intro hb
    subst hb
    cases y with
    | inl r =>
      obtain ⟨s, hs⟩ := hadj
      subst hs
      exact ⟨s, x, hx, n, by omega, hxy⟩
    | inr a' =>
      obtain rfl : a' = a := hadj
      obtain ⟨s, hs⟩ := ih rfl
      exact ⟨s, reachWithin_mono (by omega) hs⟩

/-- A contact block observes a receiver only through one of its end rings, one hop later, when no
receiver is a contact block. -/
theorem obs_contact {R : Set (Ring ⊕ Contact)} (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R)
    {a : Contact} {m : ℕ} (h : Observes (blockAdj endRing) R (.inr a) m) :
    ∃ s m', m' + 1 ≤ m ∧ Observes (blockAdj endRing) R (.inl (endRing (a, s))) m' := by
  obtain ⟨ρ, hρ, n, hn, hr⟩ := h
  rw [← reachIn_flip_iff] at hr
  suffices key : ∀ b n, ReachIn (flip (blockAdj endRing)) ρ b n → b = .inr a →
      ∃ s n', n' + 1 ≤ n ∧ ReachIn (flip (blockAdj endRing)) ρ (.inl (endRing (a, s))) n' by
    obtain ⟨s, n', hn', hr'⟩ := key _ n hr rfl
    exact ⟨s, n', by omega, ρ, hρ, n', le_rfl, reachIn_flip_iff.mp hr'⟩
  intro b n hr
  induction hr with
  | refl =>
    intro hb
    subst hb
    exact absurd hρ (hR a)
  | @tail y b n hρy hadj ih =>
    intro hb
    subst hb
    cases y with
    | inl r =>
      obtain ⟨s, hs⟩ := (hadj : blockAdj endRing (.inr a) (.inl r))
      subst hs
      exact ⟨s, n, le_rfl, hρy⟩
    | inr a' =>
      obtain rfl : a = a' := hadj
      obtain ⟨s, n', hn', h'⟩ := ih rfl
      exact ⟨s, n', by omega, h'⟩

theorem junction_of_edge {S R : Set (Ring ⊕ Contact)} {e : ℕ} {r : Ring} {y : Ring ⊕ Contact}
    (hadj : blockAdj endRing (.inl r) y) (hd : InDiamond (blockAdj endRing) S R e (.inl r) y) :
    JunctionRetained endRing S R e r := by
  obtain ⟨j, m, hz, hy, hjm⟩ := hd
  exact ⟨j, m + 1, hz, observes_step hadj hy, by omega⟩

theorem channel_of_edge {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {e : ℕ} {a : Contact} {z y : Ring ⊕ Contact}
    (hz : Ends endRing a z) (hy : Ends endRing a y)
    (hd : InDiamond (blockAdj endRing) S R e z y) : ChannelRetained endRing S R e a := by
  obtain ⟨j, m, hzr, hyo, hjm⟩ := hd
  obtain ⟨s, hs⟩ : ∃ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈
      reachWithin (blockAdj endRing) S j := by
    rcases hz with rfl | ⟨s, rfl⟩
    · exact reach_contact hS hzr
    · exact ⟨s, hzr⟩
  obtain ⟨s', m', hm', ho⟩ : ∃ s' m', m' ≤ m ∧
      Observes (blockAdj endRing) R (.inl (endRing (a, s'))) m' := by
    rcases hy with rfl | ⟨s', rfl⟩
    · obtain ⟨s', m', hm', ho⟩ := obs_contact hR hyo
      exact ⟨s', m', by omega, ho⟩
    · exact ⟨s', m, le_rfl, hyo⟩
  exact ⟨j, m', s, s', hs, ho, by omega⟩

/-- [proved-derived; formal-checked] **The Rust's rule keeps every locus a diamond edge reads.**
When the seeded contact blocks come with their end rings and no receiver is a contact block, a
locus read by an edge of the causal diamond is retained by `Diamond::retains`. -/
theorem retained_of_reads {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {e : ℕ} {ℓ : Locus Ring Contact}
    {z y : Ring ⊕ Contact} (hr : Reads endRing ℓ z y)
    (hd : InDiamond (blockAdj endRing) S R e z y) : Retained endRing S R e ℓ := by
  cases ℓ with
  | element r =>
    obtain ⟨rfl, rfl⟩ := hr
    exact hd
  | junction r =>
    obtain ⟨rfl, hadj⟩ := hr
    exact junction_of_edge hadj hd
  | channel a => exact channel_of_edge hS hR hr.1 hr.2 hd
  | conductance a =>
    obtain ⟨hz, hadj⟩ := hr
    rcases hz with rfl | ⟨s, rfl⟩
    · have hy : Ends endRing a y := by
        cases y with
        | inl r =>
          obtain ⟨s, hs⟩ := (hadj : ∃ b, endRing (a, b) = r)
          exact Or.inr ⟨s, by rw [hs]⟩
        | inr a' =>
          obtain rfl : a = a' := hadj
          exact Or.inl rfl
      exact Or.inl (channel_of_edge hS hR (Or.inl rfl) hy hd)
    · exact Or.inr ⟨s, junction_of_edge hadj hd⟩

end Rule

/-! ## 4. The release, and the release laws on the concrete medium -/

section Release

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}

open Classical in
/-- [definition] **The release of a medium's loci** (`Constitution::release`): a released element's
`W_s`, slices and `W_c` and a released channel's `C`, `D`, `K` become zero; the junctions, the
conductances, the channel embeddings, the sheet classes and the tick length are declared and stay. -/
def release (keep : Locus Ring Contact → Prop) (μ : Medium endRing V Ch ρ) :
    Medium endRing V Ch ρ where
  channel := μ.channel
  Y := μ.Y
  G := μ.G
  h := μ.h
  Ws r := if keep (.element r) then μ.Ws r else 0
  A r := if keep (.element r) then μ.A r else 0
  σ := μ.σ
  Wc r := if keep (.element r) then μ.Wc r else 0
  C a := if keep (.channel a) then μ.C a else 0
  D a := if keep (.channel a) then μ.D a else 0
  K a := if keep (.channel a) then μ.K a else 0

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ] in
/-- [proved-derived; formal-checked] The release of an admissible medium is admissible. -/
theorem release_admissible {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    (keep : Locus Ring Contact → Prop) : (release keep μ).Admissible where
  Ws_passive r v := by
    by_cases hk : keep (.element r) <;> simp [release, hk, hμ.Ws_passive r v]
  A_skew r i v := by
    by_cases hk : keep (.element r) <;> simp [release, hk, hμ.A_skew r i v]
  C_psd a v := by
    by_cases hk : keep (.channel a) <;> simp [release, hk, hμ.C_psd a v]
  D_psd a v := by
    by_cases hk : keep (.channel a) <;> simp [release, hk, hμ.D_psd a v]
  K_psd a v := by
    by_cases hk : keep (.channel a) <;> simp [release, hk, hμ.K_psd a v]
  C_symm a x y := by
    by_cases hk : keep (.channel a) <;> simp [release, hk, hμ.C_symm a x y]
  K_symm a x y := by
    by_cases hk : keep (.channel a) <;> simp [release, hk, hμ.K_symm a x y]
  Y_pos := hμ.Y_pos
  G_pos := hμ.G_pos
  h_pos := hμ.h_pos
  channel := hμ.channel

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem agreeOn_release {μ : Medium endRing V Ch ρ} {keep : Locus Ring Contact → Prop}
    {ℓ : Locus Ring Contact} (hk : keep ℓ) : AgreeOn (release keep μ) μ ℓ := by
  classical
  cases ℓ with
  | element r => exact ⟨if_pos hk, if_pos hk, rfl, if_pos hk⟩
  | junction r => rfl
  | channel a => exact ⟨if_pos hk, if_pos hk, if_pos hk, fun _ => rfl⟩
  | conductance a => rfl

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] **The release keeps every diamond edge.** Under the Rust's
rule (`retained_of_reads`), the released medium's block operator agrees with the medium's on every
edge of the causal diamond (`blockOp_agree`). -/
theorem blockOp_release {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {e : ℕ} {y z : Ring ⊕ Contact}
    (hd : InDiamond (blockAdj endRing) S R e z y) :
    blockOp (release_admissible hμ (Retained endRing S R e)) y z = blockOp hμ y z :=
  blockOp_agree (release_admissible hμ _) hμ rfl fun _ hℓ => agreeOn_release (retained_of_reads hS hR hℓ hd)

/-- [proved-derived; formal-checked] **The release is indistinguishable on the concrete word**
(`hnn::retention::collapse`, `Diamond::of`, `Diamond::opened`). Releasing every locus the Rust's
rule does not retain changes no admitted reading of the concrete word at any epoch `t ≤ e`
(`TickBlocks.fieldTick_release_past_diamond`). -/
theorem release_indistinguishable {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {X : Change endRing V Ch}
    (hX : SupportedIn (toBlocks X) S)
    {g : (b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b)} (hg : SupportedIn g R)
    {e t : ℕ} (ht : t ≤ e) :
    pair g (toBlocks ((fieldTick (release (Retained endRing S R e) μ))^[t] X)) =
      pair g (toBlocks ((fieldTick μ)^[t] X)) :=
  fieldTick_release_past_diamond hμ (release_admissible hμ _) hX hg ht
    fun _ _ hd => blockOp_release hμ hS hR hd

/-! ### The class family: the medium at its sheet classes -/

/-- [definition] The medium at the sheet classes `c` (the class configuration of `Retention`). -/
def withSheets (μ : Medium endRing V Ch ρ) (c : Ring → ρ → ℝ) : Medium endRing V Ch ρ :=
  { μ with σ := c }

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ] in
theorem withSheets_admissible {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    (c : Ring → ρ → ℝ) : (withSheets μ c).Admissible :=
  ⟨hμ.Ws_passive, hμ.A_skew, hμ.C_psd, hμ.D_psd, hμ.K_psd, hμ.C_symm, hμ.K_symm, hμ.Y_pos,
    hμ.G_pos, hμ.h_pos, hμ.channel⟩

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] [Fintype ρ]
  [∀ r, FiniteDimensional ℝ (V r)] [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem agreeOn_withSheets {μ μ' : Medium endRing V Ch ρ} {ℓ : Locus Ring Contact}
    (h : AgreeOn μ μ' ℓ) (c : Ring → ρ → ℝ) : AgreeOn (withSheets μ c) (withSheets μ' c) ℓ := by
  cases ℓ with
  | element r => exact ⟨h.1, h.2.1, rfl, h.2.2.2⟩
  | junction r => exact h
  | channel a => exact h
  | conductance a => exact h

open Classical in
/-- [definition] **The concrete operand family** (`Retention.readOp`'s `op`): a medium read at the
sheet classes `c` on the edge `z → y`, the tick's block operator there; zero off the admissible
media. -/
def mediumOp (c : Ring → ρ → ℝ) (y z : Ring ⊕ Contact) (μ : Medium endRing V Ch ρ) :
    BlockM endRing V Ch z →ₗ[ℝ] BlockM endRing V Ch y :=
  if hμ : μ.Admissible then blockOp (withSheets_admissible hμ c) y z else 0

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] On an admissible medium the family reads the concrete tick
at every class configuration. -/
theorem readOp_uniform {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (c : Ring → ρ → ℝ) :
    readOp mediumOp c (fun _ _ => μ) = blockOp (withSheets_admissible hμ c) := by
  funext y z
  simp [readOp, mediumOp, hμ]

omit [Fintype Ring] in
theorem lociSparse_uniform (μ : Medium endRing V Ch ρ) :
    LociSparse (blockAdj endRing) mediumOp (fun _ _ => μ) := by
  intro c y z h
  simp only [mediumOp]
  split_ifs with hμ
  · exact blockOp_sparse _ y z h
  · rfl

/-- [proved-derived; formal-checked] Under the continuing rule (`Diamond::continuing`,
`e_last = 2 |B|`) the released medium reads the same as the medium on every walk edge, at every
class configuration. -/
theorem mediumOp_release_on_walk {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) (c : Ring → ρ → ℝ) (y z : Ring ⊕ Contact)
    (hw : OnWalk (blockAdj endRing) S R z y) :
    mediumOp c y z (release (Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact))) μ) =
      mediumOp c y z μ := by
  have hd := (inDiamond_continuing_iff (adj := blockAdj endRing) S R z y).mpr hw
  unfold mediumOp
  rw [dif_pos (release_admissible hμ _), dif_pos hμ]
  exact blockOp_agree (withSheets_admissible (release_admissible hμ _) c)
    (withSheets_admissible hμ c) rfl fun _ hℓ =>
    agreeOn_withSheets (agreeOn_release (retained_of_reads hS hR hℓ hd)) c

/-- [proved-derived; formal-checked] **The continuing release is indistinguishable on the concrete
chain** (`Diamond::continuing`, `Opens::OnMotion`; `Retention.continuing_release_indistinguishable`
read on the concrete medium with the Rust's per-locus release). Over any chain of words, each at
its own sheet classes and opened on the last one's end plus a source moment, releasing every locus
the continuing rule does not retain changes no admitted reading of any later word at any epoch. -/
theorem continuing_release_indistinguishable {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R)
    (ws : List ((Ring → ρ → ℝ) × ℕ × ((b : Ring ⊕ Contact) → BlockM endRing V Ch b)))
    (hws : ∀ w ∈ ws, SupportedIn w.2.2 S) (c : Ring → ρ → ℝ)
    {u : (b : Ring ⊕ Contact) → BlockM endRing V Ch b} (hu : SupportedIn u S) (t : ℕ)
    {g : (b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b)} (hg : SupportedIn g R) :
    pair g (trajectory (readOp mediumOp c
        (fun _ _ => release (Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact))) μ))
        (chainEnd mediumOp
          (fun _ _ => release (Retained endRing S R (2 * Fintype.card (Ring ⊕ Contact))) μ)
          0 ws + u) t) =
      pair g (trajectory (readOp mediumOp c (fun _ _ => μ))
        (chainEnd mediumOp (fun _ _ => μ) 0 ws + u) t) := by
  have hagree := mediumOp_release_on_walk hμ hS hR
  have h0 : SupportedIn (0 : (b : Ring ⊕ Contact) → BlockM endRing V Ch b)
      (reachAll (blockAdj endRing) S) := fun _ _ => rfl
  have hch := chain_agrees_on_walk (lociSparse_uniform _) (lociSparse_uniform μ)
    (fun c y z hw => hagree c y z hw) ws hws h0 h0 fun _ _ => rfl
  have hu' : SupportedIn u (reachAll (blockAdj endRing) S) := fun b hb =>
    hu b fun hbS => hb (subset_reachAll S hbS)
  have hadd : ∀ v : (b : Ring ⊕ Contact) → BlockM endRing V Ch b,
      SupportedIn v (reachAll (blockAdj endRing) S) →
        SupportedIn (v + u) (reachAll (blockAdj endRing) S) := fun v hv b hb => by
    simp [hv b hb, hu' b hb]
  have h := trajectory_agrees_on_walk (sparse_readOp (lociSparse_uniform _) c)
    (sparse_readOp (lociSparse_uniform μ) c) (fun y z hw => hagree c y z hw) (hadd _ hch.1)
    (hadd _ hch.2.1) (fun b hb => by rw [Pi.add_apply, Pi.add_apply, hch.2.2 b hb]) t
  exact pair_agrees_on_observers hg h.2.2

end Release

/-! ## 5. The deposit per locus descends through the release -/

section DataAgree

variable {B : Type*} [Fintype B] [DecidableEq B] {adj : B → B → Prop}
variable {M : B → Type*} [∀ b, AddCommGroup (M b)] [∀ b, Module ℝ (M b)]

/-- [proved-derived; formal-checked] **A deposit's data agree on every declared edge** when two
sparse ticks agree on the causal diamond: each datum is a feature at a block that still observes a
receiver and a swept covector at a block already reached from a source
(`Propagation.trajectory_agrees_where_observed`, `sweep_agrees_where_reached`). -/
theorem depositData_agree {T T' : BlockOp ℝ M} (hT : Sparse adj T) (hT' : Sparse adj T')
    {x₀ : (b : B) → M b} {S R : Set B} (hx : SupportedIn x₀ S) {e : ℕ}
    {rd : List (ℕ × ((b : B) → Module.Dual ℝ (M b)))} (hrd : Admitted R e rd)
    (hagree : ∀ y z, InDiamond adj S R e z y → T' y z = T y z) {z y : B} (hadj : adj z y) :
    depositData adj T' x₀ S R rd z y = depositData adj T x₀ S R rd z y := by
  rw [depositData, depositData]
  refine List.flatMap_congr fun r hr => List.map_congr_left fun k hk => ?_
  have hk' : k ∈ windowTicks adj S R r.1 z y := hk
  simp only [windowTicks, List.mem_filter, List.mem_range, decide_eq_true_eq] at hk'
  obtain ⟨hkt, hz, hy⟩ := hk'
  have htr := (hrd r hr).1
  refine Prod.ext ?_ ?_
  · exact trajectory_agrees_where_observed hT hT' hx hagree (by omega)
      (observes_mono (by omega) (observes_step hadj hy))
  · exact sweep_agrees_where_reached hT hT' (hrd r hr).2 hagree (by omega)
      (reachWithin_mono (by omega) (reachWithin_step hz hadj))

end DataAgree

/-- [definition] A family of deposit data over the block edges: on `z → y`, features at `z` and
covectors at `y`. -/
abbrev EdgeData {Ring Contact : Type u} (endRing : Contact × Bool → Ring) (V : Ring → Type u)
    [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)] (Ch : Contact → Type u)
    [∀ a, NormedAddCommGroup (Ch a)] [∀ a, InnerProductSpace ℝ (Ch a)] : Type u :=
  (y z : Ring ⊕ Contact) → List (BlockM endRing V Ch z × Module.Dual ℝ (BlockM endRing V Ch y))

section Deposit

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}


open Classical in
/-- [definition] **The data a locus deposits from** (`Diamond::element_window`,
`Diamond::channel_window`): the deposit data (`Retention.depositData`) on the edges that read it. -/
def locusData (T : BlockOp ℝ (BlockM endRing V Ch)) (x₀ : (b : Ring ⊕ Contact) → BlockM endRing V Ch b)
    (S R : Set (Ring ⊕ Contact))
    (rd : List (ℕ × ((b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b))))
    (ℓ : Locus Ring Contact) : EdgeData endRing V Ch :=
  fun y z => if Reads endRing ℓ z y then depositData (blockAdj endRing) T x₀ S R rd z y else []

/-- [proved-derived; formal-checked] Every locus's data are the same read through the released
medium. -/
theorem locusData_release {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {x₀ : (b : Ring ⊕ Contact) → BlockM endRing V Ch b}
    (hx : SupportedIn x₀ S) {e : ℕ}
    {rd : List (ℕ × ((b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b)))}
    (hrd : Admitted R e rd) :
    locusData (blockOp (release_admissible hμ (Retained endRing S R e))) x₀ S R rd =
      locusData (blockOp hμ) x₀ S R rd := by
  funext ℓ y z
  simp only [locusData]
  split_ifs with hr
  · exact depositData_agree (blockOp_sparse hμ) (blockOp_sparse _) hx hrd
      (fun _ _ hd => blockOp_release hμ hS hR hd) (reads_adj hr)
  · rfl

omit [DecidableEq Ring] [DecidableEq Contact] [∀ r, FiniteDimensional ℝ (V r)]
  [∀ a, FiniteDimensional ℝ (Ch a)] in
/-- [proved-derived; formal-checked] **Nothing reaches a released locus**: its data are empty. -/
theorem locusData_released {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {e : ℕ}
    {rd : List (ℕ × ((b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b)))}
    (hrd : Admitted R e rd) (T : BlockOp ℝ (BlockM endRing V Ch))
    (x₀ : (b : Ring ⊕ Contact) → BlockM endRing V Ch b) {ℓ : Locus Ring Contact}
    (hℓ : ¬ Retained endRing S R e ℓ) : locusData T x₀ S R rd ℓ = fun _ _ => [] := by
  funext y z
  simp only [locusData]
  split_ifs with hr
  · exact depositData_eq_nil T x₀ hrd fun hd => hℓ (retained_of_reads hS hR hr hd)
  · rfl

/-- [definition] **The deposit on the learned loci** (`Constitution::deposited`): each element's
`(W_s, A, W_c)` and each channel's `(C, D, K)` move by its own law from the data that reached it;
the declared operands stay. -/
def deposited
    (Φe : (r : Ring) → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r) →
      EdgeData endRing V Ch → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r))
    (Φc : (a : Contact) → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) →
      EdgeData endRing V Ch → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a))
    (dat : Locus Ring Contact → EdgeData endRing V Ch) (μ : Medium endRing V Ch ρ) :
    Medium endRing V Ch ρ where
  channel := μ.channel
  Y := μ.Y
  G := μ.G
  h := μ.h
  Ws r := (Φe r (μ.Ws r, μ.A r, μ.Wc r) (dat (.element r))).1
  A r := (Φe r (μ.Ws r, μ.A r, μ.Wc r) (dat (.element r))).2.1
  σ := μ.σ
  Wc r := (Φe r (μ.Ws r, μ.A r, μ.Wc r) (dat (.element r))).2.2
  C a := (Φc a (μ.C a, μ.D a, μ.K a) (dat (.channel a))).1
  D a := (Φc a (μ.C a, μ.D a, μ.K a) (dat (.channel a))).2.1
  K a := (Φc a (μ.C a, μ.D a, μ.K a) (dat (.channel a))).2.2

/-- [proved-derived; formal-checked] **The deposit descends through the release on the concrete
medium** (`Retention.deposit_descends` per locus; `hnn::retention::collapse` after
`Constitution::deposited`). For locus laws that keep a locus no datum reaches, releasing after a
deposit is depositing after the release: a retained locus reads the same data either way
(`locusData_release`), and a released locus is reached by none (`locusData_released`). -/
theorem deposit_descends
    (Φe : (r : Ring) → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r) →
      EdgeData endRing V Ch → (V r →L[ℝ] V r) × (ρ → V r →L[ℝ] V r) × (V r →L[ℝ] V r))
    (Φc : (a : Contact) → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) →
      EdgeData endRing V Ch → (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a) × (Ch a →L[ℝ] Ch a))
    (hΦe : ∀ r p, Φe r p (fun _ _ => []) = p) (hΦc : ∀ a p, Φc a p (fun _ _ => []) = p)
    {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) {S R : Set (Ring ⊕ Contact)}
    (hS : ∀ a, (.inr a : Ring ⊕ Contact) ∈ S → ∀ s, (.inl (endRing (a, s)) : Ring ⊕ Contact) ∈ S)
    (hR : ∀ a, (.inr a : Ring ⊕ Contact) ∉ R) {x₀ : (b : Ring ⊕ Contact) → BlockM endRing V Ch b}
    (hx : SupportedIn x₀ S) {e : ℕ}
    {rd : List (ℕ × ((b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b)))}
    (hrd : Admitted R e rd) :
    release (Retained endRing S R e) (deposited Φe Φc (locusData (blockOp hμ) x₀ S R rd) μ) =
      deposited Φe Φc
        (locusData (blockOp (release_admissible hμ (Retained endRing S R e))) x₀ S R rd)
        (release (Retained endRing S R e) μ) := by
  classical
  rw [locusData_release hμ hS hR hx hrd]
  have hrel : ∀ ℓ, ¬ Retained endRing S R e ℓ → locusData (blockOp hμ) x₀ S R rd ℓ =
      fun _ _ => [] := fun ℓ hℓ => locusData_released hS hR hrd _ x₀ hℓ
  simp only [release, deposited, Medium.mk.injEq]
  refine ⟨trivial, trivial, trivial, trivial, funext fun r => ?_, funext fun r => ?_, trivial,
    funext fun r => ?_,
    funext fun a => ?_, funext fun a => ?_, funext fun a => ?_⟩ <;>
  first
  | (by_cases hk : Retained endRing S R e (.element r)
     · simp only [hk, if_true]
     · simp only [hk, if_false, hrel _ hk, hΦe])
  | (by_cases hk : Retained endRing S R e (.channel a)
     · simp only [hk, if_true]
     · simp only [hk, if_false, hrel _ hk, hΦc])

end Deposit

#print axioms reads_adj
#print axioms blockOp_agree
#print axioms opSub_reads
#print axioms retained_of_reads
#print axioms release_admissible
#print axioms blockOp_release
#print axioms release_indistinguishable
#print axioms readOp_uniform
#print axioms mediumOp_release_on_walk
#print axioms continuing_release_indistinguishable
#print axioms depositData_agree
#print axioms locusData_release
#print axioms locusData_released
#print axioms deposit_descends

end Holonics.HNN.LocusMap
