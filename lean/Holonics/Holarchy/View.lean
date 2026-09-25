import Holonics.Holarchy.Join
import Holonics.Foundation.HodgeReceiver
import Holonics.Aeon.Clock.Epoch

/-!
# Holarchy.View: a Holarchy's quantities belong to the receiver

[definition] Object 11 of `docs/ELEMENTARY_OBJECTS.md`, second half. A Holarchy has no fixed count,
mass or category. A **grain** groups the regions of the glued complex into blocks (`Grain`); a
**receiver** reads a region at an occurrence (`RegionReceiver`); its **clock** is an aeon of the
parametric complex together with the receiver's section, a cut clock
(`Aeon/Clock/Epoch.CutClock`): the receiver ticks where the aeon crosses its section, and the ticks
cut the aeon into epochs (`Aeon/Clock/Epoch.aeonSection`). `view receiver grain aeon section`
returns, at every tick, the occurrence it reads, the epoch that tick opens, the constituent faces
(the receiver's reading of every block), the interface flux (each block's flux through its own
boundary) and the unresolved classes (the blocks the receiver does not separate from a given
block).

`count` is defined only under a partition the receiver certifies (`Certified`): **finite**,
**exhaustive** (every region lies in a block and every block is occupied), **disjoint** and
**distinguishing** (the receiver returns different faces on different blocks). Otherwise it
returns `unresolved`. `refine` passes from a fine grain to a coarse one through a restriction of
blocks, each fine block lying inside the coarse block it restricts to: the flux reading always
closes its scale square (`refine_flux`), and a reading that separates a merged fibre has no coarse
reading (`refine_defect_witness`, `Holon/Restriction.descent_defect_refutes_factoring`).

[proved-derived; formal-checked]

* **The telescoping join.** At every grain that partitions the regions, the block chains sum to
  the whole's chain (`sum_blockChain`), so the block fluxes sum to the whole's flux
  (`sum_blockFlux`) — the same number at every grain (`total_flux_grain_independent`). A face
  shared by exactly two blocks enters them with opposite coefficients (`shared_face_cancels`),
  and a face inside one block does not appear in its boundary (`interior_face_silent`): each
  shared face cancels exactly once. The block flux is the divergence paired with the block
  (`blockFlux_stokes`, Stokes on the glued complex) and an exact current has none
  (`blockFlux_exact`). Refining a grain sums the fine fluxes into the coarse one
  (`refine_flux`: the flux reading always closes its scale square). For a Holarchy the total at
  every grain is the sum of the constituents' own fluxes (`holarchy_view_flux`).
* **`count`.** It returns a number only under certification (`count_eq_counted_iff`, which unfolds
  the definition); the content is that the number is the count of distinct faces the receiver
  returns (`certified_count_eq_faces`) and, over finitely many regions, never exceeds their number
  (`certified_count_le_cells`). The view's unresolved classes are all singletons exactly when the
  receiver distinguishes the grain at every tick (`view_unresolved_singleton_iff`).
* **The view's ticks are the aeon's crossings.** The view is indexed by the crossing ticks of the
  aeon at the receiver's section; there are as many as the aeon's forward plus backward
  crossings, their signed count is the section clock's reading, and they cut the aeon into one
  more epoch (`view_ticks`).
* **Count stability with a changing representative.** One grain certified at two ticks keeps its
  count while every face changes (`count_stable_while_faces_move`). On a weighted complex the
  number of harmonic (dormant) classes does not depend on the metric while the harmonic
  representative of one class moves (`count_stable_representative_moves`, composing
  `Foundation/HodgeReceiver.finrank_harmonic_metric_free` and `harmonic_moves_within_class`).
* **A quotient's cardinality depends on the restriction.** The same cells certified at two grains
  count `2` and `4` (`continents_and_islands`); on the `ℤ/pⁿ` tower the restriction of level
  `m + k` to level `m` has `pᵐ` classes of `pᵏ` each (`padic_quotient_card`, composing
  `Foundation/ContinuingTower.padicFibre_card`).

[counterexample; formal-checked] Each hypothesis of `count` is load-bearing: a witness keeps the
other three and drops one, and `count` returns `unresolved` where the bare number of blocks would
misreport — infinitely many singletons (`Nat.card` returns the junk `0`, `infinite_witness`), a
region outside every block (`uncovered_witness`), overlapping blocks counting three for two regions
(`overlapping_witness`), and a mass receiver that reads two regions alike (`blind_witness`). A
fine reading that separates two blocks the restriction merges has no coarse reading
(`refine_defect_witness`).

[open] The `Foundation/IwasawaTower` and `Foundation/ExactPartition` owners that also witness
restriction-dependent cardinality live in `HolonicsResearch` and are not imported here.
-/

noncomputable section

namespace Holonics.HolarchyCore

open Matrix
open Holonics.HolonCore

/-! ## 1. Grains and the certified count -/

section Count

variable {Cell Block Face : Type*}

/-- [definition] **A grain**: the blocks into which a receiver groups the regions. -/
structure Grain (Cell Block : Type*) where
  blocks : Block → Finset Cell

/-- [definition] Every region lies in a block, and every block is occupied. -/
def Grain.Exhaustive (g : Grain Cell Block) : Prop :=
  (∀ c, ∃ b, c ∈ g.blocks b) ∧ ∀ b, (g.blocks b).Nonempty

/-- [definition] Distinct blocks share no region. -/
def Grain.Disjoint (g : Grain Cell Block) : Prop :=
  ∀ b b', b ≠ b' → _root_.Disjoint (g.blocks b) (g.blocks b')

/-- [definition] The receiver returns different faces on different blocks. -/
def Grain.Distinguishing (read : Finset Cell → Face) (g : Grain Cell Block) : Prop :=
  Function.Injective fun b => read (g.blocks b)

/-- [definition] **The receiver certifies the partition**: finite, exhaustive, disjoint and
distinguishing. -/
structure Certified (read : Finset Cell → Face) (g : Grain Cell Block) : Prop where
  finite : Finite Block
  exhaustive : g.Exhaustive
  disjoint : g.Disjoint
  distinguishing : g.Distinguishing read

/-- [definition] What `count` returns. -/
inductive CountReturn where
  | counted (n : ℕ)
  | unresolved
  deriving DecidableEq

open Classical in
/-- [definition] **`count`**: the number of blocks under a certified partition, otherwise
unresolved. -/
def count (read : Finset Cell → Face) (g : Grain Cell Block) : CountReturn :=
  if Certified read g then .counted (Nat.card Block) else .unresolved

/-- [definition] `count` returns a number exactly under certification (the definition, unfolded). -/
theorem count_eq_counted_iff (read : Finset Cell → Face) (g : Grain Cell Block) (n : ℕ) :
    count read g = .counted n ↔ Certified read g ∧ Nat.card Block = n := by
  unfold count
  split_ifs with h <;> simp [h]

/-- [definition] Otherwise it is unresolved (the definition, unfolded). -/
theorem count_eq_unresolved_iff (read : Finset Cell → Face) (g : Grain Cell Block) :
    count read g = .unresolved ↔ ¬ Certified read g := by
  unfold count
  split_ifs with h <;> simp [h]

/-- [proved-derived; formal-checked] **The count is the number of distinct faces** the receiver
returns at that grain. -/
theorem certified_count_eq_faces {read : Finset Cell → Face} {g : Grain Cell Block}
    (h : Certified read g) :
    Nat.card Block = Nat.card (Set.range fun b => read (g.blocks b)) :=
  (Nat.card_range_of_injective h.distinguishing).symm

/-- [proved-derived; formal-checked] A certified count never exceeds the number of regions: each
block owns a region of its own. -/
theorem certified_count_le_cells [Finite Cell] {read : Finset Cell → Face}
    {g : Grain Cell Block} (h : Certified read g) : Nat.card Block ≤ Nat.card Cell := by
  classical
  have hrep : ∀ b, ∃ c, c ∈ g.blocks b := fun b => h.exhaustive.2 b
  choose rep hrep using hrep
  apply Nat.card_le_card_of_injective rep
  intro b b' hbb'
  by_contra hne
  exact Finset.disjoint_left.mp (h.disjoint b b' hne) (hrep b) (hbb' ▸ hrep b')

end Count

/-! ## 2. The flux of a grain on the glued complex -/

section Flux

variable {𝕜 : Type*} [Field 𝕜] (K : CellComplex 𝕜) {Block : Type*}

/-- [definition] The oriented chain of one block: the whole's oriented chain restricted to it. -/
def blockChain (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block) (b : Block) : K.C₂ → 𝕜 :=
  fun c => if c ∈ g.blocks b then orient c else 0

/-- [definition] **A block's interface flux**: the current paired with the block's boundary. -/
def blockFlux (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block) (j : K.C₁ → 𝕜) (b : Block) : 𝕜 :=
  j ⬝ᵥ (K.d₂ *ᵥ blockChain K orient g b)

variable {K}

/-- [proved-derived; formal-checked] Over a partition the block chains sum to the whole chain. -/
theorem sum_blockChain [Fintype Block] {g : Grain K.C₂ Block} (hcov : ∀ c, ∃ b, c ∈ g.blocks b)
    (hdis : g.Disjoint) (orient : K.C₂ → 𝕜) :
    ∑ b, blockChain K orient g b = orient := by
  funext c
  obtain ⟨b₀, hb₀⟩ := hcov c
  rw [Finset.sum_apply, Finset.sum_eq_single b₀]
  · simp [blockChain, hb₀]
  · intro b _ hb
    have hc : c ∉ g.blocks b := fun hc =>
      Finset.disjoint_left.mp (hdis b b₀ hb) hc hb₀
    simp [blockChain, hc]
  · simp

/-- [proved-derived; formal-checked] **The telescoping join**: over a partition the block fluxes
sum to the whole's flux. -/
theorem sum_blockFlux [Fintype Block] {g : Grain K.C₂ Block} (hcov : ∀ c, ∃ b, c ∈ g.blocks b)
    (hdis : g.Disjoint) (orient : K.C₂ → 𝕜) (j : K.C₁ → 𝕜) :
    ∑ b, blockFlux K orient g j b = j ⬝ᵥ (K.d₂ *ᵥ orient) := by
  simp only [blockFlux, ← dotProduct_sum, ← mulVec_sum]
  rw [sum_blockChain hcov hdis]

/-- [proved-derived; formal-checked] **The total is the same at every grain**: two partitions of
the same regions return the same total interface flux. -/
theorem total_flux_grain_independent {Block' : Type*} [Fintype Block] [Fintype Block']
    {g : Grain K.C₂ Block} {g' : Grain K.C₂ Block'}
    (hcov : ∀ c, ∃ b, c ∈ g.blocks b) (hdis : g.Disjoint)
    (hcov' : ∀ c, ∃ b, c ∈ g'.blocks b) (hdis' : g'.Disjoint) (orient : K.C₂ → 𝕜)
    (j : K.C₁ → 𝕜) :
    ∑ b, blockFlux K orient g j b = ∑ b, blockFlux K orient g' j b := by
  rw [sum_blockFlux hcov hdis, sum_blockFlux hcov' hdis']

/-- [proved-derived; formal-checked] Face by face, the block boundaries sum to the whole's
boundary. -/
theorem sum_blockBoundary_apply [Fintype Block] {g : Grain K.C₂ Block}
    (hcov : ∀ c, ∃ b, c ∈ g.blocks b) (hdis : g.Disjoint) (orient : K.C₂ → 𝕜) (e : K.C₁) :
    ∑ b, (K.d₂ *ᵥ blockChain K orient g b) e = (K.d₂ *ᵥ orient) e := by
  rw [← Finset.sum_apply, ← mulVec_sum, sum_blockChain hcov hdis]

/-- [proved-derived; formal-checked] **A shared face cancels exactly once.** If a face lies inside
the whole (no coefficient in the whole's boundary) and only two blocks touch it, it enters their
boundaries with opposite coefficients, so its flux leaves one block exactly as it enters the other.
-/
theorem shared_face_cancels [Fintype Block] {g : Grain K.C₂ Block}
    (hcov : ∀ c, ∃ b, c ∈ g.blocks b) (hdis : g.Disjoint) (orient : K.C₂ → 𝕜) (e : K.C₁)
    (hinterior : (K.d₂ *ᵥ orient) e = 0) {b b' : Block} (hbb' : b ≠ b')
    (honly : ∀ b'', b'' ≠ b → b'' ≠ b' → (K.d₂ *ᵥ blockChain K orient g b'') e = 0) :
    (K.d₂ *ᵥ blockChain K orient g b) e = -(K.d₂ *ᵥ blockChain K orient g b') e := by
  have h := sum_blockBoundary_apply hcov hdis orient e
  rw [hinterior, Finset.sum_eq_add_of_mem b b' (Finset.mem_univ _) (Finset.mem_univ _) hbb'
    (fun c _ hc => honly c hc.1 hc.2)] at h
  linear_combination h

/-- [proved-derived; formal-checked] **A face inside one block is silent in its boundary**: when
every block other than `b` misses it and it lies inside the whole, it does not appear in `∂b`. -/
theorem interior_face_silent [Fintype Block] {g : Grain K.C₂ Block}
    (hcov : ∀ c, ∃ b, c ∈ g.blocks b) (hdis : g.Disjoint) (orient : K.C₂ → 𝕜) (e : K.C₁)
    (hinterior : (K.d₂ *ᵥ orient) e = 0) (b : Block)
    (hothers : ∀ b'', b'' ≠ b → (K.d₂ *ᵥ blockChain K orient g b'') e = 0) :
    (K.d₂ *ᵥ blockChain K orient g b) e = 0 := by
  have h := sum_blockBoundary_apply hcov hdis orient e
  rwa [hinterior, Finset.sum_eq_single b (fun c _ hc => hothers c hc) (by simp)] at h

/-- [proved-derived; formal-checked] **Stokes on the glued complex**: a block's flux is the
divergence `∂₂ᵀ j` paired with the block (`Objects/Pairing.coordinate_stokes`). -/
theorem blockFlux_stokes (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block) (j : K.C₁ → 𝕜)
    (b : Block) : blockFlux K orient g j b = (K.d₂ᵀ *ᵥ j) ⬝ᵥ blockChain K orient g b :=
  (Objects.Pairing.coordinate_stokes _ _ _).symm

/-- [proved-derived; formal-checked] An exact current has zero flux through every block at every
grain (`CellComplex.exact_flux_zero`). -/
theorem blockFlux_exact (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block) (φ : K.C₀ → 𝕜)
    (b : Block) : blockFlux K orient g (K.d₁ᵀ *ᵥ φ) b = 0 :=
  K.exact_flux_zero φ _

end Flux

/-! ## 3. Refinement: the commuting scale square or its defect -/

section Refine

variable {Cell Fine Coarse V : Type*}

/-- [definition] **A restriction of grains**: every fine block lies in the coarse block it
restricts to. -/
structure GrainRestriction (fine : Grain Cell Fine) (coarse : Grain Cell Coarse) where
  π : Fine → Coarse
  sub : ∀ b, fine.blocks b ⊆ coarse.blocks (π b)

variable {𝕜 : Type*} [Field 𝕜] {K : CellComplex 𝕜}

/-- [proved-derived; formal-checked] **The flux reading always closes its scale square**: a coarse
block's flux is the sum of the fluxes of the fine blocks restricting to it, when the fine grain
is a partition and the coarse blocks are disjoint. -/
theorem refine_flux [Fintype Fine] [DecidableEq Coarse] {fine : Grain K.C₂ Fine}
    {coarse : Grain K.C₂ Coarse} (r : GrainRestriction fine coarse)
    (hcov : ∀ c, ∃ b, c ∈ fine.blocks b) (hdis : fine.Disjoint) (hdis' : coarse.Disjoint)
    (orient : K.C₂ → 𝕜) (j : K.C₁ → 𝕜) (B : Coarse) :
    blockFlux K orient coarse j B =
      ∑ b ∈ Finset.univ.filter (fun b => r.π b = B), blockFlux K orient fine j b := by
  have hchain : blockChain K orient coarse B =
      ∑ b ∈ Finset.univ.filter (fun b => r.π b = B), blockChain K orient fine b := by
    funext c
    obtain ⟨b₀, hb₀⟩ := hcov c
    rw [Finset.sum_apply]
    by_cases hB : r.π b₀ = B
    · rw [Finset.sum_eq_single_of_mem b₀ (by simp [hB])]
      · have hcB : c ∈ coarse.blocks B := hB ▸ r.sub b₀ hb₀
        simp [blockChain, hb₀, hcB]
      · intro b _ hb
        have hc : c ∉ fine.blocks b := fun hc =>
          Finset.disjoint_left.mp (hdis b b₀ hb) hc hb₀
        simp [blockChain, hc]
    · have hcB : c ∉ coarse.blocks B := fun hcB =>
        Finset.disjoint_left.mp (hdis' (r.π b₀) B hB) (r.sub b₀ hb₀) hcB
      rw [Finset.sum_eq_zero]
      · simp [blockChain, hcB]
      · intro b hb
        have hb' : r.π b = B := (Finset.mem_filter.mp hb).2
        have hc : c ∉ fine.blocks b := fun hc => by
          have hne : b ≠ b₀ := fun h => hB (h ▸ hb')
          exact Finset.disjoint_left.mp (hdis b b₀ hne) hc hb₀
        simp [blockChain, hc]
  simp only [blockFlux, hchain, mulVec_sum, dotProduct_sum]

end Refine

/-! ## 4. The view over an aeon at the receiver's section -/

section View

open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Reading Holonics.Aeon.Clock.Epoch

variable {𝕜 : Type*} [Field 𝕜] {Face Block : Type*}
variable {V E F : Type*} {P : ParametricComplex V E F}

/-- [definition] **A receiver of regions**: its face of a region at an occurrence. -/
structure RegionReceiver (V Cell Face : Type*) where
  read : V → Finset Cell → Face

/-- [definition] The occurrence reached after `t` steps of a word from `u`. -/
def occurrenceAt (P : ParametricComplex V E F) : V → List (E × Bool) → ℕ → V
  | u, _, 0 => u
  | u, [], _ + 1 => u
  | _, s :: w, t + 1 => occurrenceAt P (P.finish s) w t

/-- [definition] The receiver's ticks along an aeon: its crossings of the receiver's section. -/
abbrev Tick {u v : V} (γ : Aeon P u v) (c : CutClock P) : Type :=
  {t // t ∈ (aeonSection c.clock.form γ).ticks}

/-- [definition] **What the view returns** at each of the receiver's ticks. -/
structure ViewReturn (Tick Block Face 𝕜 V : Type*) where
  /-- The occurrence each tick reads. -/
  occurrence : Tick → V
  /-- The epoch each tick opens. -/
  epoch : Tick → ℕ
  /-- The receiver's face of each block. -/
  faces : Tick → Block → Face
  /-- Each block's flux through its own boundary. -/
  interfaceFlux : Tick → Block → 𝕜
  /-- The blocks the receiver does not separate from a given block. -/
  unresolved : Tick → Block → Set Block

/-- [definition] **`view receiver grain aeon section`** on a glued complex with an oriented whole
chain and the current at each occurrence. The receiver's clock is the aeon read at its section:
it ticks at the aeon's crossings, and each tick reads the occurrence it reaches and opens an
epoch. -/
def view (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜) (current : V → K.C₁ → 𝕜)
    (R : RegionReceiver V K.C₂ Face) (g : Grain K.C₂ Block) {u v : V} (γ : Aeon P u v)
    (c : CutClock P) : ViewReturn (Tick γ c) Block Face 𝕜 V where
  occurrence k := occurrenceAt P u γ.steps k.1
  epoch k := epochOf (aeonSection c.clock.form γ).ticks k.1
  faces k b := R.read (occurrenceAt P u γ.steps k.1) (g.blocks b)
  interfaceFlux k b := blockFlux K orient g (current (occurrenceAt P u γ.steps k.1)) b
  unresolved k b := {b' | R.read (occurrenceAt P u γ.steps k.1) (g.blocks b') =
    R.read (occurrenceAt P u γ.steps k.1) (g.blocks b)}

/-- [proved-derived; formal-checked] **The view's ticks are the aeon's crossings of the receiver's
section**: as many as its forward plus backward crossings, with the section clock's reading as
their signed count, cutting the aeon into one more epoch than ticks. -/
theorem view_ticks {u v : V} (γ : Aeon P u v) (c : CutClock P) :
    Nat.card (Tick γ c) =
        forwardCrossings c.clock.form γ.steps + backwardCrossings c.clock.form γ.steps ∧
      reading c.clock γ =
        (forwardCrossings c.clock.form γ.steps : ℤ) - backwardCrossings c.clock.form γ.steps ∧
      (Finset.range (γ.steps.length + 1)).image (epochOf (aeonSection c.clock.form γ).ticks) =
        Finset.range (forwardCrossings c.clock.form γ.steps +
          backwardCrossings c.clock.form γ.steps + 1) := by
  refine ⟨?_, reading_eq_crossings c γ, aeon_epochs_attained c γ⟩
  rw [Nat.card_eq_fintype_card, Fintype.card_coe]
  exact card_crossingTicks c.isCut γ.steps

/-- [proved-derived; formal-checked] **The unresolved classes are singletons exactly when the
receiver distinguishes the grain at every tick.** -/
theorem view_unresolved_singleton_iff (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜)
    (current : V → K.C₁ → 𝕜) (R : RegionReceiver V K.C₂ Face) (g : Grain K.C₂ Block)
    {u v : V} (γ : Aeon P u v) (c : CutClock P) :
    (∀ k b, (view K orient current R g γ c).unresolved k b = {b}) ↔
      ∀ k : Tick γ c, g.Distinguishing (R.read ((view K orient current R g γ c).occurrence k)) := by
  constructor
  · intro h k b b' hbb'
    have := h k b'
    have hmem : b ∈ (view K orient current R g γ c).unresolved k b' := hbb'
    rw [this] at hmem
    exact hmem
  · intro h k b
    ext b'
    simp only [view, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    exact ⟨fun hb => h k hb, fun hb => hb ▸ rfl⟩

/-- [proved-derived; formal-checked] **At every tick and every partitioning grain the view's
interface fluxes total the whole's flux.** -/
theorem view_flux_total [Fintype Block] (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜)
    (current : V → K.C₁ → 𝕜) (R : RegionReceiver V K.C₂ Face) {g : Grain K.C₂ Block}
    (hcov : ∀ c, ∃ b, c ∈ g.blocks b) (hdis : g.Disjoint) {u v : V} (γ : Aeon P u v)
    (c : CutClock P) (k : Tick γ c) :
    ∑ b, (view K orient current R g γ c).interfaceFlux k b =
      current ((view K orient current R g γ c).occurrence k) ⬝ᵥ (K.d₂ *ᵥ orient) :=
  sum_blockFlux hcov hdis orient _

variable {U σA ρA πA αA σB ρB πB αB τ : Type*}
  [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA]
  [Fintype σB] [Fintype ρB] [Fintype πB] [Fintype αB] [Fintype τ] [DecidableEq τ]

/-- [proved-derived; formal-checked] **A Holarchy's view totals the constituents' own fluxes at
every grain and every tick**: the telescoping join composed with `Holarchy.whole_flux`. -/
theorem holarchy_view_flux [Fintype Block] {A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA}
    {B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB} (h : Holarchy A B)
    (current : V → h.decl.glued.C₁ → 𝕜) (R : RegionReceiver V h.decl.glued.C₂ Face)
    {g : Grain h.decl.glued.C₂ Block} (hcov : ∀ c, ∃ b, c ∈ g.blocks b) (hdis : g.Disjoint)
    {u v : V} (γ : Aeon P u v) (c : CutClock P) (k : Tick γ c) :
    ∑ b, (view h.decl.glued h.wholeInterior current R g γ c).interfaceFlux k b =
      (h.decl.leftCells.m₁ᵀ *ᵥ current (occurrenceAt P u γ.steps k.1)) ⬝ᵥ
          (A.complex.d₂ *ᵥ A.interior) +
        (h.decl.rightCells.m₁ᵀ *ᵥ current (occurrenceAt P u γ.steps k.1)) ⬝ᵥ
          (B.complex.d₂ *ᵥ B.interior) := by
  rw [view_flux_total _ _ _ _ hcov hdis, (h.whole_flux _).1]
  rfl

end View

/-! ## 5. Witnesses: every hypothesis of `count` is load-bearing -/

section CountWitnesses

/-- [counterexample; formal-checked] **Not finite.** Singletons of `ℕ` read by their sum: the
partition is exhaustive, disjoint and distinguishing, but infinite, so `count` is unresolved;
the bare `Nat.card` would return the junk value `0` for an inhabited population. -/
theorem infinite_witness :
    let g : Grain ℕ ℕ := ⟨fun b => {b}⟩
    let read : Finset ℕ → ℕ := fun s => s.sum id
    g.Exhaustive ∧ g.Disjoint ∧ g.Distinguishing read ∧ ¬ Finite ℕ ∧
      count read g = .unresolved ∧ Nat.card ℕ = 0 := by
  intro g read
  refine ⟨⟨fun c => ⟨c, by simp [g]⟩, fun b => ⟨b, by simp [g]⟩⟩,
    fun b b' h => by simpa [g] using h, fun b b' h => by simpa [g, read] using h,
    not_finite_iff_infinite.mpr inferInstance,
    (count_eq_unresolved_iff _ _).mpr fun hc => not_finite_iff_infinite.mpr inferInstance hc.finite,
    Nat.card_eq_zero_of_infinite⟩

/-- [counterexample; formal-checked] **Not exhaustive.** One block holding only `false`: finite,
disjoint and distinguishing, but `true` lies in no block, so `count` is unresolved where the bare
number `1` would omit a region. -/
theorem uncovered_witness :
    let g : Grain Bool Unit := ⟨fun _ => {false}⟩
    let read : Finset Bool → ℕ := Finset.card
    Finite Unit ∧ g.Disjoint ∧ g.Distinguishing read ∧ ¬ g.Exhaustive ∧
      count read g = .unresolved ∧ Nat.card Unit = 1 := by
  intro g read
  refine ⟨inferInstance, fun b b' h => absurd (Subsingleton.elim b b') h,
    fun b b' _ => Subsingleton.elim b b', fun h => ?_, ?_, Nat.card_unique⟩
  · obtain ⟨b, hb⟩ := h.1 true
    simp [g] at hb
  · rw [count_eq_unresolved_iff]
    intro hc
    obtain ⟨b, hb⟩ := hc.exhaustive.1 true
    simp [g] at hb

/-- [counterexample; formal-checked] **Not disjoint.** Blocks `{false, true}`, `{false}`,
`{true}` read as themselves: finite, exhaustive and distinguishing, but overlapping, so `count`
is unresolved where the bare number `3` would count two regions three times. -/
theorem overlapping_witness :
    let g : Grain Bool (Fin 3) := ⟨![{false, true}, {false}, {true}]⟩
    let read : Finset Bool → Finset Bool := id
    Finite (Fin 3) ∧ g.Exhaustive ∧ g.Distinguishing read ∧ ¬ g.Disjoint ∧
      count read g = .unresolved ∧ Nat.card (Fin 3) = 3 ∧ Nat.card Bool = 2 := by
  intro g read
  have hnot : ¬ g.Disjoint := fun h => by
    have := h 0 1 (by decide)
    simp [g] at this
  refine ⟨inferInstance, ⟨fun c => ⟨0, by cases c <;> simp [g]⟩, fun b => ?_⟩, ?_, hnot,
    (count_eq_unresolved_iff _ _).mpr fun hc => hnot hc.disjoint, Nat.card_eq_fintype_card.trans
      (by simp), Nat.card_eq_fintype_card.trans (by simp)⟩
  · fin_cases b <;> simp [g]
  · show ∀ b b' : Fin 3, g.blocks b = g.blocks b' → b = b'
    decide

/-- [counterexample; formal-checked] **Not distinguishing.** The singletons of `Bool` read by
their mass (cardinality): finite, exhaustive and disjoint, but both blocks read `1`, so `count` is
unresolved where the bare number `2` would count what the receiver cannot tell apart. -/
theorem blind_witness :
    let g : Grain Bool Bool := ⟨fun b => {b}⟩
    let read : Finset Bool → ℕ := Finset.card
    Finite Bool ∧ g.Exhaustive ∧ g.Disjoint ∧ ¬ g.Distinguishing read ∧
      count read g = .unresolved ∧ Nat.card Bool = 2 := by
  intro g read
  have hnot : ¬ g.Distinguishing read := fun h => by
    have := @h false true (by simp [g, read])
    exact Bool.false_ne_true this
  refine ⟨inferInstance, ⟨fun c => ⟨c, by simp [g]⟩, fun b => ⟨b, by simp [g]⟩⟩,
    fun b b' h => by simpa [g] using h, hnot,
    (count_eq_unresolved_iff _ _).mpr fun hc => hnot hc.distinguishing,
    Nat.card_eq_fintype_card.trans (by simp)⟩

/-- [counterexample; formal-checked] **A reading that separates a merged fibre.** The singletons
of `Bool` restrict to one coarse block; the fine reading `false ↦ 0`, `true ↦ 1` separates the
merged pair, so no coarse reading reproduces it (`Holon/Restriction.descent_defect_refutes_factoring`).
-/
theorem refine_defect_witness :
    let fine : Grain Bool Bool := ⟨fun b => {b}⟩
    let coarse : Grain Bool Unit := ⟨fun _ => Finset.univ⟩
    let r : GrainRestriction fine coarse := ⟨fun _ => (), fun _ => Finset.subset_univ _⟩
    ¬ ∃ ρbar : Unit → ℕ, ∀ b, (fun b : Bool => if b then 1 else 0) b = ρbar (r.π b) := by
  intro fine coarse r
  exact (descent_defect_refutes_factoring r.π (fun b : Bool => if b then 1 else 0)
    (x := false) (y := true) rfl (by simp)).2.2

/-- [established-bounded; formal-checked] **Count stability with moving faces.** The singleton
grain of `Bool` read at two ticks by `s + [true ∈ ·]`: certified at both, counted `2` at both,
while every face moves by `5`. -/
theorem count_stable_while_faces_move :
    let g : Grain Bool Bool := ⟨fun b => {b}⟩
    let read : ℚ → Finset Bool → ℚ := fun s F => s + if true ∈ F then 1 else 0
    count (read 0) g = .counted 2 ∧ count (read 5) g = .counted 2 ∧
      ∀ b, read 0 (g.blocks b) ≠ read 5 (g.blocks b) := by
  intro g read
  have hcert : ∀ s, Certified (read s) g := fun s =>
    ⟨inferInstance, ⟨fun c => ⟨c, by simp [g]⟩, fun b => ⟨b, by simp [g]⟩⟩,
      fun b b' h => by simpa [g] using h,
      fun b b' h => by cases b <;> cases b' <;> simp_all [g, read]⟩
  refine ⟨(count_eq_counted_iff _ _ _).mpr ⟨hcert 0, by simp⟩,
    (count_eq_counted_iff _ _ _).mpr ⟨hcert 5, by simp⟩, fun b => ?_⟩
  cases b <;> norm_num [g, read]

/-- [established-bounded; formal-checked] **Continents and islands.** One receiver (each block
read as itself) certifies two grains of the same four regions, counting `2` and `4`; the fine grain
restricts to the coarse one. The count belongs to the grain. -/
theorem continents_and_islands :
    let coarse : Grain (Fin 4) Bool := ⟨fun b => if b then {2, 3} else {0, 1}⟩
    let fine : Grain (Fin 4) (Fin 4) := ⟨fun i => {i}⟩
    let read : Finset (Fin 4) → Finset (Fin 4) := id
    count read coarse = .counted 2 ∧ count read fine = .counted 4 ∧
      Nonempty (GrainRestriction fine coarse) := by
  intro coarse fine read
  refine ⟨(count_eq_counted_iff _ _ _).mpr ⟨⟨inferInstance, ⟨fun c => ?_, fun b => ?_⟩, ?_, ?_⟩,
      by simp⟩,
    (count_eq_counted_iff _ _ _).mpr ⟨⟨inferInstance, ⟨fun c => ⟨c, by simp [fine]⟩,
      fun b => ⟨b, by simp [fine]⟩⟩, fun b b' h => by simpa [fine] using h,
      fun b b' h => by simpa [fine, read] using h⟩, by simp⟩,
    ⟨⟨fun i => decide (2 ≤ i.val), fun i => ?_⟩⟩⟩
  · fin_cases c
    exacts [⟨false, by simp [coarse]⟩, ⟨false, by simp [coarse]⟩, ⟨true, by simp [coarse]⟩,
      ⟨true, by simp [coarse]⟩]
  · cases b
    exacts [⟨0, by simp [coarse]⟩, ⟨2, by simp [coarse]⟩]
  · intro b b' h
    cases b <;> cases b' <;> simp_all [coarse]
  · intro b b' h
    cases b <;> cases b'
    · rfl
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · rfl
  · fin_cases i <;> simp [fine, coarse]

end CountWitnesses

/-! ## 6. Stable counts, moving representatives and restriction-dependent cardinality -/

section Representatives

open Holonics.Foundation.HodgeReceiver
open Module

/-- [definition] The two-edge line: one vertex cochain `d₀ = [1; 1]`, no faces. -/
def lineD₀ : Matrix (Fin 2) (Fin 1) ℚ := !![1; 1]

/-- [definition] No cells above the edges. -/
def lineD₁ : Matrix (Fin 0) (Fin 2) ℚ := 0

theorem line_dd : lineD₁ * lineD₀ = 0 := by
  ext i; exact i.elim0

/-- [definition] The line under the unit metric. -/
def unitLine : WeightedComplex 1 2 0 := unitMetric lineD₀ lineD₁ line_dd

/-- [definition] The line with its second edge weighted `2`. -/
def weightedLine : WeightedComplex 1 2 0 where
  d₀ := lineD₀
  d₁ := lineD₁
  w₀ := fun _ => 1
  w₁ := ![1, 2]
  w₂ := fun _ => 1
  w₀pos := fun _ => one_pos
  w₁pos := fun i => by fin_cases i <;> norm_num
  w₂pos := fun _ => one_pos
  dd := line_dd

/-- [established-bounded; formal-checked] **Count stability with a changing representative.**
The number of harmonic classes of the line is the same under both metrics
(`finrank_harmonic_metric_free`), while the harmonic representative of the class of `(1, 0)` is
`(1/2, −1/2)` under the unit metric and `(2/3, −1/3)` under the weighted one: both differ from
`(1, 0)` by an exact cochain and they differ from each other. -/
theorem count_stable_representative_moves :
    finrank ℚ weightedLine.harmonic = finrank ℚ unitLine.harmonic ∧
      ![1 / 2, -1 / 2] ∈ unitLine.harmonic ∧ ![2 / 3, -1 / 3] ∈ weightedLine.harmonic ∧
      ![1, 0] - ![1 / 2, -1 / 2] ∈ unitLine.exactPart ∧
      ![1, 0] - ![2 / 3, -1 / 3] ∈ weightedLine.exactPart ∧
      (![1 / 2, -1 / 2] : Fin 2 → ℚ) ≠ ![2 / 3, -1 / 3] := by
  refine ⟨unitLine.finrank_harmonic_metric_free weightedLine rfl rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [WeightedComplex.mem_harmonic_iff]
    refine ⟨?_, by ext i; exact i.elim0⟩
    ext i; fin_cases i
    simp [unitLine, unitMetric, WeightedComplex.codiff₀, lineD₀, Matrix.mulVec, dotProduct]
    norm_num
  · rw [WeightedComplex.mem_harmonic_iff]
    refine ⟨?_, by ext i; exact i.elim0⟩
    ext i; fin_cases i
    simp [weightedLine, WeightedComplex.codiff₀, lineD₀, Matrix.mulVec, dotProduct]
    norm_num
  · refine ⟨![1 / 2], ?_⟩
    ext i; fin_cases i <;> simp [unitLine, unitMetric, lineD₀] <;> norm_num
  · refine ⟨![1 / 3], ?_⟩
    ext i; fin_cases i <;> simp [weightedLine, lineD₀] <;> norm_num
  · intro h
    have := congrFun h 0
    norm_num at this

open Holonics.Foundation.ContinuingTower in
/-- [proved-derived; formal-checked] **A quotient's cardinality depends on the restriction.** On
the `ℤ/pⁿ` tower, restricting level `m + k` to level `m` has exactly `pᵐ` classes, each a fibre
of exactly `pᵏ` elements (`padicFibre_card`); restricting `ℤ/p²` to level `1` or to level `2`
therefore counts `p` or `p²`. -/
theorem padic_quotient_card (p : ℕ) [Fact p.Prime] (m k : ℕ) :
    Nat.card (Set.range fun x : ZMod (p ^ (m + k)) =>
        (padicTower p).restrict (Nat.le_add_right m k) x) = p ^ m ∧
      ∀ face : ZMod (p ^ m), Nat.card { x : ZMod (p ^ (m + k)) //
        (padicTower p).restrict (Nat.le_add_right m k) x = face } = p ^ k := by
  refine ⟨?_, padicFibre_card p m k⟩
  rw [Set.range_eq_univ.mpr (padicTower_restrict_surjective p (Nat.le_add_right m k)),
    Nat.card_univ]
  exact Nat.card_zmod _

open Holonics.Foundation.ContinuingTower in
/-- [proved-derived; formal-checked] Two restrictions of the same population count differently:
`p ≠ p²`. -/
theorem padic_two_restrictions_differ (p : ℕ) [hp : Fact p.Prime] :
    Nat.card (Set.range fun x : ZMod (p ^ (1 + 1)) =>
        (padicTower p).restrict (Nat.le_add_right 1 1) x) ≠
      Nat.card (Set.range fun x : ZMod (p ^ (2 + 0)) =>
        (padicTower p).restrict (Nat.le_add_right 2 0) x) := by
  rw [(padic_quotient_card p 1 1).1, (padic_quotient_card p 2 0).1]
  have h1 : 1 < p := hp.out.one_lt
  exact (Nat.pow_lt_pow_right h1 (by norm_num)).ne

end Representatives

end Holonics.HolarchyCore
