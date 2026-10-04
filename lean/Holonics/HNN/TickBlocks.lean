import Holonics.HNN.Word

/-!
# HNN.TickBlocks: the concrete tick is the tick of a block operator

[definition] #62 comment 5839507068, item 3 (Step 4, #73). `HNN/Word.fieldTick` is one tick of a
word at a cut's fixed operands (an admissible `Medium`). The cone, the pairing, the diamond and the
release are proved in `HNN/Propagation` for an abstract `BlockOp` on a declared block graph. This
file joins the two: the concrete tick is the tick of a `BlockOp` on the ring/contact blocks, sparse
on the word's block graph `Word.blockAdj`, so every block law reads on the concrete tick.

The blocks are those of `Word.BlockZero`: a ring block carries the ring's storage wave and the waves
arriving at its contact ports, `V_r × (Port_r → V_r)`; a contact block carries the contact's
displacement and slip rate, `Ch_a × Ch_a`.

[proved-derived; formal-checked] What is proved.

1. **The local solves are linear.** For an admissible medium the element's solve and the contact's
   solve are unique (`Word.elementSolve_spec`, `Word.transitSolve_spec`), and the relations they
   solve are linear, so the solves are linear in their data (`elementSolve_comb`,
   `transitSolve_comb`).
2. **The tick is linear in the change** at fixed operands: `fieldTick μ (cX + Y) = c fieldTick μ X +
   fieldTick μ Y` (`fieldTick_comb`), through the junction anchor, the storage and port waves, the
   slips and the arrivals.
3. **The change is its blocks.** `toBlocks` and `ofBlocks` are inverse and carry the combination
   (`ofBlocks_toBlocks`, `toBlocks_ofBlocks`, `toBlocks_comb`), and a change vanishes on a block
   exactly when its block is zero (`blockZero_iff`).
4. **The block operator.** `blockOp hμ y z` is block `y` of the tick of the change carried on block
   `z` alone. Its tick is the concrete tick (`tick_blockOp`), it is sparse on `Word.blockAdj`
   (`blockOp_sparse`, from `Word.fieldTick_local`), and the word's iterates are its trajectory
   (`fieldTick_iterate_blocks`).
5. **The block laws on the concrete tick.** The causal cone (`fieldTick_causal_cone`), the exact
   pairing with the swept covector (`fieldTick_pairing`), the exact variation between two admissible
   media on one open change (`fieldTick_variation_exact`), the release past the diamond
   (`fieldTick_release_past_diamond`) and the agreement wherever a block is still observed
   (`fieldTick_agrees_where_observed`).

What it does not cover: the locus-level dependence of `blockOp` on the medium's operands (which
operand moves which block edge), and therefore the readings of the `HNN/Retention` laws stated on
an operand family (`deposit_descends`, `contemporary_read`, `fieldStanding`, `word_opens_at_zero`)
on the concrete medium. Those stay owed in #62.
-/

namespace Holonics.HNN.TickBlocks

open Holonics.Geometry.AffineSwing
open Holonics.HNN.Propagation
open Holonics.HNN.Word
open scoped BigOperators

universe u

section Comb

variable {Ring Contact : Type u}
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
variable {Ch : Contact → Type u}
variable {endRing : Contact × Bool → Ring}

omit [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)] in
theorem Change.ext' {X Y : Change endRing V Ch} (hs : X.s = Y.s) (harr : X.arr = Y.arr)
    (hu : X.u = Y.u) (hw : X.w = Y.w) : X = Y := by
  cases X; cases Y
  simp only at hs harr hu hw
  subst hs harr hu hw
  rfl

theorem portWave_comb (c : ℝ) (arr₁ arr₂ : (e : Contact × Bool) → V (endRing e)) (r : Ring)
    (p : Port endRing r) :
    portWave endRing (fun e => c • arr₁ e + arr₂ e) r p =
      c • portWave endRing arr₁ r p + portWave endRing arr₂ r p := by
  obtain ⟨e, he⟩ := p
  subst he
  rfl

theorem swing_comb {E : Type*} [AddCommGroup E] [Module ℝ E] (c : ℝ) (b₁ b₂ a₁ a₂ : E) :
    swing (c • b₁ + b₂) (c • a₁ + a₂) = c • swing b₁ a₁ + swing b₂ a₂ := by
  simp only [swing]
  module

variable [∀ a, NormedAddCommGroup (Ch a)] [∀ a, InnerProductSpace ℝ (Ch a)]

/-- [definition] The combination `c X + Y` of two changes, field by field. -/
def Change.comb (c : ℝ) (X Y : Change endRing V Ch) : Change endRing V Ch where
  s r := c • X.s r + Y.s r
  arr e := c • X.arr e + Y.arr e
  u a := c • X.u a + Y.u a
  w a := c • X.w a + Y.w a

variable [DecidableEq Ring] [Fintype Contact]

theorem ringAnchor_comb (Y : Ring → ℝ) (G : Contact → ℝ) (c : ℝ) (s₁ s₂ : (r : Ring) → V r)
    (arr₁ arr₂ : (e : Contact × Bool) → V (endRing e)) (r : Ring) :
    ringAnchor Y G (fun r => c • s₁ r + s₂ r) (fun e => c • arr₁ e + arr₂ e) r =
      c • ringAnchor Y G s₁ arr₁ r + ringAnchor Y G s₂ arr₂ r := by
  simp only [ringAnchor, anchor, portWave_comb, smul_add, Finset.sum_add_distrib,
    Finset.smul_sum, smul_smul]
  simp only [mul_comm c, ← smul_smul, ← Finset.smul_sum]
  abel

theorem storageWave_comb (Y : Ring → ℝ) (G : Contact → ℝ) (c : ℝ) (X₁ X₂ : Change endRing V Ch)
    (r : Ring) :
    storageWave Y G (Change.comb c X₁ X₂).s (Change.comb c X₁ X₂).arr r =
      c • storageWave Y G X₁.s X₁.arr r + storageWave Y G X₂.s X₂.arr r := by
  rw [storageWave, show (Change.comb c X₁ X₂).s = fun r => c • X₁.s r + X₂.s r from rfl,
    show (Change.comb c X₁ X₂).arr = fun e => c • X₁.arr e + X₂.arr e from rfl, ringAnchor_comb,
    swing_comb]
  rfl

theorem contrast_comb (Y : Ring → ℝ) (G : Contact → ℝ) (c : ℝ) (X₁ X₂ : Change endRing V Ch)
    (r : Ring) :
    contrast Y G (Change.comb c X₁ X₂).s (Change.comb c X₁ X₂).arr r =
      c • contrast Y G X₁.s X₁.arr r + contrast Y G X₂.s X₂.arr r := by
  rw [contrast, show (Change.comb c X₁ X₂).s = fun r => c • X₁.s r + X₂.s r from rfl,
    show (Change.comb c X₁ X₂).arr = fun e => c • X₁.arr e + X₂.arr e from rfl, ringAnchor_comb,
    contrast, contrast]
  module

theorem endOut_comb (Y : Ring → ℝ) (G : Contact → ℝ) (c : ℝ) (X₁ X₂ : Change endRing V Ch)
    (e : Contact × Bool) :
    endOut Y G (Change.comb c X₁ X₂).s (Change.comb c X₁ X₂).arr e =
      c • endOut Y G X₁.s X₁.arr e + endOut Y G X₂.s X₂.arr e := by
  rw [endOut, show (Change.comb c X₁ X₂).s = fun r => c • X₁.s r + X₂.s r from rfl,
    show (Change.comb c X₁ X₂).arr = fun e => c • X₁.arr e + X₂.arr e from rfl, ringAnchor_comb,
    swing_comb]
  rfl

end Comb

section Solve

variable {Ring Contact ρ : Type u} [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}

/-- [proved-derived; formal-checked] **The element's solve is linear** in its storage wave and
contrast: the drive form is a linear relation and its solution is unique. -/
theorem elementSolve_comb {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (r : Ring) (c : ℝ)
    (b₁ b₂ c₁ c₂ : V r) :
    elementSolve μ r (c • b₁ + b₂) (c • c₁ + c₂) =
      c • elementSolve μ r b₁ c₁ + elementSolve μ r b₂ c₂ := by
  have h₁ := (elementSolve_spec hμ r b₁ c₁).1
  have h₂ := (elementSolve_spec hμ r b₂ c₂).1
  refine ((elementSolve_spec hμ r _ _).2 _ ?_).symm
  simp only [ElementStep, map_add, map_smul] at h₁ h₂ ⊢
  linear_combination (norm := module) c • h₁ + h₂

omit [Fintype ρ] in
/-- [proved-derived; formal-checked] **The contact's solve is linear** in its displacement, slip
rate and the two channel waves: `M_a ω = 2C w + h(α_g − α_h) − h K u` is linear and its solution
unique. -/
theorem transitSolve_comb {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (a : Contact) (c : ℝ)
    (u₁ u₂ w₁ w₂ g₁ g₂ k₁ k₂ : Ch a) :
    transitSolve μ a (c • u₁ + u₂) (c • w₁ + w₂) (c • g₁ + g₂) (c • k₁ + k₂) =
      c • transitSolve μ a u₁ w₁ g₁ k₁ + transitSolve μ a u₂ w₂ g₂ k₂ := by
  have h₁ := (transitSolve_spec hμ a u₁ w₁ g₁ k₁).1
  have h₂ := (transitSolve_spec hμ a u₂ w₂ g₂ k₂).1
  refine ((transitSolve_spec hμ a _ _ _ _).2 _ ?_).symm
  simp only [TransitSolves, map_add, map_smul] at h₁ h₂ ⊢
  linear_combination (norm := module) c • h₁ + h₂

end Solve

section Tick

variable {Ring Contact ρ : Type u} [DecidableEq Ring] [Fintype Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}

omit [Fintype ρ] in
theorem tickSlip_comb {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (c : ℝ)
    (X₁ X₂ : Change endRing V Ch) (a : Contact) :
    tickSlip μ (Change.comb c X₁ X₂) a = c • tickSlip μ X₁ a + tickSlip μ X₂ a := by
  rw [tickSlip, endOut_comb, endOut_comb, map_add, map_smul, map_add, map_smul]
  exact transitSolve_comb hμ a c _ _ _ _ _ _ _ _

omit [DecidableEq Ring] [Fintype Contact] [Fintype ρ] [∀ r, FiniteDimensional ℝ (V r)]
  [∀ a, FiniteDimensional ℝ (Ch a)] in
theorem endArrive_comb (channel : (e : Contact × Bool) → Ch e.1 →L[ℝ] V (endRing e))
    (G : Contact → ℝ) (c : ℝ) (o₁ o₂ : (e : Contact × Bool) → V (endRing e))
    (ω₁ ω₂ : (a : Contact) → Ch a) (e : Contact × Bool) :
    endArrive channel G (fun e => c • o₁ e + o₂ e) (fun a => c • ω₁ a + ω₂ a) e =
      c • endArrive channel G o₁ ω₁ e + endArrive channel G o₂ ω₂ e := by
  obtain ⟨a, _ | _⟩ := e
  · simp only [endArrive, arriveH, map_add, map_smul]
    module
  · simp only [endArrive, arriveG, map_add, map_smul]
    module

/-- [proved-derived; formal-checked] **The tick is linear in the change** at the cut's fixed
operands: junction anchors, storage and port waves, element solves, contact solves and arrivals are
all linear, so `fieldTick μ (c X₁ + X₂) = c fieldTick μ X₁ + fieldTick μ X₂`. -/
theorem fieldTick_comb {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (c : ℝ)
    (X₁ X₂ : Change endRing V Ch) :
    fieldTick μ (Change.comb c X₁ X₂) = Change.comb c (fieldTick μ X₁) (fieldTick μ X₂) := by
  have hslip : tickSlip μ (Change.comb c X₁ X₂) = fun a => c • tickSlip μ X₁ a + tickSlip μ X₂ a :=
    funext (tickSlip_comb hμ c X₁ X₂)
  refine Change.ext' (funext fun r => ?_) (funext fun e => ?_) (funext fun a => ?_)
    (funext fun a => ?_)
  · change elementSolve μ r _ _ = c • elementSolve μ r _ _ + elementSolve μ r _ _
    rw [storageWave_comb, contrast_comb, elementSolve_comb hμ]
  · change endArrive μ.channel μ.G _ _ e = c • endArrive μ.channel μ.G _ _ e +
      endArrive μ.channel μ.G _ _ e
    rw [show endOut μ.Y μ.G (Change.comb c X₁ X₂).s (Change.comb c X₁ X₂).arr =
      fun e => c • endOut μ.Y μ.G X₁.s X₁.arr e + endOut μ.Y μ.G X₂.s X₂.arr e from
        funext (endOut_comb μ.Y μ.G c X₁ X₂), hslip, endArrive_comb]
  · change (c • X₁.u a + X₂.u a) + μ.h • tickSlip μ (Change.comb c X₁ X₂) a =
      c • (X₁.u a + μ.h • tickSlip μ X₁ a) + (X₂.u a + μ.h • tickSlip μ X₂ a)
    rw [hslip]
    module
  · change (2 : ℝ) • tickSlip μ (Change.comb c X₁ X₂) a - (c • X₁.w a + X₂.w a) =
      c • ((2 : ℝ) • tickSlip μ X₁ a - X₁.w a) + ((2 : ℝ) • tickSlip μ X₂ a - X₂.w a)
    rw [hslip]
    module

end Tick

section Blocks

variable {Ring Contact : Type u}
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)]

/-- [definition] **The word's blocks**: a ring block carries the ring's storage wave and the waves
arriving at its contact ports, `V_r × (Port_r → V_r)`; a contact block carries the contact's
displacement and slip rate, `Ch_a × Ch_a`. -/
def BlockM (endRing : Contact × Bool → Ring) (V : Ring → Type u) (Ch : Contact → Type u) :
    Ring ⊕ Contact → Type u
  | .inl r => V r × (Port endRing r → V r)
  | .inr a => Ch a × Ch a

variable {endRing : Contact × Bool → Ring}

instance instAddCommGroupBlockM (b : Ring ⊕ Contact) : AddCommGroup (BlockM endRing V Ch b) :=
  match b with
  | .inl r => inferInstanceAs (AddCommGroup (V r × (Port endRing r → V r)))
  | .inr a => inferInstanceAs (AddCommGroup (Ch a × Ch a))

instance instModuleBlockM (b : Ring ⊕ Contact) : Module ℝ (BlockM endRing V Ch b) :=
  match b with
  | .inl r => inferInstanceAs (Module ℝ (V r × (Port endRing r → V r)))
  | .inr a => inferInstanceAs (Module ℝ (Ch a × Ch a))

/-- [definition] A change read on its blocks. -/
def toBlocks (X : Change endRing V Ch) : (b : Ring ⊕ Contact) → BlockM endRing V Ch b
  | .inl r => ((X.s r, portWave endRing X.arr r) : V r × (Port endRing r → V r))
  | .inr a => ((X.u a, X.w a) : Ch a × Ch a)

/-- [definition] The change carried by a block state. -/
def ofBlocks (x : (b : Ring ⊕ Contact) → BlockM endRing V Ch b) : Change endRing V Ch where
  s r := Prod.fst (x (.inl r) : V r × (Port endRing r → V r))
  arr e := Prod.snd (x (.inl (endRing e)) :
    V (endRing e) × (Port endRing (endRing e) → V (endRing e))) ⟨e, rfl⟩
  u a := Prod.fst (x (.inr a) : Ch a × Ch a)
  w a := Prod.snd (x (.inr a) : Ch a × Ch a)

omit [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ a, NormedAddCommGroup (Ch a)] [∀ a, InnerProductSpace ℝ (Ch a)] in
theorem ofBlocks_toBlocks (X : Change endRing V Ch) : ofBlocks (toBlocks X) = X :=
  Change.ext' rfl rfl rfl rfl

omit [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ a, NormedAddCommGroup (Ch a)] [∀ a, InnerProductSpace ℝ (Ch a)] in
theorem toBlocks_ofBlocks (x : (b : Ring ⊕ Contact) → BlockM endRing V Ch b) :
    toBlocks (ofBlocks x) = x := by
  funext b
  cases b with
  | inl r =>
    refine Prod.ext rfl (funext fun p => ?_)
    obtain ⟨e, he⟩ := p
    subst he
    rfl
  | inr a => rfl

theorem ofBlocks_comb (c : ℝ) (x y : (b : Ring ⊕ Contact) → BlockM endRing V Ch b) :
    ofBlocks (c • x + y) = Change.comb c (ofBlocks x) (ofBlocks y) := rfl

theorem toBlocks_comb (c : ℝ) (X Y : Change endRing V Ch) :
    toBlocks (Change.comb c X Y) = c • toBlocks X + toBlocks Y := by
  funext b
  cases b with
  | inl r => exact Prod.ext rfl (funext fun p => portWave_comb c X.arr Y.arr r p)
  | inr a => rfl

omit [∀ r, InnerProductSpace ℝ (V r)] [∀ a, InnerProductSpace ℝ (Ch a)] in
/-- [proved-derived; formal-checked] A change vanishes on a block (`Word.BlockZero`) exactly when
its block is zero. -/
theorem blockZero_iff (X : Change endRing V Ch) (b : Ring ⊕ Contact) :
    BlockZero X b ↔ toBlocks X b = 0 := by
  cases b with
  | inl r =>
    constructor
    · rintro ⟨hs, harr⟩
      refine Prod.ext hs (funext fun p => ?_)
      obtain ⟨e, he⟩ := p
      subst he
      exact harr e rfl
    · intro h
      refine ⟨congrArg (Prod.fst : V r × (Port endRing r → V r) → V r) h, fun e he => ?_⟩
      subst he
      exact congrFun (congrArg (Prod.snd : V (endRing e) × (Port endRing (endRing e) →
        V (endRing e)) → (Port endRing (endRing e) → V (endRing e))) h) ⟨e, rfl⟩
  | inr a =>
    constructor
    · rintro ⟨hu, hw⟩
      exact Prod.ext hu hw
    · intro h
      exact ⟨congrArg (Prod.fst : Ch a × Ch a → Ch a) h, congrArg (Prod.snd : Ch a × Ch a → Ch a) h⟩

end Blocks

section Operator

variable {Ring Contact ρ : Type u} [Fintype Ring] [DecidableEq Ring] [Fintype Contact]
  [DecidableEq Contact] [Fintype ρ]
variable {V : Ring → Type u} [∀ r, NormedAddCommGroup (V r)] [∀ r, InnerProductSpace ℝ (V r)]
  [∀ r, FiniteDimensional ℝ (V r)]
variable {Ch : Contact → Type u} [∀ a, NormedAddCommGroup (Ch a)]
  [∀ a, InnerProductSpace ℝ (Ch a)] [∀ a, FiniteDimensional ℝ (Ch a)]
variable {endRing : Contact × Bool → Ring}

/-- [definition] The tick read on the blocks. -/
noncomputable def tickMap (μ : Medium endRing V Ch ρ) (x : (b : Ring ⊕ Contact) → BlockM endRing V Ch b) :
    (b : Ring ⊕ Contact) → BlockM endRing V Ch b :=
  toBlocks (fieldTick μ (ofBlocks x))

omit [Fintype Ring] [DecidableEq Contact] in
theorem tickMap_comb {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) (c : ℝ)
    (x y : (b : Ring ⊕ Contact) → BlockM endRing V Ch b) :
    tickMap μ (c • x + y) = c • tickMap μ x + tickMap μ y := by
  rw [tickMap, ofBlocks_comb, fieldTick_comb hμ, toBlocks_comb]
  rfl

/-- [definition] **The tick as a linear map** on the block states of an admissible medium. -/
noncomputable def tickLinear {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) :
    ((b : Ring ⊕ Contact) → BlockM endRing V Ch b) →ₗ[ℝ]
      ((b : Ring ⊕ Contact) → BlockM endRing V Ch b) where
  toFun := tickMap μ
  map_add' x y := by
    have h := tickMap_comb hμ 1 x y
    rwa [one_smul, one_smul] at h
  map_smul' c x := by
    have h0 : tickMap μ 0 = 0 := by
      have h := tickMap_comb hμ 1 0 0
      rw [one_smul, one_smul, add_zero] at h
      exact (add_eq_left.mp h.symm)
    have h := tickMap_comb hμ c x 0
    rw [add_zero, h0, add_zero] at h
    exact h

/-- [definition] **The tick's block operator**: block `y` of the tick of the change carried on
block `z` alone. -/
noncomputable def blockOp {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) :
    BlockOp ℝ (BlockM endRing V Ch) := fun y z =>
  (LinearMap.proj y).comp ((tickLinear hμ).comp (LinearMap.single ℝ (BlockM endRing V Ch) z))

/-- [proved-derived; formal-checked] **The concrete tick is the block operator's tick**:
`(T x)_y = Σ_z T y z x_z` with `T = blockOp`. -/
theorem tick_blockOp {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    (x : (b : Ring ⊕ Contact) → BlockM endRing V Ch b) :
    tick (blockOp hμ) x = tickMap μ x := by
  funext y
  simp only [tick, blockOp, LinearMap.comp_apply, LinearMap.coe_proj, Function.eval,
    LinearMap.coe_single]
  rw [← Finset.sum_apply, ← map_sum, Finset.univ_sum_single]
  rfl

omit [Fintype Ring] [DecidableEq Ring] [Fintype Contact] [DecidableEq Contact] in
theorem blockAdj_refl (b : Ring ⊕ Contact) : blockAdj endRing b b := by
  cases b with
  | inl r => exact Or.inl rfl
  | inr a => rfl

omit [Fintype Ring] in
/-- [proved-derived; formal-checked] **The block operator is sparse on the word's block graph**:
`blockOp y z = 0` off the edges of `Word.blockAdj` (`Word.fieldTick_local`: a change carried on
block `z` alone leaves every block that `z` does not reach in one tick at zero). -/
theorem blockOp_sparse {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible) :
    Sparse (blockAdj endRing) (blockOp hμ) := by
  intro y z hzy
  refine LinearMap.ext fun v => ?_
  have hyz : y ≠ z := fun h => hzy (h ▸ blockAdj_refl y)
  set x : (b : Ring ⊕ Contact) → BlockM endRing V Ch b := Pi.single z v with hx
  have hzero : ∀ b, b ≠ z → BlockZero (ofBlocks x) b := fun b hb => by
    rw [blockZero_iff, toBlocks_ofBlocks, hx, Pi.single_eq_of_ne hb]
  have hloc := fieldTick_local hμ (ofBlocks x) y (hzero y hyz)
    (fun z' hz' => hzero z' fun h => hzy (h ▸ hz'))
  rw [blockZero_iff] at hloc
  rw [LinearMap.zero_apply]
  exact hloc

/-- [proved-derived; formal-checked] **The word's iterates are the block operator's trajectory**:
`toBlocks (fieldTick^[t] X) = trajectory (blockOp hμ) (toBlocks X) t`. -/
theorem fieldTick_iterate_blocks {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    (X : Change endRing V Ch) (t : ℕ) :
    toBlocks ((fieldTick μ)^[t] X) = trajectory (blockOp hμ) (toBlocks X) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply']
    change _ = tick (blockOp hμ) (trajectory (blockOp hμ) (toBlocks X) t)
    rw [tick_blockOp, ← ih, tickMap, ofBlocks_toBlocks]

/-! ### The block laws on the concrete tick -/

/-- [proved-derived; formal-checked] **The causal cone on the concrete tick**: a change supported on
the blocks `S` is supported, after `t` ticks, within `t` hops of `S` (`Propagation.tick_causal_cone`
read through `fieldTick_iterate_blocks`; it agrees with `Word.word_tick_cone`). -/
theorem fieldTick_causal_cone {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    {X : Change endRing V Ch} {S : Set (Ring ⊕ Contact)} (hX : SupportedIn (toBlocks X) S)
    (t : ℕ) : SupportedIn (toBlocks ((fieldTick μ)^[t] X)) (reachWithin (blockAdj endRing) S t) := by
  rw [fieldTick_iterate_blocks hμ]
  exact tick_causal_cone (blockOp_sparse hμ) hX t

/-- [proved-derived; formal-checked] **The reading pairs exactly with the swept covector** on the
concrete tick: `⟨λ_(n), x_k⟩ = ⟨g, x_(k+n)⟩`, `λ` the reading covector swept back `n` ticks under
the tick's dual (`Propagation.trajectory_pairing`). -/
theorem fieldTick_pairing {μ : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    (X : Change endRing V Ch) (g : (b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b))
    (k n : ℕ) :
    pair (sweep (blockOp hμ) g n) (toBlocks ((fieldTick μ)^[k] X)) =
      pair g (toBlocks ((fieldTick μ)^[k + n] X)) := by
  rw [fieldTick_iterate_blocks hμ, fieldTick_iterate_blocks hμ]
  exact trajectory_pairing _ _ g k n

/-- [proved-derived; formal-checked] **The exact variation between two media** on one open change:
`⟨g, x′_t⟩ − ⟨g, x_t⟩ = Σ_(k<t) ⟨λ′_(t−1−k), (T′ − T) x_k⟩`, with `x` the word under `μ` and `λ′`
the reading covector swept back under `μ′` (`Propagation.word_variation_exact`). -/
theorem fieldTick_variation_exact {μ μ' : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    (hμ' : μ'.Admissible) (X : Change endRing V Ch)
    (g : (b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b)) (t : ℕ) :
    pair g (toBlocks ((fieldTick μ')^[t] X)) - pair g (toBlocks ((fieldTick μ)^[t] X)) =
      ∑ k ∈ Finset.range t, pair (sweep (blockOp hμ') g (t - 1 - k))
        (tick (opSub (blockOp hμ') (blockOp hμ)) (toBlocks ((fieldTick μ)^[k] X))) := by
  simp only [fieldTick_iterate_blocks hμ, fieldTick_iterate_blocks hμ']
  exact word_variation_exact _ _ _ g t

/-- [proved-derived; formal-checked] **A medium outside the diamond changes no admitted reading**
on the concrete tick (R3 R1). If two admissible media's block operators agree on every edge
`z → y` of the causal diamond `r_z + 1 + o_y ≤ e_last` of the open change's blocks `S` and the
receiving blocks `R`, every reading supported on `R` at any epoch `t ≤ e_last` agrees
(`Propagation.release_past_diamond`). -/
theorem fieldTick_release_past_diamond {μ μ' : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    (hμ' : μ'.Admissible) {X : Change endRing V Ch}
    {g : (b : Ring ⊕ Contact) → Module.Dual ℝ (BlockM endRing V Ch b)}
    {S R : Set (Ring ⊕ Contact)} (hX : SupportedIn (toBlocks X) S) (hg : SupportedIn g R)
    {eLast t : ℕ} (ht : t ≤ eLast)
    (hagree : ∀ y z, InDiamond (blockAdj endRing) S R eLast z y → blockOp hμ' y z = blockOp hμ y z) :
    pair g (toBlocks ((fieldTick μ')^[t] X)) = pair g (toBlocks ((fieldTick μ)^[t] X)) := by
  rw [fieldTick_iterate_blocks hμ, fieldTick_iterate_blocks hμ']
  exact release_past_diamond (blockOp_sparse hμ) (blockOp_sparse hμ') hX hg ht hagree

/-- [proved-derived; formal-checked] **The concrete word agrees wherever it is still observed**: if
two admissible media's block operators agree on the diamond's edges, block `z` of the change after
`k ≤ e_last` ticks agrees whenever `z` observes a receiving block within `e_last − k` hops
(`Propagation.trajectory_agrees_where_observed`). -/
theorem fieldTick_agrees_where_observed {μ μ' : Medium endRing V Ch ρ} (hμ : μ.Admissible)
    (hμ' : μ'.Admissible) {X : Change endRing V Ch} {S R : Set (Ring ⊕ Contact)}
    (hX : SupportedIn (toBlocks X) S) {eLast : ℕ}
    (hagree : ∀ y z, InDiamond (blockAdj endRing) S R eLast z y → blockOp hμ' y z = blockOp hμ y z)
    {k : ℕ} (hk : k ≤ eLast) {z : Ring ⊕ Contact} (hobs : Observes (blockAdj endRing) R z (eLast - k)) :
    toBlocks ((fieldTick μ')^[k] X) z = toBlocks ((fieldTick μ)^[k] X) z := by
  rw [fieldTick_iterate_blocks hμ, fieldTick_iterate_blocks hμ']
  exact trajectory_agrees_where_observed (blockOp_sparse hμ) (blockOp_sparse hμ') hX hagree hk hobs

end Operator

#print axioms elementSolve_comb
#print axioms transitSolve_comb
#print axioms fieldTick_comb
#print axioms blockZero_iff
#print axioms tick_blockOp
#print axioms blockOp_sparse
#print axioms fieldTick_iterate_blocks
#print axioms fieldTick_causal_cone
#print axioms fieldTick_pairing
#print axioms fieldTick_variation_exact
#print axioms fieldTick_release_past_diamond
#print axioms fieldTick_agrees_where_observed

end Holonics.HNN.TickBlocks
