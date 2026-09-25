import Holonics.Holarchy.View
import Holonics.Objects.RelativeCompleteness

/-!
# Holarchy.Globe: the relative completeness of a Holarchy constituent

[definition] Object 7 of `docs/ELEMENTARY_OBJECTS.md` read inside object 11. A block `b` of a grain
of a Holarchy's glued complex is a **constituent region** (`constituentRegion`):

* its **interior** is the constituent's own state, a value on each region of the block
  (`BlockInterior`);
* its **boundary datum** is the face current of the glued complex, and the exterior receivers read
  it only through the block's interface flux `⟨j, ∂(block)⟩`, which is the view's `interfaceFlux`
  (`constituentRegion_observe`): the boundary map of the constituent is the Holarchy's view
  interface at that grain;
* its **step** is the whole's field law on the glued complex (`FieldLaw`) restricted to the block,
  the rest of the whole held at zero (`blockStep`);
* its **membrane** is the block's actual boundary chain in the glued complex (`blockMembrane`),
  oriented by the whole's interior.

A block is a **globe** for its receivers (`HolarchyGlobe`) when that region is relatively complete
over that membrane (`Objects/RelativeCompleteness.RelativelyComplete`).

[proved-derived; formal-checked]

* **Clause (3) is supplied by the gluing.** The block's membrane bounds its interior by construction
  (`constituentMembrane_boundsInterior`), so no exact flux escapes it (`constituent_no_exact_flux`),
  and its interface flux is the enclosed divergence (`blockMembrane_gauss`, Gauss and Stokes). A
  block is therefore a globe exactly when its region is coupled and not determined
  (`holarchyGlobe_iff_coupled_notDetermined`).
* **The criterion in the linear chart.** For an additive field law the region is additive: its
  boundary-history fibres are cosets of the future-blind population `F` of the interface-flux
  receivers (`constituent_agree_iff`). The block is coupled exactly when some interior difference
  over one boundary current is eventually read at the interface, `∃ x, (x, 0) ∉ F`
  (`constituent_coupled_iff`), and not determined exactly when some future-blind difference moves
  and recurs, `∃ d ∈ F, ∃ n > 0, Eⁿ d = d ∧ E d ≠ d` (`constituent_notDetermined_iff`); together,
  `holarchyGlobe_iff_linear`.
* **Instances on an actual Holarchy.** `globeHolarchy` joins a two-region constituent to a
  one-region one across a shared face. Under the field law in which one inner region flips sign,
  the other is conserved and the face current reads it (a charge read at the boundary, Gauss and
  Birkhoff type), the two-region block is a globe for the interface-flux receiver
  (`globeHolarchy_left_block_is_globe`), while the one-region block, whose conserved interior never
  moves, is not (`globeHolarchy_right_block_is_not_globe`).

[counterexample; formal-checked] At the membrane level, the open tube's lateral membrane is the
membrane of no region of the square (`tube_is_not_a_constituent`), and the hollow loop bounds no
region of its faceless complex (`hollow_is_not_a_constituent`); both hold because a constituent's
membrane bounds its interior by construction.

[open] **The relative completeness theorem is owed in #62 and is not asserted here**: a criterion
for when a globe exists as a potential, stated as interior↔exterior entrance and escape currents
through the constituent's interface, from the Einstein lifts paired with the complex
Euler/Navier–Stokes current laws, with the bounding radius against dimension. The field law is
declared on the glued complex; deriving it from the whole's port Holon (whose storage coordinates
are not yet joined to the glued complex's regions) is also owed.
-/

noncomputable section

namespace Holonics.HolarchyCore

open Matrix
open Holonics.Objects.RelativeCompleteness
open Holonics.Foundation.CausalRelevance
open Holonics.Foundation.Chronology (transportWord transportWord_nil transportWord_cons)

universe u

/-! ## 1. The constituent membrane -/

section Membrane

variable {K C₀ C₁ C₂ : Type*} [Field K] [AddCommGroup C₀] [Module K C₀]
  [AddCommGroup C₁] [Module K C₁] [AddCommGroup C₂] [Module K C₂]

/-- [definition] **The membrane of a region**: its chain as the interior, its boundary as the
surface. -/
def constituentMembrane (bd₁ : C₁ →ₗ[K] C₀) (bd₂ : C₂ →ₗ[K] C₁) (hbb : bd₁.comp bd₂ = 0)
    (region : C₂) : Membrane K C₀ C₁ C₂ where
  boundary₁ := bd₁
  boundary₂ := bd₂
  boundary_squared := hbb
  interiorChain := region
  surface := bd₂ region

/-- [proved-derived; formal-checked] **A region's membrane bounds its interior**, by construction. -/
theorem constituentMembrane_boundsInterior (bd₁ : C₁ →ₗ[K] C₀) (bd₂ : C₂ →ₗ[K] C₁)
    (hbb : bd₁.comp bd₂ = 0) (region : C₂) :
    (constituentMembrane bd₁ bd₂ hbb region).BoundsInterior := rfl

/-- [proved-derived; formal-checked] **No exact flux escapes a constituent**
(`Membrane.Bounds.closed`, `closed_iff_no_exact_flux`). -/
theorem constituent_no_exact_flux (bd₁ : C₁ →ₗ[K] C₀) (bd₂ : C₂ →ₗ[K] C₁)
    (hbb : bd₁.comp bd₂ = 0) (region : C₂) (potential : Module.Dual K C₀) :
    bd₁.dualMap potential (bd₂ region) = 0 :=
  (Membrane.closed_iff_no_exact_flux _).mp
    (constituentMembrane_boundsInterior bd₁ bd₂ hbb region).bounds.closed potential

end Membrane

/-! ## 2. The constituent region of a block -/

section Region

variable {𝕜 : Type u} [Field 𝕜] {Block : Type*}

theorem CellComplex.dd_linear (K : CellComplex 𝕜) :
    (Matrix.mulVecLin K.d₁).comp (Matrix.mulVecLin K.d₂) = 0 := by
  apply LinearMap.ext
  intro c
  simp [Matrix.mulVec_mulVec, K.dd]

/-- [definition] **The membrane of a block**: the block's oriented chain and its boundary in the
glued complex. -/
def blockMembrane (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block) (b : Block) :
    Membrane 𝕜 (K.C₀ → 𝕜) (K.C₁ → 𝕜) (K.C₂ → 𝕜) :=
  constituentMembrane (Matrix.mulVecLin K.d₁) (Matrix.mulVecLin K.d₂) K.dd_linear
    (blockChain K orient g b)

/-- [proved-derived; formal-checked] **Gauss on a constituent**: its interface flux is the enclosed
divergence, and an exact current has none. -/
theorem blockMembrane_gauss (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block)
    (b : Block) (j : K.C₁ → 𝕜) (φ : K.C₀ → 𝕜) :
    j ⬝ᵥ (blockMembrane K orient g b).surface =
        (K.d₂ᵀ *ᵥ j) ⬝ᵥ (blockMembrane K orient g b).interiorChain ∧
      (K.d₁ᵀ *ᵥ φ) ⬝ᵥ (blockMembrane K orient g b).surface = 0 :=
  ⟨blockFlux_stokes orient g j b, blockFlux_exact orient g φ b⟩

/-- [definition] **The interior of a block**: a value on each of its regions. -/
abbrev BlockInterior (K : CellComplex 𝕜) (g : Grain K.C₂ Block) (b : Block) : Type u :=
  {c // c ∈ g.blocks b} → 𝕜

/-- [definition] A block's interior extended by zero to the whole glued complex. -/
def extendBlock (K : CellComplex 𝕜) (g : Grain K.C₂ Block) (b : Block) :
    BlockInterior K g b →+ (K.C₂ → 𝕜) where
  toFun x c := if hc : c ∈ g.blocks b then x ⟨c, hc⟩ else 0
  map_zero' := by funext c; simp
  map_add' x y := by funext c; by_cases hc : c ∈ g.blocks b <;> simp [hc]

/-- [definition] The whole's regions read on a block. -/
def restrictBlock (K : CellComplex 𝕜) (g : Grain K.C₂ Block) (b : Block) :
    (K.C₂ → 𝕜) →+ BlockInterior K g b where
  toFun x c := x c.1
  map_zero' := rfl
  map_add' _ _ := rfl

/-- [definition] **A field law of the glued complex**: one additive step of the region storage and
the face current of the whole. -/
abbrev FieldLaw (K : CellComplex 𝕜) : Type u :=
  (K.C₂ → 𝕜) × (K.C₁ → 𝕜) →+ (K.C₂ → 𝕜) × (K.C₁ → 𝕜)

/-- [definition] **The whole's field law restricted to a block**: extend the block's interior by
zero, take one step of the whole, read the block's regions and the face current. -/
def blockStep (K : CellComplex 𝕜) (g : Grain K.C₂ Block) (b : Block) (law : FieldLaw K) :
    BlockInterior K g b × (K.C₁ → 𝕜) →+ BlockInterior K g b × (K.C₁ → 𝕜) :=
  ((restrictBlock K g b).prodMap (AddMonoidHom.id _)).comp
    (law.comp ((extendBlock K g b).prodMap (AddMonoidHom.id _)))

/-- [definition] The block's interface flux of a face current, as an additive reading. -/
def interfaceReading (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block)
    (b : Block) : (K.C₁ → 𝕜) →+ 𝕜 where
  toFun j := j ⬝ᵥ (blockMembrane K orient g b).surface
  map_zero' := zero_dotProduct _
  map_add' _ _ := add_dotProduct _ _ _

/-- [definition] **The constituent region of block `b`**: the block's interior, the glued face
current as boundary datum, the whole's field law restricted to the block, and exterior receivers
that read the boundary datum only through the block's interface flux. -/
def constituentRegion {Receiver Face : Type u} [AddCommGroup Face] (K : CellComplex 𝕜)
    (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block) (b : Block) (law : FieldLaw K)
    (R : Receiver → (𝕜 →+ Face)) :
    Region PUnit.{u + 1} Receiver (BlockInterior K g b) (K.C₁ → 𝕜) Face :=
  Region.ofAdditive (fun _ => blockStep K g b law)
    (fun r => (R r).comp (interfaceReading K orient g b)) Set.univ

variable {Receiver Face : Type u} [AddCommGroup Face]

/-- [proved-derived; formal-checked] **The boundary map of a constituent is the Holarchy's view
interface at that grain**: an exterior receiver reads a state of the region as its reading of the
block's `interfaceFlux` in the view, at any tick whose occurrence carries that face current. -/
theorem constituentRegion_observe {V E F : Type*}
    {P : Holonics.Aeon.Clock.Groupoid.ParametricComplex V E F} {ViewFace : Type*}
    (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block) (b : Block) (law : FieldLaw K)
    (R : Receiver → (𝕜 →+ Face)) (current : V → K.C₁ → 𝕜) (Rv : RegionReceiver V K.C₂ ViewFace)
    {x y : V} (γ : Holonics.Aeon.Clock.Groupoid.Aeon P x y)
    (c : Holonics.Aeon.Clock.Epoch.CutClock P) (k : Tick γ c) (r : Receiver)
    (s : BlockInterior K g b) :
    (constituentRegion K orient g b law R).observe r (s, current ((view K orient current Rv g γ c).occurrence k)) =
      R r ((view K orient current Rv g γ c).interfaceFlux k b) := rfl

variable {U σA ρA πA αA σB ρB πB αB τ : Type*}
  [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA]
  [Fintype σB] [Fintype ρB] [Fintype πB] [Fintype αB] [Fintype τ] [DecidableEq τ]

/-- [definition] **A Holarchy globe**: block `b` of a grain of the Holarchy's glued complex, with
its interior, the whole's field law restricted to it and receivers reading its interface flux, is
relatively complete over its actual membrane, oriented by the whole's interior. -/
def HolarchyGlobe {A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA} {B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB}
    (h : Holarchy A B) (g : Grain h.decl.glued.C₂ Block) (b : Block) (law : FieldLaw h.decl.glued)
    (R : Receiver → (𝕜 →+ Face)) : Prop :=
  RelativelyComplete (constituentRegion h.decl.glued h.wholeInterior g b law R)
    (blockMembrane h.decl.glued h.wholeInterior g b)

/-- [proved-derived; formal-checked] **Clause (3) is supplied by the gluing**: a block of a
Holarchy is a globe exactly when its constituent region is coupled and not determined. -/
theorem holarchyGlobe_iff_coupled_notDetermined {A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA}
    {B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB} (h : Holarchy A B) (g : Grain h.decl.glued.C₂ Block)
    (b : Block) (law : FieldLaw h.decl.glued) (R : Receiver → (𝕜 →+ Face)) :
    HolarchyGlobe h g b law R ↔
      (constituentRegion h.decl.glued h.wholeInterior g b law R).Coupled ∧
        (constituentRegion h.decl.glued h.wholeInterior g b law R).NotDetermined :=
  ⟨fun hg => ⟨hg.coupled, hg.notDetermined⟩,
    fun hc => ⟨hc.1, hc.2, constituentMembrane_boundsInterior _ _ _ _⟩⟩

end Region

/-! ## 3. The criterion in the linear chart -/

section Linear

variable {R I Bd V : Type u} [AddCommGroup I] [AddCommGroup Bd] [AddCommGroup V]

/-- [proved-derived; formal-checked] An additive region over all states is coupled exactly when
some interior difference over one boundary datum is not future-blind. -/
theorem ofAdditive_coupled_iff (E : I × Bd →+ I × Bd) (read : R → (Bd →+ V)) :
    (Region.ofAdditive (fun _ : PUnit.{u + 1} => E) read Set.univ).Coupled ↔
      ∃ x : I, ((x, 0) : I × Bd) ∉
        futureCollapsed (outwardRead read) (fun _ : PUnit.{u + 1} => E) := by
  unfold Region.Coupled
  constructor
  · rintro ⟨i, i', bd, -, -, h⟩
    rw [ofAdditive_agree_iff] at h
    refine ⟨i' - i, ?_⟩
    have : ((i', bd) : I × Bd) - (i, bd) = (i' - i, 0) := by ext <;> simp
    rwa [this] at h
  · rintro ⟨x, hx⟩
    refine ⟨0, x, 0, Set.mem_univ _, Set.mem_univ _, ?_⟩
    rw [ofAdditive_agree_iff]
    simpa using hx

/-- [proved-derived; formal-checked] An additive region over all states is not determined exactly
when some future-blind difference moves and recurs (`ofAdditive_persistent_iff`). -/
theorem ofAdditive_notDetermined_iff (E : I × Bd →+ I × Bd) (read : R → (Bd →+ V)) :
    (Region.ofAdditive (fun _ : PUnit.{u + 1} => E) read Set.univ).NotDetermined ↔
      ∃ d ∈ futureCollapsed (outwardRead read) (fun _ : PUnit.{u + 1} => E),
        ∃ n, 0 < n ∧ (⇑E)^[n] d = d ∧ E d ≠ d := by
  unfold Region.NotDetermined
  constructor
  · intro h
    obtain ⟨other, hagree, hpersist⟩ := h 0 (Set.mem_univ _)
    rw [ofAdditive_agree_iff] at hagree
    rw [ofAdditive_persistent_iff] at hpersist
    simp only [sub_zero] at hagree hpersist
    exact ⟨other, hagree, hpersist⟩
  · rintro ⟨d, hd, hper⟩ state _
    refine ⟨state + d, ?_, ?_⟩
    · rw [ofAdditive_agree_iff]; simpa using hd
    · rw [ofAdditive_persistent_iff]; simpa using hper

end Linear

section LinearHolarchy

variable {𝕜 : Type u} [Field 𝕜] {Block : Type*} {Receiver Face : Type u} [AddCommGroup Face]

/-- [proved-derived; formal-checked] **The fibres of a constituent region** are the cosets of the
future-blind population of its interface-flux receivers. -/
theorem constituent_agree_iff (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block)
    (b : Block) (law : FieldLaw K) (R : Receiver → (𝕜 →+ Face))
    (s s' : BlockInterior K g b × (K.C₁ → 𝕜)) :
    (constituentRegion K orient g b law R).Agree s s' ↔
      s' - s ∈ futureCollapsed (outwardRead fun r => (R r).comp (interfaceReading K orient g b))
        (fun _ : PUnit.{u + 1} => blockStep K g b law) :=
  ofAdditive_agree_iff _ _ _ _ _

/-- [proved-derived; formal-checked] **A constituent is coupled** exactly when some interior
difference over one face current is eventually read at its interface. -/
theorem constituent_coupled_iff (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜) (g : Grain K.C₂ Block)
    (b : Block) (law : FieldLaw K) (R : Receiver → (𝕜 →+ Face)) :
    (constituentRegion K orient g b law R).Coupled ↔
      ∃ x : BlockInterior K g b, ((x, 0) : BlockInterior K g b × (K.C₁ → 𝕜)) ∉
        futureCollapsed (outwardRead fun r => (R r).comp (interfaceReading K orient g b))
          (fun _ : PUnit.{u + 1} => blockStep K g b law) :=
  ofAdditive_coupled_iff (blockStep K g b law)
    (fun r => (R r).comp (interfaceReading K orient g b))

/-- [proved-derived; formal-checked] **A constituent is not determined** exactly when some
difference invisible to its interface at every future moves and recurs under the restricted
field law. -/
theorem constituent_notDetermined_iff (K : CellComplex 𝕜) (orient : K.C₂ → 𝕜)
    (g : Grain K.C₂ Block) (b : Block) (law : FieldLaw K) (R : Receiver → (𝕜 →+ Face)) :
    (constituentRegion K orient g b law R).NotDetermined ↔
      ∃ d ∈ futureCollapsed (outwardRead fun r => (R r).comp (interfaceReading K orient g b))
          (fun _ : PUnit.{u + 1} => blockStep K g b law),
        ∃ n, 0 < n ∧ (⇑(blockStep K g b law))^[n] d = d ∧ blockStep K g b law d ≠ d :=
  ofAdditive_notDetermined_iff (blockStep K g b law)
    (fun r => (R r).comp (interfaceReading K orient g b))

variable {U σA ρA πA αA σB ρB πB αB τ : Type*}
  [Fintype σA] [Fintype ρA] [Fintype πA] [Fintype αA]
  [Fintype σB] [Fintype ρB] [Fintype πB] [Fintype αB] [Fintype τ] [DecidableEq τ]

/-- [proved-derived; formal-checked] **The Holarchy globe criterion in the linear chart.** Block
`b` of a Holarchy is a globe exactly when some interior difference over one face current is
eventually read at its interface, and some difference invisible to its interface at every future
moves and recurs under the whole's field law restricted to it. -/
theorem holarchyGlobe_iff_linear {A : Constituent 𝕜 U σA ρA (πA ⊕ τ) αA}
    {B : Constituent 𝕜 U σB ρB (τ ⊕ πB) αB} (h : Holarchy A B) (g : Grain h.decl.glued.C₂ Block)
    (b : Block) (law : FieldLaw h.decl.glued) (R : Receiver → (𝕜 →+ Face)) :
    HolarchyGlobe h g b law R ↔
      (∃ x : BlockInterior h.decl.glued g b,
          ((x, 0) : BlockInterior h.decl.glued g b × (h.decl.glued.C₁ → 𝕜)) ∉
            futureCollapsed
              (outwardRead fun r => (R r).comp (interfaceReading h.decl.glued h.wholeInterior g b))
              (fun _ : PUnit.{u + 1} => blockStep h.decl.glued g b law)) ∧
        ∃ d ∈ futureCollapsed
            (outwardRead fun r => (R r).comp (interfaceReading h.decl.glued h.wholeInterior g b))
            (fun _ : PUnit.{u + 1} => blockStep h.decl.glued g b law),
          ∃ n, 0 < n ∧ (⇑(blockStep h.decl.glued g b law))^[n] d = d ∧
            blockStep h.decl.glued g b law d ≠ d := by
  rw [holarchyGlobe_iff_coupled_notDetermined, constituent_coupled_iff,
    constituent_notDetermined_iff]

end LinearHolarchy

/-! ## 4. A globe of an actual Holarchy, and a block that is not one -/

section Instances

/-- [definition] A constituent complex with two regions on one face: region `false` is interior
(it touches no face), region `true` is bounded by the face. -/
abbrev innerOuterComplex : CellComplex ℚ where
  C₀ := Empty
  C₁ := Unit
  C₂ := Bool
  d₁ := 0
  d₂ := fun _ r => if r then 1 else 0
  dd := by ext i; exact i.elim

/-- [definition] The two-region constituent: a passive coholon on its shared port, both regions
oriented `+1`. -/
abbrev innerOuterConstituent : Constituent ℚ Bool Empty Empty (Empty ⊕ Unit) Empty where
  holon := coholonLeft
  complex := innerOuterComplex
  interior := fun _ => 1
  unit := fun _ => true
  portFace := fun _ => ()
  Nav := Empty
  navigator := fun x => x.elim
  pumpNavigator := fun x => x.elim

/-- [definition] The glued complex: the two left regions and the right region on the shared face,
the right region reversed. -/
abbrev globeComplex : CellComplex ℚ where
  C₀ := Empty
  C₁ := Unit
  C₂ := Bool ⊕ Unit
  d₁ := 0
  d₂ := fun _ r => match r with
    | .inl true => 1
    | .inl false => 0
    | .inr () => -1
  dd := by ext i; exact i.elim

/-- [definition] The gluing of the two-region constituent to the one-region right constituent. -/
abbrev globeDecl : JoinDeclaration innerOuterConstituent (rightConstituent true) where
  flowGain := 1
  effortGain := 1
  glued := globeComplex
  leftCells := ⟨fun x => Empty.elim x, fun _ => (), Sum.inl, fun x => Empty.elim x, fun _ => 1,
    fun _ => 1⟩
  rightCells := ⟨fun x => Empty.elim x, fun _ => (), fun _ => .inr (), fun x => Empty.elim x,
    fun _ => -1, fun _ => 1⟩
  jointRate := 1

/-- [established-bounded; formal-checked] The declaration glues. -/
theorem globeDecl_glues : globeDecl.Glues := by
  refine ⟨fun _ => rfl, by simp [JoinDeclaration.PowerCancels], fun side => ?_,
    fun side => ?_, ⟨fun v => Empty.elim v, fun _ => Or.inl ⟨(), rfl⟩, fun r => ?_⟩,
    fun _ => rfl, ⟨fun _ _ h => Sum.inl_ne_inr h, fun _ _ _ => ⟨(), rfl, rfl⟩⟩, fun _ => ?_, ?_⟩
  · cases side <;> refine ⟨by ext i; exact i.elim, ?_⟩ <;> ext i j <;>
      rw [Matrix.mul_apply, Matrix.mul_apply]
    · cases j <;> simp [CellEmbedding.m₁, CellEmbedding.m₂]
    · simp [CellEmbedding.m₁, CellEmbedding.m₂]
  · cases side
    · exact ⟨fun x => Empty.elim x, fun _ _ _ => rfl, Sum.inl_injective⟩
    · exact ⟨fun x => Empty.elim x, fun _ _ _ => rfl, fun _ _ _ => rfl⟩
  · rcases r with r | r
    · exact Or.inl ⟨r, rfl⟩
    · exact Or.inr ⟨(), rfl⟩
  · simp [JoinDeclaration.SharedFaceCancels, JoinDeclaration.sharedFaceBoundary, Matrix.mulVec,
      dotProduct]
  · rintro (p | p) <;> exact p.elim

/-- [definition] **The globe Holarchy.** -/
abbrev globeHolarchy : Holarchy innerOuterConstituent (rightConstituent true) :=
  ⟨globeDecl, globeDecl_glues⟩

/-- [definition] Its grain of two blocks: the left constituent's regions (`true`) and the right
constituent's region (`false`). -/
def globeGrain : Grain (Bool ⊕ Unit) Bool := ⟨fun b => if b then {.inl false, .inl true} else {.inr ()}⟩

/-- [definition] **The field law**: the inner region flips sign, the other regions are conserved,
and the face current reads the outer left region's storage (a charge read at the boundary). -/
def globeLaw : FieldLaw globeComplex where
  toFun s := (fun r => match r with
    | .inl false => -s.1 (.inl false)
    | r => s.1 r, fun _ => s.1 (.inl true))
  map_zero' := by ext r <;> [rcases r with (_ | _) | _; skip] <;> simp
  map_add' s t := by
    ext r
    · rcases r with (_ | _) | _ <;> simp [add_comm]
    · simp

/-- [definition] The receiver that reads the interface flux itself. -/
def fluxReceiver : PUnit.{1} → (ℚ →+ ℚ) := fun _ => AddMonoidHom.id ℚ

theorem globe_wholeInterior (r : Bool ⊕ Unit) : globeHolarchy.wholeInterior r = 1 := by
  rcases r with r | r <;>
    simp [Holarchy.wholeInterior, CellEmbedding.m₂, Matrix.mulVec, dotProduct]

theorem globe_surface (b : Bool) :
    (blockMembrane globeHolarchy.decl.glued globeHolarchy.wholeInterior globeGrain b).surface () =
      if b then 1 else -1 := by
  show (globeComplex.d₂ *ᵥ blockChain globeComplex globeHolarchy.wholeInterior globeGrain b) () = _
  cases b <;>
    simp [Matrix.mulVec, dotProduct, blockChain, globe_wholeInterior, Fintype.sum_sum_type,
      globeGrain]

theorem globe_interfaceReading (b : Bool) (j : Unit → ℚ) :
    interfaceReading globeHolarchy.decl.glued globeHolarchy.wholeInterior globeGrain b j =
      if b then j () else -j () := by
  show j ⬝ᵥ (blockMembrane globeHolarchy.decl.glued globeHolarchy.wholeInterior globeGrain b).surface = _
  rw [dotProduct, Fintype.sum_unique, globe_surface]
  cases b <;> simp

/-- [definition] The block interior carried by one region, with value `a`. -/
def globePoint (r : Bool ⊕ Unit) (a : ℚ) : BlockInterior globeComplex globeGrain true :=
  fun c => if c.1 = r then a else 0

theorem globe_mem_true (r : Bool) : (Sum.inl r : Bool ⊕ Unit) ∈ globeGrain.blocks true := by
  cases r <;> simp [globeGrain]

theorem globe_not_mem_true : (Sum.inr () : Bool ⊕ Unit) ∉ globeGrain.blocks true := by
  simp [globeGrain]

theorem globe_extend_true (x : BlockInterior globeComplex globeGrain true) (r : Bool) :
    extendBlock globeComplex globeGrain true x (.inl r) = x ⟨.inl r, globe_mem_true r⟩ := by
  simp [extendBlock, globe_mem_true r]

/-- The restricted law on the two-region block: the inner region flips, the outer region is
conserved, and the face current reads the outer region. -/
theorem globe_step_true (x : BlockInterior globeComplex globeGrain true) (j : Unit → ℚ) :
    blockStep globeHolarchy.decl.glued globeGrain true globeLaw (x, j) =
      (fun c => if c.1 = .inl false then -x c else x c,
        fun _ => x ⟨.inl true, globe_mem_true true⟩) := by
  change (((fun c : {c // c ∈ globeGrain.blocks true} =>
      (globeLaw (extendBlock globeComplex globeGrain true x, j)).1 c.1),
    fun _ => extendBlock globeComplex globeGrain true x (.inl true)) :
      BlockInterior globeComplex globeGrain true × (Unit → ℚ)) = _
  refine Prod.ext (funext fun c => ?_) (funext fun _ => globe_extend_true x true)
  obtain ⟨c, hc⟩ := c
  rcases c with (_ | _) | _
  · simp only [globeLaw, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [globe_extend_true]
    simp
  · simp only [globeLaw, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [globe_extend_true]
    simp
  · exact absurd hc globe_not_mem_true

/-- The restricted law on the one-region block: its region is conserved and the face current reads
nothing of it. -/
theorem globe_step_false (x : BlockInterior globeComplex globeGrain false) (j : Unit → ℚ) :
    blockStep globeHolarchy.decl.glued globeGrain false globeLaw (x, j) = (x, 0) := by
  change (((fun c : {c // c ∈ globeGrain.blocks false} =>
      (globeLaw (extendBlock globeComplex globeGrain false x, j)).1 c.1),
    fun _ => extendBlock globeComplex globeGrain false x (.inl true)) :
      BlockInterior globeComplex globeGrain false × (Unit → ℚ)) = _
  have hout : ∀ r : Bool, (Sum.inl r : Bool ⊕ Unit) ∉ globeGrain.blocks false := by
    intro r; simp [globeGrain]
  refine Prod.ext (funext fun c => ?_) (funext fun _ => by simp [extendBlock, hout])
  obtain ⟨c, hc⟩ := c
  rcases c with (_ | _) | _
  · exact absurd hc (hout false)
  · exact absurd hc (hout true)
  · simp [globeLaw, extendBlock, hc]

/-- The interface reading of the two-region block is the face current, that of the one-region block
its negative. -/
theorem globe_read (b : Bool) (s : BlockInterior globeComplex globeGrain b × (Unit → ℚ)) :
    outwardRead (fun r => (fluxReceiver r).comp
        (interfaceReading globeHolarchy.decl.glued globeHolarchy.wholeInterior globeGrain b))
      PUnit.unit s = if b then s.2 () else -s.2 () := by
  change interfaceReading globeHolarchy.decl.glued globeHolarchy.wholeInterior globeGrain b s.2 = _
  exact globe_interfaceReading b s.2

theorem globe_step_inner (a : ℚ) :
    blockStep globeHolarchy.decl.glued globeGrain true globeLaw (globePoint (.inl false) a, 0) =
      (globePoint (.inl false) (-a), 0) := by
  rw [globe_step_true]
  refine Prod.ext (funext fun c => ?_) (funext fun _ => ?_)
  · by_cases hc : c.1 = .inl false <;> simp [globePoint, hc]
  · simp [globePoint]

/-- The future-blind certificate: a state carried by the inner region alone, with no face current,
stays so under every word and is never read. -/
theorem globe_inner_blind (a : ℚ) :
    ((globePoint (.inl false) a, 0) : BlockInterior globeComplex globeGrain true × (Unit → ℚ)) ∈
      futureCollapsed
        (outwardRead fun r => (fluxReceiver r).comp
          (interfaceReading globeHolarchy.decl.glued globeHolarchy.wholeInterior globeGrain true))
        (fun _ : PUnit.{1} => blockStep globeHolarchy.decl.glued globeGrain true globeLaw) := by
  rw [mem_futureCollapsed_iff]
  intro r word
  have hword : ∀ (word : List PUnit.{1}) (a : ℚ), ∃ a' : ℚ,
      transportWord (fun g s => (fun _ : PUnit.{1} =>
          blockStep globeHolarchy.decl.glued globeGrain true globeLaw) g s) word
        (globePoint (.inl false) a, 0) = (globePoint (.inl false) a', 0) := by
    intro word
    induction word with
    | nil => exact fun a => ⟨a, rfl⟩
    | cons g word ih =>
      intro a
      obtain ⟨a', ha'⟩ := ih a
      exact ⟨-a', by rw [transportWord_cons, ha', globe_step_inner]⟩
  obtain ⟨a', ha'⟩ := hword word a
  rw [ha']
  cases r
  rw [globe_read]
  simp

/-- [established-bounded; formal-checked] **A globe of an actual Holarchy.** The two-region block
of `globeHolarchy`, under the field law that flips its inner region and reads its outer region's
conserved storage on the shared face, is relatively complete for the receiver that reads its
interface flux: coupled through the outer charge, and not determined because the inner region
flips unobserved and returns every two epochs. -/
theorem globeHolarchy_left_block_is_globe :
    HolarchyGlobe globeHolarchy globeGrain true globeLaw fluxReceiver := by
  rw [holarchyGlobe_iff_linear]
  refine ⟨⟨globePoint (.inl true) 1, fun hmem => ?_⟩,
    ⟨(globePoint (.inl false) 1, 0), globe_inner_blind 1, 2, two_pos, ?_, ?_⟩⟩
  · rw [mem_futureCollapsed_iff] at hmem
    have h1 := hmem PUnit.unit [PUnit.unit]
    rw [transportWord_cons, transportWord_nil] at h1
    change outwardRead (fun r => (fluxReceiver r).comp
        (interfaceReading globeHolarchy.decl.glued globeHolarchy.wholeInterior globeGrain true))
      PUnit.unit (blockStep globeHolarchy.decl.glued globeGrain true globeLaw
        (globePoint (.inl true) 1, 0)) = 0 at h1
    rw [globe_step_true, globe_read] at h1
    simp [globePoint] at h1
  · rw [Function.iterate_succ_apply, Function.iterate_one, globe_step_inner, globe_step_inner,
      neg_neg]
  · rw [globe_step_inner]
    intro h
    have := congrFun (congrArg Prod.fst h) ⟨.inl false, globe_mem_true false⟩
    simp [globePoint] at this
    norm_num at this

/-- [counterexample; formal-checked] **A block that is not a globe.** The one-region block of the
same Holarchy under the same law is not a globe for the same receiver: its storage is conserved
and every difference invisible to its interface is fixed by the law, so clause (2) fails. -/
theorem globeHolarchy_right_block_is_not_globe :
    ¬ HolarchyGlobe globeHolarchy globeGrain false globeLaw fluxReceiver := by
  rw [holarchyGlobe_iff_linear]
  rintro ⟨-, d, hd, n, -, -, hmove⟩
  rw [mem_futureCollapsed_iff] at hd
  have h0 := hd PUnit.unit []
  rw [transportWord_nil] at h0
  change outwardRead (fun r => (fluxReceiver r).comp
      (interfaceReading globeHolarchy.decl.glued globeHolarchy.wholeInterior globeGrain false))
    PUnit.unit d = 0 at h0
  rw [globe_read] at h0
  obtain ⟨d₁, d₂⟩ := d
  have hd₂ : d₂ = 0 := funext fun u => by cases u; simpa using h0
  subst hd₂
  exact hmove (globe_step_false d₁ 0)

end Instances

/-! ## 5. Membrane-level counterexamples on the square complex -/

section Square

/-- [counterexample; formal-checked] **The open tube is not a constituent**: no region of the
square has the tube's lateral membrane as its membrane (`tubeMembrane_escapes`); a region's
membrane bounds its interior by construction. -/
theorem tube_is_not_a_constituent (region : ℚ) :
    constituentMembrane squareBoundary₁ squareBoundary₂ square_boundary_squared region ≠
      tubeMembrane := by
  intro h
  apply tubeMembrane_escapes.2
  rw [← h]
  exact (constituentMembrane_boundsInterior _ _ _ _).bounds

/-- [counterexample; formal-checked] **The hollow loop bounds no region** of its faceless complex
(`hollowMembrane_closed_not_bounds`). -/
theorem hollow_is_not_a_constituent (region : ℚ) (hbb : squareBoundary₁.comp 0 = 0) :
    constituentMembrane squareBoundary₁ (0 : ℚ →ₗ[ℚ] (Fin 4 → ℚ)) hbb region ≠
      hollowMembrane := by
  intro h
  apply hollowMembrane_closed_not_bounds.2
  rw [← h]
  exact (constituentMembrane_boundsInterior _ _ _ _).bounds

end Square

end Holonics.HolarchyCore
