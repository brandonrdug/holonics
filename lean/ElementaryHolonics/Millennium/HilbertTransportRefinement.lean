import ElementaryHolonics.Millennium.HilbertReceiverForm

/-!
# Directed refinement of finite Hilbert transport complexes

This file composes three existing owners:

* `HilbertTransportChain` owns an actual finite Hilbert complex, its adjoints, harmonic and
  non-harmonic populations, and its middle Hodge Laplacian;
* `HilbertReceiverForm` owns the Laplacian energy receiver and finite complement coercivity;
* `YangMillsLimit` names the additional scale-uniform separator required before a continuum
  mass-gap inference is lawful.

A refinement is not merely a map of the two differentials.  It consists of isometric maps on all
three carriers which commute with both differentials and both adjoints.  Those four local squares
return the exact consequences needed here: harmonic and non-harmonic populations transport,
middle Laplacians intertwine, and the Laplacian energy is unchanged on every transported
occurrence.

A directed scale system then retains coherent refinements between actual finite complexes.  Every
individual non-harmonic receiver is coercive by finite dimensionality, but the shared positive
separator is left as the explicit proposition `HasUniformNonharmonicGap`.  Its exact negation is
`HasUniformGapDefect`: at every proposed positive separator, some scale and some non-harmonic
occurrence violate it.  No theorem below chooses either side, constructs a continuum limit,
identifies a complex with gauge fields, or asserts the Yang--Mills mass gap.

Truth status: the structures are `definition`; every theorem is `proved-derived`; the existence
of a scale-uniform gap and a continuum realization remain `open`.
-/

noncomputable section

open InnerProductSpace

namespace Soma.Holonics.Millennium.Coupling

universe u v

/-- One actual finite-dimensional Hilbert transport complex, bundled with all carrier instances
needed by `HilbertTransportChain`. -/
structure FiniteHilbertTransportComplex where
  Left : Type u
  [leftNormedAddCommGroup : NormedAddCommGroup Left]
  [leftInnerProductSpace : InnerProductSpace ℝ Left]
  [leftFiniteDimensional : FiniteDimensional ℝ Left]
  Middle : Type u
  [middleNormedAddCommGroup : NormedAddCommGroup Middle]
  [middleInnerProductSpace : InnerProductSpace ℝ Middle]
  [middleFiniteDimensional : FiniteDimensional ℝ Middle]
  Right : Type u
  [rightNormedAddCommGroup : NormedAddCommGroup Right]
  [rightInnerProductSpace : InnerProductSpace ℝ Right]
  [rightFiniteDimensional : FiniteDimensional ℝ Right]
  chain : HilbertTransportChain Left Middle Right

attribute [instance]
  FiniteHilbertTransportComplex.leftNormedAddCommGroup
  FiniteHilbertTransportComplex.leftInnerProductSpace
  FiniteHilbertTransportComplex.leftFiniteDimensional
  FiniteHilbertTransportComplex.middleNormedAddCommGroup
  FiniteHilbertTransportComplex.middleInnerProductSpace
  FiniteHilbertTransportComplex.middleFiniteDimensional
  FiniteHilbertTransportComplex.rightNormedAddCommGroup
  FiniteHilbertTransportComplex.rightInnerProductSpace
  FiniteHilbertTransportComplex.rightFiniteDimensional

/-- A coarse-to-fine refinement which respects the complete finite Hodge operator.

The differential squares alone define a chain map.  The two adjoint squares are the additional
reducing-subcomplex receipt which makes harmonic transport and Laplacian intertwining valid. -/
structure HilbertTransportRefinement
    (source target : FiniteHilbertTransportComplex) where
  left : source.Left →ₗᵢ[ℝ] target.Left
  middle : source.Middle →ₗᵢ[ℝ] target.Middle
  right : source.Right →ₗᵢ[ℝ] target.Right
  into_natural : ∀ a,
    target.chain.into (left a) = middle (source.chain.into a)
  outOf_natural : ∀ b,
    target.chain.outOf (middle b) = right (source.chain.outOf b)
  incomingAdjoint_natural : ∀ b,
    target.chain.incomingAdjoint (middle b) = left (source.chain.incomingAdjoint b)
  outgoingAdjoint_natural : ∀ c,
    target.chain.outgoingAdjoint (right c) = middle (source.chain.outgoingAdjoint c)

namespace HilbertTransportRefinement

variable {source middle target : FiniteHilbertTransportComplex}

/-- The identity refinement. -/
def id (source : FiniteHilbertTransportComplex) :
    HilbertTransportRefinement source source where
  left := LinearIsometry.id
  middle := LinearIsometry.id
  right := LinearIsometry.id
  into_natural := fun _ ↦ rfl
  outOf_natural := fun _ ↦ rfl
  incomingAdjoint_natural := fun _ ↦ rfl
  outgoingAdjoint_natural := fun _ ↦ rfl

/-- Serial composition of two refinements retains every differential and adjoint square. -/
def comp (later : HilbertTransportRefinement middle target)
    (earlier : HilbertTransportRefinement source middle) :
    HilbertTransportRefinement source target where
  left := later.left.comp earlier.left
  middle := later.middle.comp earlier.middle
  right := later.right.comp earlier.right
  into_natural := by
    intro a
    change target.chain.into (later.left (earlier.left a)) =
      later.middle (earlier.middle (source.chain.into a))
    rw [later.into_natural, earlier.into_natural]
  outOf_natural := by
    intro b
    change target.chain.outOf (later.middle (earlier.middle b)) =
      later.right (earlier.right (source.chain.outOf b))
    rw [later.outOf_natural, earlier.outOf_natural]
  incomingAdjoint_natural := by
    intro b
    change target.chain.incomingAdjoint (later.middle (earlier.middle b)) =
      later.left (earlier.left (source.chain.incomingAdjoint b))
    rw [later.incomingAdjoint_natural, earlier.incomingAdjoint_natural]
  outgoingAdjoint_natural := by
    intro c
    change target.chain.outgoingAdjoint (later.right (earlier.right c)) =
      later.middle (earlier.middle (source.chain.outgoingAdjoint c))
    rw [later.outgoingAdjoint_natural, earlier.outgoingAdjoint_natural]

variable (R : HilbertTransportRefinement source target)

/-- A refinement carries every harmonic occurrence to a harmonic occurrence. -/
theorem maps_harmonic {x : source.Middle} (hx : x ∈ source.chain.harmonic) :
    R.middle x ∈ target.chain.harmonic := by
  change target.chain.outOf (R.middle x) = 0 ∧
    target.chain.incomingAdjoint (R.middle x) = 0
  change source.chain.outOf x = 0 ∧ source.chain.incomingAdjoint x = 0 at hx
  rw [R.outOf_natural, R.incomingAdjoint_natural, hx.1, hx.2, map_zero, map_zero]
  exact ⟨rfl, rfl⟩

/-- The transported harmonic population as an actual linear isometry of subspaces. -/
def harmonicMap : source.chain.harmonic →ₗᵢ[ℝ] target.chain.harmonic where
  toLinearMap :=
    { toFun := fun x ↦ ⟨R.middle x, R.maps_harmonic x.property⟩
      map_add' := by
        intro x y
        ext
        exact R.middle.map_add x y
      map_smul' := by
        intro c x
        ext
        exact R.middle.map_smul c x }
  norm_map' := by
    intro x
    exact R.middle.norm_map x

/-- A refinement carries exact occurrences to exact occurrences. -/
theorem maps_exact {x : source.Middle} (hx : x ∈ source.chain.exact) :
    R.middle x ∈ target.chain.exact := by
  obtain ⟨a, rfl⟩ := hx
  refine ⟨R.left a, ?_⟩
  exact R.into_natural a

/-- A refinement carries coexact occurrences to coexact occurrences. -/
theorem maps_coexact {x : source.Middle} (hx : x ∈ source.chain.coexact) :
    R.middle x ∈ target.chain.coexact := by
  obtain ⟨c, rfl⟩ := hx
  refine ⟨R.right c, ?_⟩
  exact R.outgoingAdjoint_natural c

/-- A refinement carries the complete exact-plus-coexact population to the target's
non-harmonic population. -/
theorem maps_nonharmonic {x : source.Middle} (hx : x ∈ source.chain.nonharmonic) :
    R.middle x ∈ target.chain.nonharmonic := by
  obtain ⟨e, he, c, hc, rfl⟩ := Submodule.mem_sup.mp hx
  change R.middle (e + c) ∈ target.chain.exact ⊔ target.chain.coexact
  simpa only [map_add] using
    (Submodule.add_mem_sup (R.maps_exact he) (R.maps_coexact hc))

/-- The transported non-harmonic population as an actual linear isometry of subspaces. -/
def nonharmonicMap : source.chain.nonharmonic →ₗᵢ[ℝ] target.chain.nonharmonic where
  toLinearMap :=
    { toFun := fun x ↦ ⟨R.middle x, R.maps_nonharmonic x.property⟩
      map_add' := by
        intro x y
        ext
        exact R.middle.map_add x y
      map_smul' := by
        intro c x
        ext
        exact R.middle.map_smul c x }
  norm_map' := by
    intro x
    exact R.middle.norm_map x

/-- The four local refinement squares make the middle Hodge Laplacian commute with refinement. -/
theorem middleLaplacian_natural (x : source.Middle) :
    target.chain.middleLaplacian (R.middle x) =
      R.middle (source.chain.middleLaplacian x) := by
  change
    target.chain.into (target.chain.incomingAdjoint (R.middle x)) +
        target.chain.outgoingAdjoint (target.chain.outOf (R.middle x)) =
      R.middle
        (source.chain.into (source.chain.incomingAdjoint x) +
          source.chain.outgoingAdjoint (source.chain.outOf x))
  rw [R.incomingAdjoint_natural, R.outOf_natural,
    R.into_natural, R.outgoingAdjoint_natural, map_add]

/-- Laplacian energy is exactly unchanged on transported occurrences. -/
theorem laplacianEnergyForm_natural (x y : source.Middle) :
    target.chain.laplacianEnergyForm (R.middle x) (R.middle y) =
      source.chain.laplacianEnergyForm x y := by
  rw [HilbertTransportChain.laplacianEnergyForm_apply,
    HilbertTransportChain.laplacianEnergyForm_apply, R.middleLaplacian_natural]
  exact R.middle.inner_map_map (source.chain.middleLaplacian x) y

/-- The non-harmonic receiver reading commutes with the actual refinement map. -/
theorem nonharmonicReceiverForm_natural
    (x y : source.chain.nonharmonic) :
    target.chain.nonharmonicReceiverForm.B (R.nonharmonicMap x) (R.nonharmonicMap y) =
      source.chain.nonharmonicReceiverForm.B x y := by
  rw [target.chain.nonharmonicReceiverForm_reading,
    source.chain.nonharmonicReceiverForm_reading]
  exact R.laplacianEnergyForm_natural x y

/-- Fine non-harmonic occurrences orthogonal to the transported coarse population.

This is the explicit new-mode population on which an individual refinement supplies no gap
comparison.  It may be trivial or nontrivial; no declaration below chooses either case. -/
def newNonharmonicModes : Submodule ℝ target.Middle :=
  (source.chain.nonharmonic.map R.middle.toLinearMap)ᗮ ⊓ target.chain.nonharmonic

/-- Every new mode is genuinely non-harmonic at the fine scale. -/
theorem newNonharmonicModes_le_nonharmonic :
    R.newNonharmonicModes ≤ target.chain.nonharmonic :=
  inf_le_right

/-- Every new fine mode is orthogonal to every transported coarse non-harmonic occurrence. -/
theorem inner_transported_newNonharmonicModes_eq_zero
    (x : source.chain.nonharmonic) {y : target.Middle}
    (hy : y ∈ R.newNonharmonicModes) :
    inner ℝ (R.middle x) y = 0 := by
  exact Submodule.inner_right_of_mem_orthogonal
    (K := source.chain.nonharmonic.map R.middle.toLinearMap)
    ⟨(x : source.Middle), x.property, rfl⟩ hy.1

end HilbertTransportRefinement

/-- A coherent directed family of actual finite Hilbert transport complexes. -/
structure DirectedHilbertTransportSystem (Scale : Type v) [Preorder Scale] [Nonempty Scale] where
  object : Scale → FiniteHilbertTransportComplex.{u}
  refinement : ∀ {coarse fine : Scale}, coarse ≤ fine →
    HilbertTransportRefinement.{u, u} (object coarse) (object fine)
  directed : ∀ (left right : Scale), ∃ common : Scale, left ≤ common ∧ right ≤ common
  refinement_refl : ∀ scale : Scale,
    refinement (le_refl scale) = HilbertTransportRefinement.id (object scale)
  refinement_trans : ∀ {first second third : Scale}
      (hfirst : first ≤ second) (hsecond : second ≤ third),
    refinement (hfirst.trans hsecond) =
      HilbertTransportRefinement.comp (refinement hsecond) (refinement hfirst)

namespace DirectedHilbertTransportSystem

variable {Scale : Type v} [Preorder Scale] [Nonempty Scale]
variable (system : DirectedHilbertTransportSystem.{u, v} Scale)

/-- One positive lower bound valid on the non-harmonic receiver at every admitted scale. -/
def HasUniformNonharmonicGap : Prop :=
  ∃ Δ : ℝ, 0 < Δ ∧
    ∀ (scale : Scale) (x : (system.object scale).chain.nonharmonic),
      Δ * ‖x‖ ^ 2 ≤
        (system.object scale).chain.nonharmonicReceiverForm.B x x

/-- The exact failure receipt for a scale-uniform gap: every proposed positive separator is
violated by a named scale and non-harmonic occurrence. -/
def HasUniformGapDefect : Prop :=
  ∀ Δ : ℝ, 0 < Δ →
    ∃ (scale : Scale) (x : (system.object scale).chain.nonharmonic),
      (system.object scale).chain.nonharmonicReceiverForm.B x x < Δ * ‖x‖ ^ 2

/-- The defect is exactly the logical complement of the uniform-gap proposition. -/
theorem not_hasUniformNonharmonicGap_iff :
    ¬ system.HasUniformNonharmonicGap ↔ system.HasUniformGapDefect := by
  classical
  simp only [HasUniformNonharmonicGap, HasUniformGapDefect, not_exists, not_and,
    not_forall, not_le]

/-- Every individual finite scale is coercive on its non-harmonic complement.

The scale-dependent witness returned here is deliberately not promoted to a common `Δ`. -/
theorem eachScaleHasNonharmonicGap (scale : Scale) :
    (system.object scale).chain.nonharmonicReceiverForm.IsCoercive :=
  (system.object scale).chain.nonharmonicReceiverForm_isCoercive

/-- A uniform gap specializes to the same quantitative bound at every chosen scale. -/
theorem uniformGap_specializes
    (hgap : system.HasUniformNonharmonicGap) (scale : Scale) :
    ∃ Δ : ℝ, 0 < Δ ∧
      ∀ x : (system.object scale).chain.nonharmonic,
        Δ * ‖x‖ ^ 2 ≤
          (system.object scale).chain.nonharmonicReceiverForm.B x x := by
  obtain ⟨Δ, hΔ, hbound⟩ := hgap
  exact ⟨Δ, hΔ, hbound scale⟩

end DirectedHilbertTransportSystem

end Soma.Holonics.Millennium.Coupling
