import Mathlib.Analysis.InnerProductSpace.PiL2
import ElementaryHolonics.Millennium.HilbertTransportRefinement

/-!
# A concrete dimension-changing Hilbert refinement

This file realizes the abstract directed-refinement owner on two actual finite scales.  At each
scale the incoming differential is the identity and the outgoing differential is zero.  The
coarse middle carrier is `ℝ`; the fine middle carrier is `EuclideanSpace ℝ (Fin 2)`; and
refinement inserts the coarse occurrence as the first orthogonal coordinate.

The family is genuinely nonconstant: its middle finrank grows from one to two.  The complete
differential and adjoint squares commute, and the middle Laplacian is the identity at both scales,
so the shared non-harmonic gap is exactly bounded below by one.  This is a finite two-scale
realization only.  It is not a lattice gauge complex, a continuum limit, or a Yang--Mills mass-gap
theorem.

Truth status: all structures below are `definition`; every theorem is `proved-derived`.  A
geometric/gauge realization and an unbounded refinement family remain `open`.
-/

noncomputable section

open InnerProductSpace

namespace Soma.Holonics.Millennium.Coupling

universe u

/-- The exact finite chain `V --id--> V --0--> V`. -/
def identityZeroComplex (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    FiniteHilbertTransportComplex where
  Left := V
  Middle := V
  Right := V
  chain :=
    { into := ContinuousLinearMap.id ℝ V
      outOf := 0
      composite_zero := by simp }

/-- Any linear isometry gives a complete refinement between identity--zero complexes. -/
def identityZeroRefinement
    {V W : Type u}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (f : V →ₗᵢ[ℝ] W) :
    HilbertTransportRefinement (identityZeroComplex V) (identityZeroComplex W) where
  left := f
  middle := f
  right := f
  into_natural := by simp [identityZeroComplex]
  outOf_natural := by simp [identityZeroComplex]
  incomingAdjoint_natural := by
    simp [identityZeroComplex, HilbertTransportChain.incomingAdjoint]
  outgoingAdjoint_natural := by
    simp [identityZeroComplex, HilbertTransportChain.outgoingAdjoint]

/-- The two admitted refinement scales. -/
inductive TwoHilbertScale where
  | coarse
  | fine
  deriving DecidableEq, Inhabited

namespace TwoHilbertScale

/-- The coarse scale precedes both scales, while the fine scale precedes only itself. -/
def le : TwoHilbertScale → TwoHilbertScale → Prop
  | .coarse, _ => True
  | .fine, .coarse => False
  | .fine, .fine => True

instance : LE TwoHilbertScale := ⟨le⟩

instance : Preorder TwoHilbertScale where
  le := le
  le_refl := by
    intro scale
    cases scale <;> trivial
  le_trans := by
    intro first second third hfirst hsecond
    cases first <;> cases second <;> cases third <;> trivial

end TwoHilbertScale

/-- The coarse line and fine plane as actual identity--zero Hilbert complexes. -/
def twoScaleObject : TwoHilbertScale → FiniteHilbertTransportComplex
  | .coarse => identityZeroComplex ℝ
  | .fine => identityZeroComplex (EuclideanSpace ℝ (Fin 2))

/-- The coordinate inclusion `x ↦ x e₀` from the real line into the Euclidean plane. -/
def realToEuclideanPlane : ℝ →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toLinearMap :=
    { toFun := fun x ↦ EuclideanSpace.single 0 x
      map_add' := by
        intro x y
        ext i
        by_cases hi : i = 0 <;> simp [EuclideanSpace.single_apply, hi]
      map_smul' := by
        intro c x
        ext i
        simp [EuclideanSpace.single_apply] }
  norm_map' := by
    intro x
    exact EuclideanSpace.norm_single 0 x

/-- The only strict refinement inserts the line into the first coordinate of the plane. -/
def coarseToFineRefinement :
    HilbertTransportRefinement
      (twoScaleObject .coarse) (twoScaleObject .fine) :=
  identityZeroRefinement realToEuclideanPlane

/-- The refinement selected by a witnessed comparison of the two scales. -/
def twoScaleRefinement : ∀ {lower upper : TwoHilbertScale}, lower ≤ upper →
    HilbertTransportRefinement (twoScaleObject lower) (twoScaleObject upper) := by
  intro lower upper h
  cases lower <;> cases upper
  · exact HilbertTransportRefinement.id _
  · exact coarseToFineRefinement
  · exact False.elim h
  · exact HilbertTransportRefinement.id _

/-- Two refinements are equal when their three isometric carrier maps agree pointwise. -/
private theorem refinement_ext
    {source target : FiniteHilbertTransportComplex}
    {R S : HilbertTransportRefinement source target}
    (hleft : ∀ x, R.left x = S.left x)
    (hmiddle : ∀ x, R.middle x = S.middle x)
    (hright : ∀ x, R.right x = S.right x) : R = S := by
  cases R
  cases S
  simp_all only
  congr
  · ext x
    exact hleft x
  · ext x
    exact hmiddle x
  · ext x
    exact hright x

/-- The concrete dimension-changing two-scale directed system. -/
def twoScaleSystem : DirectedHilbertTransportSystem TwoHilbertScale where
  object := twoScaleObject
  refinement := twoScaleRefinement
  directed := by
    intro left right
    exact ⟨.fine, by cases left <;> trivial, by cases right <;> trivial⟩
  refinement_refl := by
    intro scale
    cases scale <;> rfl
  refinement_trans := by
    intro first second third hfirst hsecond
    cases first <;> cases second <;> cases third
    all_goals try { exact False.elim hfirst }
    all_goals try { exact False.elim hsecond }
    all_goals
      apply refinement_ext <;> intro x <;> rfl

/-- The object family is genuinely dimension-changing at the middle carrier. -/
theorem twoScale_middle_finrank_strict :
    Module.finrank ℝ (twoScaleSystem.object .coarse).Middle <
      Module.finrank ℝ (twoScaleSystem.object .fine).Middle := by
  change Module.finrank ℝ ℝ < Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))
  norm_num

/-- The fine coordinate which is absent from the transported coarse line. -/
def fineSecondMode : EuclideanSpace ℝ (Fin 2) :=
  EuclideanSpace.single 1 1

/-- The added fine coordinate is a nonzero new non-harmonic mode, orthogonal to the complete
transported coarse population. -/
theorem fineSecondMode_mem_newNonharmonicModes :
    fineSecondMode ∈ coarseToFineRefinement.newNonharmonicModes := by
  constructor
  · change fineSecondMode ∈
      ((identityZeroComplex ℝ).chain.nonharmonic.map realToEuclideanPlane.toLinearMap)ᗮ
    rw [Submodule.mem_orthogonal']
    intro u hu
    obtain ⟨x, hx, rfl⟩ := hu
    change inner ℝ fineSecondMode (realToEuclideanPlane x) = 0
    simp [fineSecondMode, realToEuclideanPlane, EuclideanSpace.inner_single_left,
      EuclideanSpace.single_apply]
  · change fineSecondMode ∈
      (identityZeroComplex (EuclideanSpace ℝ (Fin 2))).chain.nonharmonic
    apply Submodule.mem_sup_left
    change fineSecondMode ∈
      (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))).range
    exact ⟨fineSecondMode, rfl⟩

/-- The new fine mode is not the zero occurrence. -/
theorem fineSecondMode_ne_zero : fineSecondMode ≠ 0 := by
  simp [fineSecondMode, EuclideanSpace.single_eq_zero_iff]

/-- The identity--zero complex has Laplacian energy exactly equal to squared norm. -/
theorem identityZeroComplex_laplacianEnergy_self
    (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    (x : V) :
    (identityZeroComplex V).chain.laplacianEnergyForm x x = ‖x‖ ^ 2 := by
  rw [HilbertTransportChain.laplacianEnergyForm_self]
  simp [identityZeroComplex, HilbertTransportChain.incomingAdjoint]

/-- Every occurrence in an identity--zero complex is non-harmonic: it arrives through the
identity incoming differential. -/
theorem identityZeroComplex_nonharmonic_eq_top
    (V : Type u)
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] :
    (identityZeroComplex V).chain.nonharmonic = ⊤ := by
  apply top_unique
  intro x _
  apply Submodule.mem_sup_left
  change x ∈ (ContinuousLinearMap.id ℝ V).range
  exact ⟨x, rfl⟩

/-- Both scales share the quantitative non-harmonic lower bound `Δ = 1`. -/
theorem twoScaleSystem_hasUniformNonharmonicGap :
    twoScaleSystem.HasUniformNonharmonicGap := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro scale x
  rw [(twoScaleSystem.object scale).chain.nonharmonicReceiverForm_reading]
  cases scale with
  | coarse =>
      change 1 * ‖(x.val : ℝ)‖ ^ 2 ≤
        (identityZeroComplex ℝ).chain.laplacianEnergyForm x.val x.val
      rw [identityZeroComplex_laplacianEnergy_self]
      rw [one_mul, Real.norm_eq_abs, sq_abs]
  | fine =>
      change 1 * ‖(x.val : EuclideanSpace ℝ (Fin 2))‖ ^ 2 ≤
        (identityZeroComplex (EuclideanSpace ℝ (Fin 2))).chain.laplacianEnergyForm x.val x.val
      rw [identityZeroComplex_laplacianEnergy_self]
      simp

/-- No lower-bound constant larger than one can hold on this family.  Together with
`twoScaleSystem_hasUniformNonharmonicGap`, this identifies one as the optimal uniform gap. -/
theorem twoScaleSystem_uniformGapConstant_le_one
    {Δ : ℝ}
    (hbound : ∀ (scale : TwoHilbertScale)
      (x : (twoScaleSystem.object scale).chain.nonharmonic),
      Δ * ‖x‖ ^ 2 ≤
        (twoScaleSystem.object scale).chain.nonharmonicReceiverForm.B x x) :
    Δ ≤ 1 := by
  let unit : (identityZeroComplex ℝ).chain.nonharmonic :=
    ⟨(1 : ℝ), by
      change (1 : ℝ) ∈ (identityZeroComplex ℝ).chain.nonharmonic
      rw [identityZeroComplex_nonharmonic_eq_top]
      exact Submodule.mem_top⟩
  have hunit := hbound .coarse unit
  dsimp [unit] at hunit
  rw [(twoScaleSystem.object .coarse).chain.nonharmonicReceiverForm_reading] at hunit
  change Δ * ‖(1 : ℝ)‖ ^ 2 ≤
    (identityZeroComplex ℝ).chain.laplacianEnergyForm (1 : ℝ) (1 : ℝ) at hunit
  rw [identityZeroComplex_laplacianEnergy_self] at hunit
  norm_num at hunit
  exact hunit

/-- Consequently the exact gap-defect proposition is false for this concrete family. -/
theorem twoScaleSystem_not_hasUniformGapDefect :
    ¬ twoScaleSystem.HasUniformGapDefect := by
  rw [← twoScaleSystem.not_hasUniformNonharmonicGap_iff]
  exact not_not_intro twoScaleSystem_hasUniformNonharmonicGap

end Soma.Holonics.Millennium.Coupling
