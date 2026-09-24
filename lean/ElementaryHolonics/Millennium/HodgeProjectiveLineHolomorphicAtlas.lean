import ElementaryHolonics.Millennium.HodgeProjectiveLineDivisors
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Holomorphic transition laws for the projective-line product atlas

The preceding atlas file constructs exact affine charts on the actual projectivization quotient.
Here we prove the missing analytic compatibility: every one-dimensional transition is either the
identity or complex inversion on its nonzero overlap, and every product transition is the
coordinatewise product of those maps.  Consequently every admitted overlap transition is complex
differentiable.

This is a constructed complex-atlas certificate.  It is not yet an instance of Mathlib's manifold
API because that API does not supply a topology on `Projectivization`; the next topology owner can
be induced from these exact charts without postulating a transition law.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HodgeProjectiveLineHolomorphicAtlas

open Soma.Holonics.Millennium.HodgeProjectiveLineProduct
open Soma.Holonics.Millennium.HodgeProjectiveLineAtlas

/-- [definition] The exact affine transition: unchanged pivot gives identity, changed pivot gives
inversion. -/
def transition : AffineChart → AffineChart → ℂ → ℂ
  | .first, .first => id
  | .second, .second => id
  | .first, .second => fun z => z⁻¹
  | .second, .first => fun z => z⁻¹

/-- [definition] Inversion transitions are admitted only away from zero. -/
def TransitionAdmissible (source target : AffineChart) (z : ℂ) : Prop :=
  source = target ∨ z ≠ 0

/-- [proved-derived; formal-checked] If a projective point lies in two distinct charts, its
coordinate in either source chart is nonzero. -/
theorem coordinate_ne_zero_of_distinct_overlap
    {source target : AffineChart} (hne : source ≠ target)
    (projectivePoint : ComplexProjectiveLine)
    (hsource : InChart source projectivePoint)
    (htarget : InChart target projectivePoint) :
    coordinate source ⟨projectivePoint, hsource⟩ ≠ 0 := by
  cases source <;> cases target
  · exact (hne rfl).elim
  · exact div_ne_zero htarget hsource
  · exact div_ne_zero htarget hsource
  · exact (hne rfl).elim

/-- [proved-derived; formal-checked] Every actual overlap produces the domain proof required by
its transition function. -/
theorem overlap_admissible
    (source target : AffineChart)
    (projectivePoint : ComplexProjectiveLine)
    (hsource : InChart source projectivePoint)
    (htarget : InChart target projectivePoint) :
    TransitionAdmissible source target (coordinate source ⟨projectivePoint, hsource⟩) := by
  by_cases hequal : source = target
  · exact Or.inl hequal
  · exact Or.inr (coordinate_ne_zero_of_distinct_overlap hequal projectivePoint hsource htarget)

/-- [proved-derived; formal-checked] The coordinate receiver commutes with the exact overlap
transition. -/
theorem coordinate_transition
    (source target : AffineChart)
    (projectivePoint : ComplexProjectiveLine)
    (hsource : InChart source projectivePoint)
    (htarget : InChart target projectivePoint) :
    coordinate target ⟨projectivePoint, htarget⟩ =
      transition source target (coordinate source ⟨projectivePoint, hsource⟩) := by
  cases source <;> cases target
  · rfl
  · exact overlap_transition projectivePoint hsource htarget
  · simp only [transition, coordinate, AffineChart.other, AffineChart.pivot]
    field_simp [hsource, htarget]
  · rfl

/-- [proved-derived; formal-checked] Every admitted one-dimensional transition is complex
differentiable at the addressed coordinate. -/
theorem transition_differentiableAt
    (source target : AffineChart) (z : ℂ)
    (hadmitted : TransitionAdmissible source target z) :
    DifferentiableAt ℂ (transition source target) z := by
  cases source <;> cases target
  · simpa [transition] using (differentiableAt_id : DifferentiableAt ℂ id z)
  · exact differentiableAt_inv (hadmitted.resolve_left (by decide))
  · exact differentiableAt_inv (hadmitted.resolve_left (by decide))
  · simpa [transition] using (differentiableAt_id : DifferentiableAt ℂ id z)

/-- [proved-derived; formal-checked] The changed-chart transition has the exact derivative
`-z⁻²`; no limiting or numerical approximation is used. -/
theorem transition_hasDerivAt_of_ne
    {source target : AffineChart} (hne : source ≠ target) {z : ℂ} (hz : z ≠ 0) :
    HasDerivAt (transition source target) (-(z ^ 2)⁻¹) z := by
  cases source <;> cases target
  · exact (hne rfl).elim
  · exact hasDerivAt_inv hz
  · exact hasDerivAt_inv hz
  · exact (hne rfl).elim

/-! ## Product transitions -/

/-- [definition] Product-chart transitions act independently on the two addressed coordinates. -/
def surfaceTransition (source target : SurfaceChart) (z : ℂ × ℂ) : ℂ × ℂ :=
  (transition source.1 target.1 z.1, transition source.2 target.2 z.2)

/-- [definition] Both coordinate transitions must be admitted. -/
def SurfaceTransitionAdmissible (source target : SurfaceChart) (z : ℂ × ℂ) : Prop :=
  TransitionAdmissible source.1 target.1 z.1 ∧
    TransitionAdmissible source.2 target.2 z.2

theorem surface_overlap_admissible
    (source target : SurfaceChart) (surfacePoint : Surface)
    (hsource : InSurfaceChart source surfacePoint)
    (htarget : InSurfaceChart target surfacePoint) :
    SurfaceTransitionAdmissible source target
      (surfaceCoordinate source ⟨surfacePoint, hsource⟩) :=
  ⟨overlap_admissible source.1 target.1 surfacePoint.1 hsource.1 htarget.1,
    overlap_admissible source.2 target.2 surfacePoint.2 hsource.2 htarget.2⟩

/-- [proved-derived; formal-checked] Every actual surface overlap commutes with the product
transition map. -/
theorem surface_coordinate_transition
    (source target : SurfaceChart) (surfacePoint : Surface)
    (hsource : InSurfaceChart source surfacePoint)
    (htarget : InSurfaceChart target surfacePoint) :
    surfaceCoordinate target ⟨surfacePoint, htarget⟩ =
      surfaceTransition source target (surfaceCoordinate source ⟨surfacePoint, hsource⟩) := by
  apply Prod.ext
  · exact coordinate_transition source.1 target.1 surfacePoint.1 hsource.1 htarget.1
  · exact coordinate_transition source.2 target.2 surfacePoint.2 hsource.2 htarget.2

/-- [proved-derived; formal-checked] Every admitted product transition is complex differentiable. -/
theorem surfaceTransition_differentiableAt
    (source target : SurfaceChart) (z : ℂ × ℂ)
    (hadmitted : SurfaceTransitionAdmissible source target z) :
    DifferentiableAt ℂ (surfaceTransition source target) z := by
  have hfirst : DifferentiableAt ℂ
      (fun point : ℂ × ℂ => transition source.1 target.1 point.1) z :=
    (transition_differentiableAt source.1 target.1 z.1 hadmitted.1).comp z
      differentiableAt_fst
  have hsecond : DifferentiableAt ℂ
      (fun point : ℂ × ℂ => transition source.2 target.2 point.2) z :=
    (transition_differentiableAt source.2 target.2 z.2 hadmitted.2).comp z
      differentiableAt_snd
  exact hfirst.prodMk hsecond

/-- [definition] The complete constructed transition certificate for the four-chart complex
surface atlas.  Every field is instantiated below; none is an external smoothness hypothesis. -/
structure HolomorphicSurfaceAtlasCertificate where
  chart : SurfaceChart → Set Surface
  coordinateEquiv : (c : SurfaceChart) → { x : Surface // x ∈ chart c } ≃ ℂ × ℂ
  cover : ∀ x : Surface, ∃ c : SurfaceChart, x ∈ chart c
  transitionMap : SurfaceChart → SurfaceChart → (ℂ × ℂ → ℂ × ℂ)
  transition_commutes : ∀ (source target : SurfaceChart) (x : Surface)
    (hsource : x ∈ chart source) (htarget : x ∈ chart target),
      coordinateEquiv target ⟨x, htarget⟩ =
        transitionMap source target (coordinateEquiv source ⟨x, hsource⟩)
  transition_differentiable : ∀ (source target : SurfaceChart) (x : Surface)
    (hsource : x ∈ chart source) (htarget : x ∈ chart target),
      DifferentiableAt ℂ (transitionMap source target) (coordinateEquiv source ⟨x, hsource⟩)

/-- [proved-derived; formal-checked] The actual projective-line product carries the constructed
four-chart holomorphic transition certificate. -/
def projectiveLineProductHolomorphicAtlas : HolomorphicSurfaceAtlasCertificate where
  chart := fun c => { x | InSurfaceChart c x }
  coordinateEquiv := surfaceChartEquiv
  cover := surface_chart_cover
  transitionMap := surfaceTransition
  transition_commutes := surface_coordinate_transition
  transition_differentiable := by
    intro source target x hsource htarget
    exact surfaceTransition_differentiableAt source target
      (surfaceCoordinate source ⟨x, hsource⟩)
      (surface_overlap_admissible source target x hsource htarget)

section Audit

#print axioms coordinate_ne_zero_of_distinct_overlap
#print axioms coordinate_transition
#print axioms transition_differentiableAt
#print axioms transition_hasDerivAt_of_ne
#print axioms surface_coordinate_transition
#print axioms surfaceTransition_differentiableAt
#print axioms projectiveLineProductHolomorphicAtlas

end Audit

end Soma.Holonics.Millennium.HodgeProjectiveLineHolomorphicAtlas
