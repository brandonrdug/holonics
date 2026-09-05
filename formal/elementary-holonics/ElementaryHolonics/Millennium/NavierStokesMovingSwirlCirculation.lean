import ElementaryHolonics.Millennium.NavierStokesSwirlCirculation

/-!
# Moving spacetime swirl circulation

This owner lifts the angular momentum identity to a time-dependent meridional chart.  The joint
spacetime derivative is split into its time port and the actual meridional trajectory port before
the existing spatial circulation identity is applied.  The axis remains explicit through the
factor `s`; no division by radius, viscosity, or solution existence is introduced.
-/

noncomputable section

open ContDiff Set

namespace Soma.Holonics.Millennium.NavierStokesMovingSwirlCirculation

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesSwirlCirculation

abbrev SpacetimeProfile := ℝ × (ℝ × ℝ) → ℝ

def timeDerivative (Omega : SpacetimeProfile) (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ Omega (t, p) (1, (0, 0))

def timeSlice (Omega : SpacetimeProfile) (t : ℝ) : MeridionalProfile :=
  fun p ↦ Omega (t, p)

def timeSliceV (V : ℝ → MeridionalProfile) (t : ℝ) : MeridionalProfile := V t

def timeSliceW (W : ℝ → MeridionalProfile) (t : ℝ) : MeridionalProfile := W t

/-- Joint angular momentum on spacetime, retaining the squared-radius factor on the axis. -/
def movingAngularMomentum (Omega : SpacetimeProfile)
    (q : ℝ × (ℝ × ℝ)) : ℝ := q.2.1 * Omega q

def movingSwirlResidual
    (Omega : SpacetimeProfile) (alpha beta : ℝ → ℝ)
    (V W : ℝ → MeridionalProfile) (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  timeDerivative Omega t p +
    swirlMomentum (alpha t) (beta t) (timeSliceV V t) (timeSlice Omega t)
      (timeSliceW W t) p

theorem timeSlice_differentiableAt
    (Omega : SpacetimeProfile) (t : ℝ) (p : ℝ × ℝ)
    (hOmega : DifferentiableAt ℝ Omega (t, p)) :
    DifferentiableAt ℝ (timeSlice Omega t) p := by
  exact hOmega.comp p ((hasFDerivAt_prodMk_right (𝕜 := ℝ) t p).differentiableAt)

theorem timeSlice_fderiv_apply
    (Omega : SpacetimeProfile) (t : ℝ) (p direction : ℝ × ℝ)
    (hOmega : DifferentiableAt ℝ Omega (t, p)) :
    fderiv ℝ (timeSlice Omega t) p direction =
      fderiv ℝ Omega (t, p) (0, direction) := by
  have h := hOmega.hasFDerivAt.comp p
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t p)
  have happ := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L direction) h.fderiv
  change fderiv ℝ (fun x : ℝ × ℝ => Omega (t, x)) p direction = _
  exact happ

theorem timeDerivative_plus_spatial_fderiv
    (Omega : SpacetimeProfile) (t : ℝ) (p direction : ℝ × ℝ)
    (hOmega : DifferentiableAt ℝ Omega (t, p)) :
    fderiv ℝ Omega (t, p) (1, direction) =
      timeDerivative Omega t p + fderiv ℝ (timeSlice Omega t) p direction := by
  have htime := timeDerivative Omega t p
  have hspace := timeSlice_fderiv_apply Omega t p direction hOmega
  calc
    fderiv ℝ Omega (t, p) (1, direction) =
        fderiv ℝ Omega (t, p) ((1, (0, 0)) + (0, direction)) := by
      congr 1
      simp
    _ = fderiv ℝ Omega (t, p) (1, (0, 0)) +
        fderiv ℝ Omega (t, p) (0, direction) := by rw [map_add]
    _ = timeDerivative Omega t p + fderiv ℝ (timeSlice Omega t) p direction := by
      rw [hspace]
      rfl

theorem hasDerivAt_movingAngularMomentum
    (Omega : SpacetimeProfile) (alpha beta : ℝ → ℝ)
    (V W : ℝ → MeridionalProfile) (trajectory : ℝ → ℝ × ℝ) (t : ℝ)
    (hOmega : DifferentiableAt ℝ Omega (t, trajectory t))
    (htrajectory : HasDerivAt trajectory
      (meridionalDrift (beta t) (timeSliceV V t) (timeSliceW W t) (trajectory t)) t) :
    HasDerivAt (fun τ ↦ (trajectory τ).1 * Omega (τ, trajectory τ))
      ((trajectory t).1 *
          (timeDerivative Omega t (trajectory t) +
            swirlMomentum (alpha t) (beta t) (timeSliceV V t) (timeSlice Omega t)
              (timeSliceW W t) (trajectory t)) -
        (alpha t - beta t) *
          ((trajectory t).1 * Omega (t, trajectory t))) t := by
  let drift := meridionalDrift (beta t) (timeSliceV V t) (timeSliceW W t) (trajectory t)
  have hslice := timeSlice_differentiableAt Omega t (trajectory t) hOmega
  have hangular := angularMomentum_fderiv_apply (alpha t) (beta t)
    (timeSliceV V t) (timeSlice Omega t) (timeSliceW W t) (trajectory t) hslice
  have hpath : HasDerivAt (fun τ ↦ (τ, trajectory τ))
      (1, meridionalDrift (beta t) (timeSliceV V t) (timeSliceW W t) (trajectory t)) t := by
    have h₁ := (hasDerivAt_id' t).hasFDerivAt
    have h₂ := htrajectory.hasFDerivAt
    have h := h₁.prodMk h₂
    simpa [Function.comp_def] using h.hasDerivAt
  have hjoint := hOmega.hasFDerivAt.comp_hasDerivAt t hpath
  have hsplit := timeDerivative_plus_spatial_fderiv Omega t (trajectory t) drift hOmega
  have hradial := (hasFDerivAt_fst (𝕜 := ℝ) (p := trajectory t)).comp_hasDerivAt t
    htrajectory
  have hradial' : HasDerivAt (fun τ ↦ (trajectory τ).1) drift.1 t := by
    simpa [Function.comp_def, drift] using hradial
  have hjoint' : HasDerivAt (fun τ ↦ Omega (τ, trajectory τ))
      (fderiv ℝ Omega (t, trajectory t) (1, drift)) t := by
    simpa [Function.comp_def] using hjoint
  have hproduct := hradial'.mul hjoint'
  have hsliceProduct := (hasFDerivAt_fst (𝕜 := ℝ) (p := trajectory t)).mul
    hslice.hasFDerivAt
  have hangular' := hangular
  rw [show angularMomentum (timeSlice Omega t) =
      (fun q : ℝ × ℝ ↦ q.1) * timeSlice Omega t by rfl,
    hsliceProduct.fderiv] at hangular'
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply] at hangular'
  have hderivEq :
      drift.1 * Omega (t, trajectory t) + (trajectory t).1 *
          fderiv ℝ Omega (t, trajectory t) (1, drift) =
        (trajectory t).1 *
            (timeDerivative Omega t (trajectory t) +
              swirlMomentum (alpha t) (beta t) (timeSliceV V t) (timeSlice Omega t)
                (timeSliceW W t) (trajectory t)) -
          (alpha t - beta t) * ((trajectory t).1 * Omega (t, trajectory t)) := by
    rw [hsplit]
    dsimp [angularMomentum, timeSlice, drift, timeSliceV, timeSliceW] at hangular'
    dsimp [drift, timeSliceV, timeSliceW]
    linear_combination hangular'
  have hproduct' := hproduct
  rw [hderivEq] at hproduct'
  change HasDerivAt (fun τ ↦ (trajectory τ).1 * Omega (τ, trajectory τ)) _ t at hproduct'
  exact hproduct'

theorem movingSwirlResidual_source_identity
    (Omega : SpacetimeProfile) (alpha beta : ℝ → ℝ)
    (V W : ℝ → MeridionalProfile) (t : ℝ) (p : ℝ × ℝ) :
    movingSwirlResidual Omega alpha beta V W t p =
      timeDerivative Omega t p +
        swirlMomentum (alpha t) (beta t) (timeSliceV V t) (timeSlice Omega t)
          (timeSliceW W t) p := rfl

#print axioms timeSlice_differentiableAt
#print axioms timeSlice_fderiv_apply
#print axioms timeDerivative_plus_spatial_fderiv
#print axioms hasDerivAt_movingAngularMomentum
#print axioms movingSwirlResidual_source_identity

end Soma.Holonics.Millennium.NavierStokesMovingSwirlCirculation
