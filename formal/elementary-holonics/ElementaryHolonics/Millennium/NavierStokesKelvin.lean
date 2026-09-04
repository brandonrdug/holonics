import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.MeasureTheory.Integral.CurveIntegral.Basic
import ElementaryHolonics.Millennium.NavierStokes

/-!
# Kelvin circulation on genuine closed paths

This module complements the finite material-polygon receiver with Mathlib's actual curve integral.
A velocity field becomes a spatial one-form through the real inner product, a time-indexed closed
path returns its circulation, and a `KelvinCertificate` turns vanishing circulation derivative on
the nonnegative time half-line into global constancy there.

`CurveCirculationBalance` retains a source term before selecting the Kelvin zero-source fibre.  The
next analytic deed is to derive that source from the Navier--Stokes momentum equation and a smooth
material-loop transport theorem.
-/

noncomputable section

open Set

namespace Soma.Holonics.Millennium.NavierStokesKelvin

open Soma.Holonics.Millennium.NavierStokes

/-- The velocity one-form at a fixed time, obtained by lowering the velocity with the Euclidean
inner product. -/
def velocityOneForm (velocity : VelocityField) (t : ℝ) : Space → Space →L[ℝ] ℝ :=
  fun x ↦ innerSL ℝ (velocity x t)

/-- The curve-integral circulation of a time-indexed closed path.  A corresponding
`VelocityKelvinCertificate` retains the `CurveIntegrable` witness which makes this totalized
integral an admitted circulation at every receiver time. -/
def curveCirculation (velocity : VelocityField) (base : ℝ → Space)
    (loop : ∀ t, Path (base t) (base t)) (t : ℝ) : ℝ :=
  ∫ᶜ x in loop t, velocityOneForm velocity t x

/-- A circulation whose derivative vanishes on oriented nonnegative time. -/
structure KelvinCertificate (circulation : ℝ → ℝ) : Prop where
  differentiable : DifferentiableOn ℝ circulation (Ici 0)
  derivative_zero : ∀ t ∈ Ici (0 : ℝ), derivWithin circulation (Ici 0) t = 0

/-- **Kelvin constancy from the zero derivative.**  Every pair of nonnegative receiver times reads
the same certified circulation. -/
theorem KelvinCertificate.eq_of_nonnegative
    {circulation : ℝ → ℝ} (certificate : KelvinCertificate circulation)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    circulation s = circulation t := by
  apply (convex_Ici (0 : ℝ)).is_const_of_fderivWithin_eq_zero certificate.differentiable
  · intro x hx
    rw [← toSpanSingleton_derivWithin, certificate.derivative_zero x hx]
    simp
  · exact hs
  · exact ht

/-- A differentiable circulation with a retained source/flux face. -/
structure CurveCirculationBalance (circulation source : ℝ → ℝ) : Prop where
  differentiable : DifferentiableOn ℝ circulation (Ici 0)
  balance : ∀ t ∈ Ici (0 : ℝ), derivWithin circulation (Ici 0) t = source t

/-- A zero source turns the full circulation balance into a Kelvin certificate. -/
def CurveCirculationBalance.kelvinCertificate
    {circulation source : ℝ → ℝ}
    (balance : CurveCirculationBalance circulation source)
    (hsource : ∀ t ∈ Ici (0 : ℝ), source t = 0) : KelvinCertificate circulation where
  differentiable := balance.differentiable
  derivative_zero t ht := by rw [balance.balance t ht, hsource t ht]

/-- **Kelvin theorem on the zero-source fibre of a curve-circulation balance.** -/
theorem CurveCirculationBalance.kelvin
    {circulation source : ℝ → ℝ}
    (balance : CurveCirculationBalance circulation source)
    (hsource : ∀ t ∈ Ici (0 : ℝ), source t = 0)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    circulation s = circulation t :=
  (balance.kelvinCertificate hsource).eq_of_nonnegative hs ht

/-- A Kelvin certificate specialized to an admitted curve-integral receiver of a velocity field.
The integrability field prevents Mathlib's totalized curve integral from silently reading a
non-integrable occurrence as zero. -/
structure VelocityKelvinCertificate (velocity : VelocityField) (base : ℝ → Space)
    (loop : ∀ t, Path (base t) (base t)) : Prop where
  certificate : KelvinCertificate (curveCirculation velocity base loop)
  curveIntegrable : ∀ t ∈ Ici (0 : ℝ),
    CurveIntegrable (velocityOneForm velocity t) (loop t)

/-- The specialized curve-integral conclusion. -/
theorem VelocityKelvinCertificate.curveCirculation_eq
    {velocity : VelocityField} {base : ℝ → Space}
    {loop : ∀ t, Path (base t) (base t)}
    (certificate : VelocityKelvinCertificate velocity base loop)
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    curveCirculation velocity base loop s = curveCirculation velocity base loop t :=
  certificate.certificate.eq_of_nonnegative hs ht

section Audit

#print axioms KelvinCertificate.eq_of_nonnegative
#print axioms CurveCirculationBalance.kelvin
#print axioms VelocityKelvinCertificate.curveCirculation_eq

end Audit

end Soma.Holonics.Millennium.NavierStokesKelvin
