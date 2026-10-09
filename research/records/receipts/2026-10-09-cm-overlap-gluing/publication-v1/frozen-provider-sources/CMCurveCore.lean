import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.NormNum

/-! The shared nonsingular Weierstrass source, without affine point/class-group imports. -/

noncomputable section

namespace Holonics.Hodge.CMGraphSource

/-- The nonsingular short Weierstrass model v^2=u^3-u. -/
def squareCurve : WeierstrassCurve ℂ := ⟨0, 0, 0, -1, 0⟩

theorem squareCurve_discriminant : squareCurve.Δ = 64 := by
  norm_num [squareCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

instance : squareCurve.IsElliptic := ⟨by
  rw [squareCurve_discriminant]
  exact isUnit_iff_ne_zero.mpr (by norm_num)⟩

#print axioms squareCurve_discriminant

end Holonics.Hodge.CMGraphSource
