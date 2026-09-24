import ElementaryHolonics.Millennium.Ellipse
import ElementaryHolonics.Millennium.NavierStokesMaterialPolygon
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The mass shell is the Pythagorean face of the Lorentz law of cosines

The complete relativistic mass--energy relation `E² = (pc)² + (m₀c²)²` is not a separate law.
It is the reading of one symmetric bilinear form, the Lorentz pairing
`⟪P, Q⟫ = E_P E_Q − c² p_P · p_Q`, on the diagonal, and it takes the Pythagorean shape because
the time face `(E, 0)` and the space face `(0, p)` are Lorentz-orthogonal.  The general law is the
polarization identity `⟪P+Q, P+Q⟫ = ⟪P,P⟫ + ⟪Q,Q⟫ + 2⟪P,Q⟫`, whose cross term is the grip
(`TABLET_THE_TURN`: aim = cosine); the mass shell is its `cos θ = 0` specialization exactly as the
2026-07-16 triangle record states for the Euclidean face.

The Einstein coupling `8π` is read here in its two chart expansions.  `2 · (4π)` is the
half-density times the solid angle of the sphere chart (`Ellipse.theEightPiFactors`);
`2² · (2π)` is the dyadic fork depth of `refineForkCoupling 2 0 = 4 · arc/differential` times the
circle chart constant that the Navier--Stokes exterior face carries as `2π · G(N)`.  Both are
exact product expansions of one integer face `2³` and one circle constraint.

No physical constant is asserted; `c` and `m₀` are declared scalars.
-/

noncomputable section

open Finset

namespace Soma.Holonics.Millennium.HolonicMassShellFace

/-- A four-momentum: one energy face and three momentum coordinates. -/
@[ext] structure FourMomentum where
  energy : ℝ
  momentum : Fin 3 → ℝ

namespace FourMomentum

instance : Add FourMomentum := ⟨fun P Q => ⟨P.energy + Q.energy, P.momentum + Q.momentum⟩⟩

@[simp] theorem add_energy (P Q : FourMomentum) : (P + Q).energy = P.energy + Q.energy := rfl
@[simp] theorem add_momentum (P Q : FourMomentum) : (P + Q).momentum = P.momentum + Q.momentum :=
  rfl

/-- The time face of a four-momentum. -/
def timeFace (P : FourMomentum) : FourMomentum := ⟨P.energy, 0⟩

/-- The space face of a four-momentum. -/
def spaceFace (P : FourMomentum) : FourMomentum := ⟨0, P.momentum⟩

theorem timeFace_add_spaceFace (P : FourMomentum) : P.timeFace + P.spaceFace = P := by
  ext <;> simp [timeFace, spaceFace]

end FourMomentum

/-- The Lorentz pairing at light speed `c`: `E_P E_Q − c² p_P · p_Q`. -/
def lorentzPairing (c : ℝ) (P Q : FourMomentum) : ℝ :=
  P.energy * Q.energy - c ^ 2 * ∑ i, P.momentum i * Q.momentum i

theorem lorentzPairing_comm (c : ℝ) (P Q : FourMomentum) :
    lorentzPairing c P Q = lorentzPairing c Q P := by
  unfold lorentzPairing
  simp_rw [mul_comm P.energy, mul_comm (P.momentum _)]

/-- **The Lorentz law of cosines.**  The diagonal reading of a sum is the two diagonal readings
plus twice the grip. -/
theorem lorentzPairing_add_add (c : ℝ) (P Q : FourMomentum) :
    lorentzPairing c (P + Q) (P + Q) =
      lorentzPairing c P P + lorentzPairing c Q Q + 2 * lorentzPairing c P Q := by
  unfold lorentzPairing
  simp only [FourMomentum.add_energy, FourMomentum.add_momentum, Pi.add_apply]
  have : ∑ i, (P.momentum i + Q.momentum i) * (P.momentum i + Q.momentum i) =
      ∑ i, P.momentum i * P.momentum i + ∑ i, Q.momentum i * Q.momentum i +
        2 * ∑ i, P.momentum i * Q.momentum i := by
    rw [mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => by ring
  rw [this]; ring

/-- The time face and the space face are Lorentz-orthogonal: the grip vanishes. -/
theorem lorentzPairing_timeFace_spaceFace (c : ℝ) (P : FourMomentum) :
    lorentzPairing c P.timeFace P.spaceFace = 0 := by
  simp [lorentzPairing, FourMomentum.timeFace, FourMomentum.spaceFace]

/-- The squared spatial momentum. -/
def momentumSquare (P : FourMomentum) : ℝ := ∑ i, P.momentum i * P.momentum i

/-- **The mass shell is the Pythagorean face.**  Because the two faces are orthogonal, the diagonal
reading is `E² − c²|p|²`, and the mass-shell condition `⟪P,P⟫ = (m₀c²)²` is exactly
`E² = (|p|c)² + (m₀c²)²`. -/
theorem lorentzPairing_self (c : ℝ) (P : FourMomentum) :
    lorentzPairing c P P = P.energy ^ 2 - c ^ 2 * momentumSquare P := by
  unfold lorentzPairing momentumSquare; ring

theorem massShell_iff (c m₀ : ℝ) (P : FourMomentum) :
    lorentzPairing c P P = (m₀ * c ^ 2) ^ 2 ↔
      P.energy ^ 2 = c ^ 2 * momentumSquare P + (m₀ * c ^ 2) ^ 2 := by
  rw [lorentzPairing_self]
  constructor <;> intro h <;> linarith

/-- The Pythagorean shape is the law of cosines evaluated on the orthogonal split. -/
theorem lorentzPairing_self_eq_faces (c : ℝ) (P : FourMomentum) :
    lorentzPairing c P P =
      lorentzPairing c P.timeFace P.timeFace + lorentzPairing c P.spaceFace P.spaceFace := by
  conv_lhs => rw [← P.timeFace_add_spaceFace]
  rw [lorentzPairing_add_add, lorentzPairing_timeFace_spaceFace, mul_zero, add_zero]

/-- A dust-style algebraic face reading: density times the diagonal Lorentz reading of the carrier
momentum. On the mass shell it is exactly `density * (m₀ * c ^ 2) ^ 2`;
this scalar identity alone does not constitute a physical stress-energy measurement. -/
def dustFaceReading (c density : ℝ) (P : FourMomentum) : ℝ := density * lorentzPairing c P P

theorem dustFaceReading_massShell (c m₀ density : ℝ) (P : FourMomentum)
    (hshell : lorentzPairing c P P = (m₀ * c ^ 2) ^ 2) :
    dustFaceReading c density P = density * (m₀ * c ^ 2) ^ 2 := by
  unfold dustFaceReading; rw [hshell]

/-- The two chart expansions of the Einstein coupling: the sphere chart `2 · (4π)` and the
circle chart `2² · (2π)`.  Both carry the integer face `2³` and one circle constraint. -/
theorem eightPi_chart_expansions :
    (8 : ℝ) * Real.pi = 2 * (4 * Real.pi) ∧ (8 : ℝ) * Real.pi = 2 ^ 2 * (2 * Real.pi) :=
  ⟨Ellipse.theEightPiFactors, by ring⟩

/-- The circle-chart integer face is the dyadic fork depth of the calibrated coupling. -/
theorem fourArcOverDifferential_eq_forkDepth (arc differential : ℝ) (h : differential ≠ 0) :
    NavierStokesMaterialPolygon.refineForkCoupling 2 0 arc differential = 2 ^ 2 * (arc / differential) := by
  rw [NavierStokesMaterialPolygon.refineForkCoupling_two_zero arc differential h]; norm_num

section Audit

#print axioms lorentzPairing_add_add
#print axioms massShell_iff
#print axioms lorentzPairing_self_eq_faces
#print axioms dustFaceReading_massShell
#print axioms eightPi_chart_expansions
#print axioms fourArcOverDifferential_eq_forkDepth

end Audit

end Soma.Holonics.Millennium.HolonicMassShellFace
