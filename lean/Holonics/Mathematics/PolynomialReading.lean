import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Cast.CharZero

/-!
# Exact rational polynomial readings at rational and real faces

[agent-inferred] The Ratio object's selected-root arithmetic and the existing
Sturm instrument use the same coefficient reading. The three declaration
bodies moved unchanged from `HolonicsResearch/Mathematics/Sturm.lean`; their
public `Holonics.Mathematics.Sturm` names remain unchanged. This owner does not
count roots or interpret a Sturm isolation certificate.
-/
namespace Holonics.Mathematics.Sturm

def evalAt (x : ℚ) : List ℚ → ℚ
  | [] => 0
  | c :: p => c + x * evalAt x p

noncomputable def evalReal (x : ℝ) : List ℚ → ℝ
  | [] => 0
  | c :: p => (c : ℝ) + x * evalReal x p

theorem theRationalReadingCastsToTheRealReading (x : ℚ) :
    ∀ p : List ℚ, ((evalAt x p : ℚ) : ℝ) = evalReal (x : ℝ) p := by
  intro p
  induction p with
  | nil => simp [evalAt, evalReal]
  | cons c p ih => simp [evalAt, evalReal, ih]

#print axioms theRationalReadingCastsToTheRealReading
end Holonics.Mathematics.Sturm
