import ElementaryHolonics.Foundation.HolonTensorLens
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic

/-!
# The finite Copson--de Bruijn tail receiver

This file isolates the finite tail geometry from the de Bruijn--Newman heat-flow line.  Its
surface term is not a root mean square: the square root encloses the unnormalized tail energy,
while the inverse square-root weight depends on the one-based starting index of that tail.

The optimal infinite coefficient, the `ENNReal` limit, de Bruijn's recurrence characterization,
and a certified numerical enclosure remain later theorems.  No Galois, Riemann-hypothesis,
compression, or conservation conclusion is asserted here.
-/

noncomputable section

namespace Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

open Finset
open scoped BigOperators NNReal

/-- A finite nonnegative section of length `N`. -/
abbrev FiniteSection (N : ℕ) := Fin N → ℝ≥0

/-- The unnormalized square energy in the complete suffix beginning at `n`. -/
def tailEnergy {N : ℕ} (finite : FiniteSection N) (n : Fin N) : ℝ≥0 :=
  ∑ k ∈ Finset.Ici n, finite k ^ 2

/-- The additive mass on a finite section. -/
def mass {N : ℕ} (finite : FiniteSection N) : ℝ≥0 :=
  ∑ n, finite n

/-- The inverse square root of the one-based starting index. -/
def startingIndexWeight {N : ℕ} (n : Fin N) : ℝ≥0 :=
  (NNReal.sqrt (n.val + 1))⁻¹

/-- The square-root radius of the unnormalized tail energy. -/
def tailRadius {N : ℕ} (finite : FiniteSection N) (n : Fin N) : ℝ≥0 :=
  NNReal.sqrt (tailEnergy finite n)

/-!
The Copson--de Bruijn finite surface.  This is explicitly not an RMS: no tail cardinality divides
the energy under the square root.  The separate weight uses the tail's one-based starting index.
-/
def tailSurface {N : ℕ} (finite : FiniteSection N) : ℝ≥0 :=
  ∑ n, startingIndexWeight n * tailRadius finite n

/-- The complete finite face returned by the tail receiver. -/
structure FiniteTailFace (N : ℕ) where
  tailEnergy : Fin N → ℝ≥0
  mass : ℝ≥0
  tailSurface : ℝ≥0

/-- The finite returned face, retaining every suffix energy together with mass and surface. -/
def finiteTailFace {N : ℕ} (finite : FiniteSection N) : FiniteTailFace N where
  tailEnergy := tailEnergy finite
  mass := mass finite
  tailSurface := tailSurface finite

/-- The section-to-face occurrence passage underlying the finite tail receiver. -/
def finiteTailHolon (N : ℕ) :
    Holon (FiniteSection N) (FiniteTailFace N) (FiniteTailFace N) where
  Occurrence := FiniteSection N
  source finite := finite
  target finite := finiteTailFace finite
  receive finite := finiteTailFace finite

/-- Every finite section compatible with one returned tail face. -/
abbrev FiniteTailPreimage {N : ℕ} (face : FiniteTailFace N) : Type :=
  (finiteTailHolon N).PreimageFibre face

/-- A supplied section inhabits the preimage of the face it returns. -/
def finiteTailPreimageOfSection {N : ℕ} (finite : FiniteSection N) :
    FiniteTailPreimage (finiteTailFace finite) :=
  ⟨finite, rfl⟩

/-- The suffix energy starts with the current square and continues with the next suffix. -/
theorem tailEnergy_balance {N : ℕ} (finite : FiniteSection (N + 1)) (n : Fin N) :
    tailEnergy finite n.castSucc = finite n.castSucc ^ 2 + tailEnergy finite n.succ := by
  have htail : (Finset.Ici n.castSucc : Finset (Fin (N + 1))) =
      insert n.castSucc (Finset.Ici n.succ) := by
    ext k
    by_cases hk : k = n.castSucc
    · subst k
      simp
    · simp only [Finset.mem_Ici, Finset.mem_insert, hk, false_or]
      change n.val ≤ k.val ↔ n.val + 1 ≤ k.val
      have hval : k.val ≠ n.val := by
        intro same
        apply hk
        exact Fin.ext same
      omega
  rw [tailEnergy, tailEnergy, htail, Finset.sum_insert]
  simp

@[simp] theorem tailEnergy_zero {N : ℕ} (n : Fin N) :
    tailEnergy (0 : FiniteSection N) n = 0 := by
  simp [tailEnergy]

@[simp] theorem mass_zero (N : ℕ) :
    mass (0 : FiniteSection N) = 0 := by
  simp [mass]

@[simp] theorem tailRadius_zero {N : ℕ} (n : Fin N) :
    tailRadius (0 : FiniteSection N) n = 0 := by
  simp [tailRadius]

@[simp] theorem tailSurface_zero (N : ℕ) :
    tailSurface (0 : FiniteSection N) = 0 := by
  simp [tailSurface]

/-- Tail energy is homogeneous of degree two. -/
theorem tailEnergy_smul {N : ℕ} (scale : ℝ≥0)
    (finite : FiniteSection N) (n : Fin N) :
    tailEnergy (scale • finite) n = scale ^ 2 * tailEnergy finite n := by
  simp [tailEnergy, Finset.mul_sum, mul_pow]

/-- Additive mass is homogeneous of degree one. -/
theorem mass_smul {N : ℕ} (scale : ℝ≥0) (finite : FiniteSection N) :
    mass (scale • finite) = scale * mass finite := by
  simp [mass, Finset.mul_sum]

/-- Every unnormalized tail radius is homogeneous of degree one. -/
theorem tailRadius_smul {N : ℕ} (scale : ℝ≥0)
    (finite : FiniteSection N) (n : Fin N) :
    tailRadius (scale • finite) n = scale * tailRadius finite n := by
  rw [tailRadius, tailEnergy_smul, NNReal.sqrt_mul, NNReal.sqrt_sq]
  rfl

/-- The scale-weighted finite tail surface is homogeneous of degree one. -/
theorem tailSurface_smul {N : ℕ} (scale : ℝ≥0) (finite : FiniteSection N) :
    tailSurface (scale • finite) = scale * tailSurface finite := by
  unfold tailSurface
  simp_rw [tailRadius_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ac_rfl

end Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail

section Audit
open Soma.Holonics.Mathematics.CopsonDeBruijnFiniteTail
#print axioms tailEnergy_balance
#print axioms tailEnergy_smul
#print axioms mass_smul
#print axioms tailSurface_smul
#print axioms finiteTailHolon
end Audit
