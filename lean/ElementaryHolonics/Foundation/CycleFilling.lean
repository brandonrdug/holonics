import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Exact cycle fillings

A homology-vanishing assertion forgets the current which realizes the vanishing.  This owner keeps
that current: every cycle in one addressed degree is sent linearly to a filler one degree above,
and the filler boundary returns the original cycle exactly.  It is the minimal constructive input
needed to annihilate homology in that degree; a chain contraction or chain-homotopy equivalence is
strictly stronger data.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Soma.Holonics.Foundation

universe u

variable {R : Type u} [CommRing R]

/-- [definition] A source-retaining linear filler for every cycle in one degree of a chain
complex. -/
structure CycleFilling (K : ChainComplex (ModuleCat R) ℕ) (degree : ℕ) where
  fill : K.cycles degree ⟶ K.X (degree + 1)
  boundary_fill : fill ≫ K.d (degree + 1) degree = K.iCycles degree

namespace CycleFilling

variable {K : ChainComplex (ModuleCat R) ℕ} {degree : ℕ}

/-- [proved-derived; formal-checked] A retained filler makes the complex exact in its addressed
degree. -/
theorem exactAt (filling : CycleFilling K degree) : K.ExactAt degree := by
  let splitToCycles : SplitEpi (K.toCycles (degree + 1) degree) :=
    { section_ := filling.fill
      id := by
        rw [← cancel_mono (K.iCycles degree), Category.assoc, K.toCycles_i,
          filling.boundary_fill, Category.id_comp] }
  rw [K.exactAt_iff' (degree + 1) degree ((ComplexShape.down ℕ).next degree)
      (ChainComplex.prev ℕ degree) rfl,
    ShortComplex.exact_iff_epi_toCycles,
    ← K.toCycles_cyclesIsoSc'_hom (degree + 1) degree
      ((ComplexShape.down ℕ).next degree) (ChainComplex.prev ℕ degree) rfl]
  exact
    (splitToCycles.comp
      { section_ :=
          (K.cyclesIsoSc' (degree + 1) degree ((ComplexShape.down ℕ).next degree)
            (ChainComplex.prev ℕ degree) rfl).inv }).epi

/-- [proved-derived; formal-checked] An exact cycle-filling current annihilates the corresponding
homology receiver. -/
theorem homologyIsZero (filling : CycleFilling K degree) :
    IsZero (K.homology degree) :=
  filling.exactAt.isZero_homology

section Audit

#print axioms CycleFilling.exactAt
#print axioms CycleFilling.homologyIsZero

end Audit

end CycleFilling

end Soma.Holonics.Foundation
