import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.RingTheory.TensorProduct.Quotient
import Mathlib.RingTheory.Length

/-! The degree-zero derived tensor face is the actual mapped-ideal quotient.
This joins the native right-exact derived-functor comparison to the native
algebra tensor quotient, with all scalars restricted to the acting ring.
Higher Tor vanishing is a separate obligation, supplied by a regular
scalar resolution in the consuming graph comparison.

agent-inferred: keep this native comparison separate from regularity so
that no regularity-under-arbitrary-pullback premise enters the consumer.
The external helical pair receiver touches faces and placement, cell
holonomy and tube; helix, pair and tower thread remain attached. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false
open CategoryTheory CategoryTheory.MonoidalCategory
namespace Holonics.Hodge.CMGraphSource
universe u

def cartierTorZeroQuotientIso (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) :
    (((Tor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B)).obj
      (ModuleCat.of A (A ⧸ I))) ≅
        ModuleCat.of A (B ⧸ I.map (algebraMap A B)) :=
  (Functor.leftDerivedZeroIsoSelf
      ((tensoringLeft (ModuleCat.{u} A)).obj (ModuleCat.of A B))).app
        (ModuleCat.of A (A ⧸ I)) ≪≫
    (((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B I).toLinearEquiv.restrictScalars
      A).symm.toModuleIso)

theorem cartierTorZeroQuotient_length (A B : Type u) [CommRing A] [CommRing B]
    [Algebra A B] (I : Ideal A) :
    Module.length A (((Tor (ModuleCat.{u} A) 0).obj (ModuleCat.of A B)).obj
      (ModuleCat.of A (A ⧸ I))) =
        Module.length A (B ⧸ I.map (algebraMap A B)) :=
  (cartierTorZeroQuotientIso A B I).toLinearEquiv.length_eq

#print axioms cartierTorZeroQuotientIso
#print axioms cartierTorZeroQuotient_length
end Holonics.Hodge.CMGraphSource
