/-
Source candidate only. This file was not compiled, per the worker boundary.

It is intended to be included from a Hodge research module after the imports listed in
SOURCE_NOTES.md. The proof is written against the installed Mathlib API, but its elaboration
and the tensorized homology join remain unchecked.
-/
import Mathlib.CategoryTheory.Monoidal.Tor
import Mathlib.Algebra.Regular.SMul
import Mathlib.RingTheory.Regular.Category
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.Abelian.Projective.Resolution

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option Elab.async false

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped TensorProduct ZeroObject

namespace Holonics.Hodge.CMGraphSource

universe u

variable (A : Type u) [CommRing A] (d : A)


private def resolutionX (A : Type u) [CommRing A] (n : ℕ) : ModuleCat.{u} A :=
  match n with
  | 0 => ModuleCat.of A A
  | 1 => ModuleCat.of A A
  | _ => 0

private def resolutionD (A : Type u) [CommRing A] (d : A) :
    ∀ n : ℕ, resolutionX A (n + 1) ⟶ resolutionX A n := by
  intro n
  cases n with
  | zero => exact (ModuleCat.smulShortComplex (ModuleCat.of A A) d).f
  | succ n => exact 0

private def resolutionComplex : ChainComplex (ModuleCat.{u} A) ℕ :=
  ChainComplex.of (resolutionX A) (resolutionD A d) (by
    intro n
    cases n with
    | zero => simp [resolutionD]
    | succ n => simp [resolutionD])

private theorem resolutionComplex_d10 :
    (resolutionComplex A d).d 1 0 =
      (ModuleCat.smulShortComplex (ModuleCat.of A A) d).f := by
  change ChainComplex.of.d (resolutionX A) (resolutionD A d) (0 + 1) 0 = _
  rw [ChainComplex.of_d]
  rfl

private theorem resolutionComplex_d21 : (resolutionComplex A d).d 2 1 = 0 := by
  change ChainComplex.of.d (resolutionX A) (resolutionD A d) (1 + 1) 1 = _
  rw [ChainComplex.of_d]
  rfl

private theorem resolutionComplex_d00 : (resolutionComplex A d).d 0 0 = 0 := by
  exact ChainComplex.of_d_ne (resolutionX A) (resolutionD A d) (by decide)

private def quotientAugmentation :
    resolutionComplex A d ⟶
      (ChainComplex.single₀ (ModuleCat.{u} A)).obj (ModuleCat.of A (QuotSMulTop d A)) := by
  let S := ModuleCat.smulShortComplex (ModuleCat.of A A) d
  exact (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨S.g, by
      rw [resolutionComplex_d10]
      exact S.zero⟩

/-- The scalar two-term projective resolution of the native scalar quotient. -/
def scalarQuotientResolution (hd : IsRegular d) :
    ProjectiveResolution (ModuleCat.of A (QuotSMulTop d A)) := by
  let S := ModuleCat.smulShortComplex (ModuleCat.of A A) d
  let hdA : IsSMulRegular A d := hd.left.isSMulRegular
  let hS : S.ShortExact := hdA.smulShortComplex_shortExact
  refine
    { complex := resolutionComplex A d
      projective := ?_
      π := quotientAugmentation A d
      quasiIso := ?_ }
  · intro n
    cases n with
    | zero =>
        change Projective (ModuleCat.of A A)
        exact ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of A A)
    | succ n => cases n with
      | zero =>
          change Projective (ModuleCat.of A A)
          exact ModuleCat.projective_of_categoryTheory_projective (ModuleCat.of A A)
      | succ n => exact IsZero.projective (isZero_zero (ModuleCat.{u} A))
  · refine ⟨fun n => ?_⟩
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · change (ShortComplex.mk ((resolutionComplex A d).d 1 0)
            ((quotientAugmentation A d).f 0) _).Exact ∧
          Epi ((quotientAugmentation A d).f 0)
        refine (ShortComplex.exact_and_epi_g_iff_of_iso ?_).2
          ⟨hS.exact, inferInstance⟩
        exact ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
          (by
            simp only [Iso.refl_hom, Category.id_comp, Category.comp_id,
              resolutionComplex_d10]
            rfl)
          (by
            simp [quotientAugmentation]
            rfl)
      · exact resolutionComplex_d00 A d
      · rfl
      · rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · cases n with
        | zero =>
          rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
          apply (ShortComplex.exact_iff_mono _ (resolutionComplex_d21 A d)).2
          change Mono ((resolutionComplex A d).d 1 0)
          rw [resolutionComplex_d10]
          exact hS.mono_f
        | succ n =>
          rw [HomologicalComplex.exactAt_iff' _ (n + 3) (n + 2) (n + 1) (by simp) (by simp)]
          apply ShortComplex.exact_of_isZero_X₂
          exact isZero_zero (ModuleCat.{u} A)
      · exact ChainComplex.exactAt_succ_single_obj _ _

/-- Higher Tor vanishing for a scalar quotient, computed from the explicit resolution. -/
theorem higherTorScalarQuotient_isZero
    (M : Type u) [AddCommGroup M] [Module A M]
    (hd : IsRegular d) (hM : IsSMulRegular M d) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A (QuotSMulTop d A))) := by
  let P := scalarQuotientResolution A d hd
  let F := (tensoringLeft (ModuleCat.{u} A)).obj (ModuleCat.of A M)
  let T := (F.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex
  have hregTensor : IsSMulRegular (M ⊗[A] A) d :=
    (TensorProduct.rid A M).isSMulRegular_congr d |>.mpr hM
  have hmono : Mono (T.d 1 0) := by
    change Mono (F.map (d • 𝟙 (ModuleCat.of A A)))
    rw [CategoryTheory.Functor.map_smul, F.map_id]
    rw [ModuleCat.mono_iff_injective]
    exact hregTensor
  have hExact : ∀ k : ℕ, T.ExactAt (k + 1) := by
    intro k
    cases k with
    | zero =>
      rw [HomologicalComplex.exactAt_iff' _ 2 1 0 (by simp) (by simp)]
      have hf : T.d 2 1 = 0 := by
        change F.map ((resolutionComplex A d).d 2 1) = 0
        rw [resolutionComplex_d21, F.map_zero]
      apply (ShortComplex.exact_iff_mono _ hf).2
      exact hmono
    | succ k =>
      rw [HomologicalComplex.exactAt_iff' _ (k + 3) (k + 2) (k + 1) (by simp) (by simp)]
      apply ShortComplex.exact_of_isZero_X₂
      change IsZero (F.obj (resolutionX A (k + 2)))
      exact Functor.map_isZero F (isZero_zero (ModuleCat.{u} A))
  have hzero : IsZero (T.homology (n + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact hExact n
  change IsZero ((F.leftDerived (n + 1)).obj (ModuleCat.of A (QuotSMulTop d A)))
  exact IsZero.of_iso hzero (P.isoLeftDerivedObj F (n + 1))

/-- The higher-Tor vanishing with the conventional principal ideal quotient as target. -/
theorem higherTorIdealQuotient_isZero
    (M : Type u) [AddCommGroup M] [Module A M]
    (hd : IsRegular d) (hM : IsSMulRegular M d) (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} A) (n + 1)).obj (ModuleCat.of A M)).obj
      (ModuleCat.of A (A ⧸ Ideal.span {d}))) := by
  let e : ModuleCat.of A (QuotSMulTop d A) ≅
      ModuleCat.of A (A ⧸ Ideal.span {d}) :=
    (QuotSMulTop.equivTensorQuot d A ≪≫ₗ
      TensorProduct.lid A (A ⧸ Ideal.span {d})).toModuleIso
  exact IsZero.of_iso (higherTorScalarQuotient_isZero A d M hd hM n)
    (((Tor (ModuleCat.{u} A) (n + 1)).obj (ModuleCat.of A M)).mapIso e).symm

#print axioms scalarQuotientResolution
#print axioms higherTorScalarQuotient_isZero
#print axioms higherTorIdealQuotient_isZero

end Holonics.Hodge.CMGraphSource
