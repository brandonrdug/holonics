/-
Source-only generic chart naturality for an equation section. No Lean process was run
under the worker boundary; the proof is an uncompiled candidate against the inspected
Mathlib owners.
-/
import CMResidueStalkBridge

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry

namespace Holonics.Hodge.CMGraphSource

universe u

variable {X Y : Scheme.{u}} {R S : CommRingCat.{u}}
  (jR : Spec R ⟶ X) [IsOpenImmersion jR]
  (jS : Spec S ⟶ Y) [IsOpenImmersion jS]
  (φ : CommRingCat.of S ⟶ R) (f : X ⟶ Y)

private def spectrumImagePoint (x : Spec R) : Spec S := Spec.map φ x

omit [IsOpenImmersion jR] [IsOpenImmersion jS] in
private theorem spectrumImagePoint_eq
    (hs : Spec.map φ ≫ jS = jR ≫ f) (x : Spec R) :
    jS (spectrumImagePoint φ x) = f (jR x) := by
  have h := congrArg (fun g : Spec R ⟶ Y => g x) hs
  change jS (spectrumImagePoint φ x) = f (jR x) at h
  exact h

/-- The image section of `s` read in the ambient `Y` stalk at the point transported by `hs`. -/
def spectrumImageAmbientGerm
    (hs : Spec.map φ ≫ jS = jR ≫ f) (x : Spec R) (s : S) :
    Y.presheaf.stalk (f (jR x)) :=
  Y.presheaf.germ (jS ''ᵁ ⊤) (f (jR x))
    ⟨spectrumImagePoint φ x, trivial, spectrumImagePoint_eq jR jS φ f hs x⟩
    (spectrumImageEquation S jS s)

/-- The image section on the `R` chart, read in the ambient `X` stalk. -/
def spectrumImageChartGerm (x : Spec R) (s : S) : X.presheaf.stalk (jR x) :=
  X.presheaf.germ (jR ''ᵁ ⊤) (jR x) ⟨x, trivial, rfl⟩
    (spectrumImageEquation R jR (φ.hom s))

/-- Pulling the ambient equation germ back through the actual chart map gives the chart
equation germ. This is the stalk-level naturality square; no equality of stalk quotients
is assumed. -/
theorem spectrumImage_stalkMap_naturality
    (hs : Spec.map φ ≫ jS = jR ≫ f) (x : Spec R) (s : S) :
    (f.stalkMap (jR x)).hom (spectrumImageAmbientGerm jR jS φ f hs x s) =
      spectrumImageChartGerm jR φ x s := by
  let q := spectrumImagePoint φ x
  let y := jR x
  let z := f y
  have hp : jS q = z := by
    exact spectrumImagePoint_eq jR jS φ f hs x
  have hq : jS q ∈ jS ''ᵁ ⊤ := ⟨q, trivial, rfl⟩
  have hz : z ∈ jS ''ᵁ ⊤ := ⟨q, trivial, hp⟩
  let pre : CommRingCat.of S ⟶ Y.presheaf.stalk (jS q) :=
    (Scheme.ΓSpecIso S).inv ≫ (jS.appIso ⊤).inv ≫
      Y.presheaf.germ (jS ''ᵁ ⊤) (jS q) hq
  let pointIso := Y.presheaf.stalkCongr (.of_eq hp)
  have htransport :
      Y.presheaf.germ (jS ''ᵁ ⊤) (jS q) hq ≫ pointIso.hom =
        Y.presheaf.germ (jS ''ᵁ ⊤) z hz := by
    simp only [pointIso, TopCat.Presheaf.stalkCongr_hom,
      TopCat.Presheaf.germ_stalkSpecializes]
  have hmaps :
      jS.stalkMap q ≫ (Spec.map φ).stalkMap x =
        pointIso.hom ≫ f.stalkMap y ≫ jR.stalkMap x := by
    simpa only [Scheme.Hom.stalkMap_comp, pointIso, y, q, z,
      spectrumImagePoint, Scheme.Hom.comp_apply] using
      (Scheme.Hom.stalkMap_congr_hom (Spec.map φ ≫ jS) (jR ≫ f) hs x)
  have hpre : pre ≫ jS.stalkMap q = StructureSheaf.toStalk S q := by
    dsimp only [pre]
    simp only [Category.assoc, spectrumImage_germ_stalkMap]
    rfl
  have hcomposed :
      (Scheme.ΓSpecIso S).inv ≫ (jS.appIso ⊤).inv ≫
        Y.presheaf.germ (jS ''ᵁ ⊤) z hz ≫ f.stalkMap y ≫ jR.stalkMap x =
          φ ≫ StructureSheaf.toStalk R x := by
    calc
      _ = pre ≫ pointIso.hom ≫ f.stalkMap y ≫ jR.stalkMap x := by
        dsimp only [pre]
        rw [← htransport]
        simp only [Category.assoc]
      _ = pre ≫ jS.stalkMap q ≫ (Spec.map φ).stalkMap x := by
        rw [hmaps]
      _ = StructureSheaf.toStalk S q ≫ (Spec.map φ).stalkMap x := by
        rw [← Category.assoc, hpre]
      _ = φ ≫ StructureSheaf.toStalk R x := by
        exact AlgebraicGeometry.stalkMap_toStalk φ x
  have hchart :
      φ ≫ (Scheme.ΓSpecIso R).inv ≫ (jR.appIso ⊤).inv ≫
        X.presheaf.germ (jR ''ᵁ ⊤) y ⟨x, trivial, rfl⟩ ≫ jR.stalkMap x =
          φ ≫ StructureSheaf.toStalk R x := by
    rw [spectrumImage_germ_stalkMap]
    rfl
  have hpost :
      (jR.stalkMap x).hom
          ((f.stalkMap y).hom (spectrumImageAmbientGerm jR jS φ f hs x s)) =
        (jR.stalkMap x).hom (spectrumImageChartGerm jR φ x s) := by
    have heq := hcomposed.trans hchart.symm
    exact congrArg (fun g : S ⟶ (Spec R).presheaf.stalk x => g.hom s) heq
  have hmono : Function.Injective (jR.stalkMap x).hom :=
    (asIso (jR.stalkMap x)).commRingCatIsoToRingEquiv.injective
  exact hmono hpost

#print axioms spectrumImage_stalkMap_naturality

end Holonics.Hodge.CMGraphSource
