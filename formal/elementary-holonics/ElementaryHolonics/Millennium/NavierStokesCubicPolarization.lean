import ElementaryHolonics.Millennium.NavierStokesQuadraticH3Energy
import Mathlib.Analysis.Normed.Module.Multilinear.Curry

/-!
# Cubic polarization: the gyroparallelogram from diagonal strokes to mixed jets

The existing third-order production identity is addressed by one repeated spatial direction.
The coordinate--Frobenius receiver, however, retains every ordered word of length three.  The
finite bridge is cubic polarization: seven diagonal evaluations recover a symmetric trilinear
face.  This is the precise additive parallelogram calculus needed before the diagonal PDE can be
transported to mixed coordinate words.

This owner first proves the algebraic seven-term identity for an arbitrary symmetric continuous
trilinear scalar map.  It then applies the identity to the genuine third iterated Frechet
derivative of a smooth scalar field.  No Navier--Stokes production estimate, spatial integration,
or identification with the existing line-derivative PDE is asserted here.
-/

noncomputable section

open ContDiff

namespace Soma.Holonics.Millennium.NavierStokesCubicPolarization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesH3Production

/-- Evaluation of a continuous trilinear scalar map on three addressed vectors. -/
def trilinearValue (A : E [×3]→L[ℝ] ℝ) (x y z : E) : ℝ :=
  A ![x, y, z]

/-- The diagonal cubic read from a trilinear map. -/
def cubicDiagonal (A : E [×3]→L[ℝ] ℝ) (x : E) : ℝ :=
  trilinearValue A x x x

/-- The seven addressed diagonal faces which polarize a cubic population. -/
def cubicFacePolarization (face : E → ℝ) (x y z : E) : ℝ :=
  face (x + y + z) - face (x + y) - face (x + z) - face (y + z) +
    face x + face y + face z

theorem trilinearValue_add_first
    (A : E [×3]→L[ℝ] ℝ) (x x' y z : E) :
    trilinearValue A (x + x') y z =
      trilinearValue A x y z + trilinearValue A x' y z := by
  simpa [trilinearValue] using
    A.toMultilinearMap.cons_add ![y, z] x x'

theorem trilinearValue_add_second
    (A : E [×3]→L[ℝ] ℝ) (x y y' z : E) :
    trilinearValue A x (y + y') z =
      trilinearValue A x y z + trilinearValue A x y' z := by
  simpa [trilinearValue] using
    (A.curryLeft x).toMultilinearMap.cons_add ![z] y y'

theorem trilinearValue_add_third
    (A : E [×3]→L[ℝ] ℝ) (x y z z' : E) :
    trilinearValue A x y (z + z') =
      trilinearValue A x y z + trilinearValue A x y z' := by
  simpa [trilinearValue] using
    ((A.curryLeft x).curryLeft y).toMultilinearMap.cons_add ![] z z'

/-- The seven diagonal faces recover six copies of a symmetric trilinear face. -/
theorem cubicPolarization
    (A : E [×3]→L[ℝ] ℝ)
    (hswapFirst : ∀ a b c, trilinearValue A a b c = trilinearValue A b a c)
    (hswapLast : ∀ a b c, trilinearValue A a b c = trilinearValue A a c b)
    (x y z : E) :
    cubicFacePolarization (cubicDiagonal A) x y z =
      6 * trilinearValue A x y z := by
  have hxy : trilinearValue A y x z = trilinearValue A x y z :=
    hswapFirst y x z
  have hxz : trilinearValue A x z y = trilinearValue A x y z :=
    hswapLast x z y
  have hyz : trilinearValue A y z x = trilinearValue A x y z := by
    rw [hswapLast y z x, hswapFirst y x z]
  have hzx : trilinearValue A z x y = trilinearValue A x y z := by
    rw [hswapFirst z x y, hswapLast x z y]
  have hzy : trilinearValue A z y x = trilinearValue A x y z := by
    rw [hswapFirst z y x, hswapLast y z x, hswapFirst y x z]
  simp only [cubicFacePolarization, cubicDiagonal, trilinearValue_add_first,
    trilinearValue_add_second, trilinearValue_add_third]
  rw [hxy, hxz, hyz, hzx, hzy]
  ring

/-! ## The genuine smooth third derivative -/

/-- The scalar third Frechet derivative at one point, exposed as the trilinear carrier used by
polarization. -/
def thirdFDerivAt (f : E → ℝ) (x : E) : E [×3]→L[ℝ] ℝ :=
  iteratedFDeriv ℝ 3 f x

/-- Smooth third derivatives are symmetric under exchange of the first two inputs. -/
theorem trilinearValue_thirdFDerivAt_swap_first
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (a b c : E) :
    trilinearValue (thirdFDerivAt f x) a b c =
      trilinearValue (thirdFDerivAt f x) b a c := by
  have hDf : ContDiffAt ℝ ∞ (fderiv ℝ f) x :=
    hf.fderiv_right (by simp)
  have hsymm : IsSymmSndFDerivAt ℝ (fderiv ℝ f) x :=
    hDf.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.mpr le_top)
  have h := hsymm.iteratedFDeriv_cons (v := a) (w := b)
  have hc := congrArg (fun L : E →L[ℝ] ℝ ↦ L c) h
  have habc : Fin.init ![a, b, c] = ![a, b] := by
    funext i
    fin_cases i <;> rfl
  have hbac : Fin.init ![b, a, c] = ![b, a] := by
    funext i
    fin_cases i <;> rfl
  have hleft :
      trilinearValue (thirdFDerivAt f x) a b c =
        ((iteratedFDeriv ℝ 2 (fderiv ℝ f) x) ![a, b]) c := by
    unfold trilinearValue thirdFDerivAt
    rw [iteratedFDeriv_succ_apply_right, habc]
    rfl
  have hright :
      trilinearValue (thirdFDerivAt f x) b a c =
        ((iteratedFDeriv ℝ 2 (fderiv ℝ f) x) ![b, a]) c := by
    unfold trilinearValue thirdFDerivAt
    rw [iteratedFDeriv_succ_apply_right, hbac]
    rfl
  exact hleft.trans (hc.trans hright.symm)

/-- Smooth third derivatives are symmetric under exchange of the last two inputs. -/
theorem trilinearValue_thirdFDerivAt_swap_last
    {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ ∞ f x)
    (a b c : E) :
    trilinearValue (thirdFDerivAt f x) a b c =
      trilinearValue (thirdFDerivAt f x) a c b := by
  let evaluateBC : (E [×2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E) ℝ ![b, c]
  let evaluateCB : (E [×2]→L[ℝ] ℝ) →L[ℝ] ℝ :=
    ContinuousMultilinearMap.apply ℝ (fun _ : Fin 2 ↦ E) ℝ ![c, b]
  have hfinite : ContDiffAt ℝ 2 f x :=
    hf.of_le (WithTop.coe_le_coe.mpr (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hevent : ∀ᶠ q in nhds x, ContDiffAt ℝ 2 f q :=
    hfinite.eventually (by simp)
  have heq :
      (fun q ↦ evaluateBC (iteratedFDeriv ℝ 2 f q)) =ᶠ[nhds x]
        (fun q ↦ evaluateCB (iteratedFDeriv ℝ 2 f q)) := by
    filter_upwards [hevent] with q hq
    have hsymm : IsSymmSndFDerivAt ℝ f q :=
      hq.isSymmSndFDerivAt (by
        rw [minSmoothness_of_isRCLikeNormedField])
    simpa [evaluateBC, evaluateCB] using
      hsymm.iteratedFDeriv_cons (v := b) (w := c)
  have hderiv := heq.fderiv_eq (𝕜 := ℝ)
  have ha := congrArg (fun L : E →L[ℝ] ℝ ↦ L a) hderiv
  have hD2 : DifferentiableAt ℝ (iteratedFDeriv ℝ 2 f) x :=
    hf.differentiableAt_iteratedFDeriv
      (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top 2))
  have hBC :
      fderiv ℝ (fun q ↦ evaluateBC (iteratedFDeriv ℝ 2 f q)) x =
        evaluateBC.comp (fderiv ℝ (iteratedFDeriv ℝ 2 f) x) := by
    simpa only [ContinuousLinearMap.fderiv] using
      fderiv_comp' x evaluateBC.differentiableAt hD2
  have hCB :
      fderiv ℝ (fun q ↦ evaluateCB (iteratedFDeriv ℝ 2 f q)) x =
        evaluateCB.comp (fderiv ℝ (iteratedFDeriv ℝ 2 f) x) := by
    simpa only [ContinuousLinearMap.fderiv] using
      fderiv_comp' x evaluateCB.differentiableAt hD2
  rw [hBC, hCB] at ha
  simpa [trilinearValue, thirdFDerivAt, evaluateBC, evaluateCB,
    iteratedFDeriv_succ_apply_left] using ha

/-- Seven diagonal third-derivative strokes recover every mixed third derivative of a smooth
scalar field. -/
theorem thirdFDerivAt_cubicPolarization
    {f : E → ℝ} {base : E} (hf : ContDiffAt ℝ ∞ f base)
    (x y z : E) :
    cubicFacePolarization (cubicDiagonal (thirdFDerivAt f base)) x y z =
      6 * trilinearValue (thirdFDerivAt f base) x y z := by
  exact cubicPolarization (thirdFDerivAt f base)
    (trilinearValue_thirdFDerivAt_swap_first hf)
    (trilinearValue_thirdFDerivAt_swap_last hf) x y z

/-! ## Diagonal Frechet faces are the actual affine-line strokes -/

/-- The continuous linear passage sending a scalar line parameter to its addressed spatial
displacement. -/
def scalarLineMap (direction : E) : ℝ →L[ℝ] E :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) direction

@[simp]
theorem scalarLineMap_apply (direction : E) (s : ℝ) :
    scalarLineMap direction s = s • direction := by
  rfl

/-- The third ordinary derivative along an affine line is exactly the diagonal evaluation of the
third Frechet derivative. -/
theorem iteratedDeriv_three_affineLine_eq_cubicDiagonal
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (base direction : E) :
    iteratedDeriv 3 (fun s : ℝ ↦ f (base + s • direction)) 0 =
      cubicDiagonal (thirdFDerivAt f base) direction := by
  let shifted : E → ℝ := fun z ↦ f (base + z)
  have hshifted : ContDiff ℝ ∞ shifted := by
    exact hf.comp (contDiff_const.add contDiff_id)
  have hcomp := (scalarLineMap direction).iteratedFDeriv_comp_right
    hshifted 0 (i := 3) (WithTop.coe_le_coe.mpr le_top)
  have hat := congrArg
    (fun A : (ℝ [×3]→L[ℝ] ℝ) ↦ A (fun _ : Fin 3 ↦ 1)) hcomp
  have htranslate := iteratedFDeriv_comp_add_left (𝕜 := ℝ) (f := f) 3 base 0
  have hdirections : (fun _ : Fin 3 ↦ direction) = ![direction, direction, direction] := by
    funext i
    fin_cases i <;> rfl
  simpa [shifted, scalarLineMap, cubicDiagonal, trilinearValue, thirdFDerivAt,
    Function.comp_def, iteratedDeriv_eq_iteratedFDeriv, htranslate, hdirections] using hat

/-- The mixed third Frechet face is recovered exactly from seven actual affine-line strokes. -/
theorem mixedThirdFDeriv_eq_seven_affineLineStrokes
    {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (base x y z : E) :
    6 * trilinearValue (thirdFDerivAt f base) x y z =
      cubicFacePolarization
        (fun direction ↦ iteratedDeriv 3
          (fun s : ℝ ↦ f (base + s • direction)) 0)
        x y z := by
  have hpolar := thirdFDerivAt_cubicPolarization (base := base) hf.contDiffAt x y z
  rw [cubicFacePolarization]
  rw [iteratedDeriv_three_affineLine_eq_cubicDiagonal hf,
    iteratedDeriv_three_affineLine_eq_cubicDiagonal hf,
    iteratedDeriv_three_affineLine_eq_cubicDiagonal hf,
    iteratedDeriv_three_affineLine_eq_cubicDiagonal hf,
    iteratedDeriv_three_affineLine_eq_cubicDiagonal hf,
    iteratedDeriv_three_affineLine_eq_cubicDiagonal hf,
    iteratedDeriv_three_affineLine_eq_cubicDiagonal hf]
  simpa [cubicFacePolarization] using hpolar.symm

/-- On the actual Navier--Stokes spatial carrier, every mixed third velocity-component face is
recovered from the seven diagonal strokes already used by the production equation. -/
theorem mixedThirdVelocityComponent_eq_sevenDirectionalStrokes
    {u : InitialVelocity} (hu : ContDiff ℝ ∞ u)
    (base x y z : Space) (component : Fin 3) :
    6 * trilinearValue
        (thirdFDerivAt (fun q ↦ u q component) base) x y z =
      cubicFacePolarization
        (fun direction ↦ iteratedDeriv 3
          (velocityComponentLine u base direction component) 0)
        x y z := by
  have hcomponent : ContDiff ℝ ∞ (fun q ↦ u q component) := by
    simpa [Function.comp_def] using
      (EuclideanSpace.proj component).contDiff.comp hu
  change
    6 * trilinearValue
        (thirdFDerivAt (fun q ↦ u q component) base) x y z =
      cubicFacePolarization
        (fun direction ↦ iteratedDeriv 3
          (fun s : ℝ ↦ u (base + s • direction) component) 0)
        x y z
  exact mixedThirdFDeriv_eq_seven_affineLineStrokes hcomponent base x y z

section Audit

#print axioms cubicPolarization
#print axioms trilinearValue_thirdFDerivAt_swap_first
#print axioms trilinearValue_thirdFDerivAt_swap_last
#print axioms thirdFDerivAt_cubicPolarization
#print axioms iteratedDeriv_three_affineLine_eq_cubicDiagonal
#print axioms mixedThirdFDeriv_eq_seven_affineLineStrokes
#print axioms mixedThirdVelocityComponent_eq_sevenDirectionalStrokes

end Audit

end Soma.Holonics.Millennium.NavierStokesCubicPolarization
