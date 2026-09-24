import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic

/-!
# An exact two-face constitutive reduction

The current is presented in four cut coordinates and two active face coordinates:

`j = J q + D z + r`.

The residual `r` is retained as part of the current fibre.  It is blind to the
active face receiver (`Dᵀ r = 0`) and, when a cut reading is claimed, to the
cut receiver as well.  The material law is the finite rational law
`j_after + τ D M Dᵀ j_after = j_before + J u + D f`.

This file proves the exact compact update and an explicit plus/minus decoder.
The decoder is supplied with the maps and their identities. For a fixed complete
source and forcing, the fine response is unique under the positive modal denominators;
distinct source fibres are still retained.
-/

noncomputable section

namespace Soma.Holonics.Physics.TwoFaceConstitutive

abbrev Cut := Fin 4 → ℚ
abbrev Face := Fin 2 → ℚ

variable {Current : Type*} [AddCommGroup Current] [Module ℚ Current]

def faceMetric : Face →ₗ[ℚ] Face where
  toFun := fun z ↦ ![4 * z 0 + z 1, z 0 + 4 * z 1]
  map_add' := by
    intro left right
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro scalar z
    funext i
    fin_cases i <;> simp <;> ring

def cutFaceCoupling : Cut →ₗ[ℚ] Face where
  toFun := fun q ↦ ![q 0 - q 1, q 0 - q 2]
  map_add' := by
    intro left right
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro scalar q
    funext i
    fin_cases i <;> simp <;> ring

def materialMap (mu nu : ℚ) : Face →ₗ[ℚ] Face where
  toFun := fun z ↦ ![mu * z 0 + nu * z 1, nu * z 0 + mu * z 1]
  map_add' := by
    intro left right
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro scalar z
    funext i
    fin_cases i <;> simp <;> ring

def facePlus (z : Face) : ℚ := z 0 + z 1

def faceMinus (z : Face) : ℚ := z 0 - z 1

def faceOfPlusMinus (p m : ℚ) : Face := ![(p + m) / 2, (p - m) / 2]

theorem faceOfPlusMinus_plus (p m : ℚ) :
    facePlus (faceOfPlusMinus p m) = p := by
  simp [facePlus, faceOfPlusMinus]
  ring

theorem faceOfPlusMinus_minus (p m : ℚ) :
    faceMinus (faceOfPlusMinus p m) = m := by
  simp [faceMinus, faceOfPlusMinus]
  ring

theorem face_eq_of_plus_minus_eq
    {left right : Face}
    (hplus : facePlus left = facePlus right)
    (hminus : faceMinus left = faceMinus right) : left = right := by
  change left 0 + left 1 = right 0 + right 1 at hplus
  change left 0 - left 1 = right 0 - right 1 at hminus
  funext i
  fin_cases i
  · change left 0 = right 0
    linarith [hplus, hminus]
  · change left 1 = right 1
    linarith [hplus, hminus]

theorem faceMetric_material_commute (mu nu : ℚ) :
    faceMetric.comp (materialMap mu nu) =
      (materialMap mu nu).comp faceMetric := by
  apply LinearMap.ext
  intro z
  funext i
  fin_cases i <;> simp [faceMetric, materialMap] <;> ring

theorem faceMetric_injective : Function.Injective faceMetric := by
  intro left right h
  have h0 := congrArg (fun z : Face ↦ z 0) h
  have h1 := congrArg (fun z : Face ↦ z 1) h
  dsimp [faceMetric] at h0 h1
  change 4 * left 0 + left 1 = 4 * right 0 + right 1 at h0
  change left 0 + 4 * left 1 = right 0 + 4 * right 1 at h1
  funext i
  fin_cases i
  · change left 0 = right 0
    linarith [h0, h1]
  · change left 1 = right 1
    linarith [h0, h1]

def decodedCurrent
    (J : Cut →ₗ[ℚ] Current) (D : Face →ₗ[ℚ] Current)
    (q : Cut) (z : Face) (r : Current) : Current :=
  J q + D z + r

def fineLaw
    (tau mu nu : ℚ)
    (J : Cut →ₗ[ℚ] Current) (D : Face →ₗ[ℚ] Current)
    (Dt : Current →ₗ[ℚ] Face)
    (jBefore jAfter : Current) (u : Cut) (f : Face) : Prop :=
  jAfter + tau • D (materialMap mu nu (Dt jAfter)) =
    jBefore + J u + D f

def compactLaw
    (tau mu nu : ℚ) (q u : Cut) (f z z' : Face) : Prop :=
  z' + tau • materialMap mu nu
      (cutFaceCoupling (q + u) + faceMetric z') = z + f

def compactPlusUpdate
    (tau mu nu : ℚ) (qPrime : Cut) (z f : Face) : ℚ :=
  (facePlus z + facePlus f -
      tau * (mu + nu) * (2 * qPrime 0 - qPrime 1 - qPrime 2)) /
    (1 + 5 * tau * (mu + nu))

def compactMinusUpdate
    (tau mu nu : ℚ) (qPrime : Cut) (z f : Face) : ℚ :=
  (faceMinus z + faceMinus f -
      tau * (mu - nu) * (qPrime 2 - qPrime 1)) /
    (1 + 3 * tau * (mu - nu))

def compactExplicitUpdate
    (tau mu nu : ℚ) (qPrime : Cut) (z f : Face) : Face :=
  faceOfPlusMinus
    (compactPlusUpdate tau mu nu qPrime z f)
    (compactMinusUpdate tau mu nu qPrime z f)

theorem plus_denominator_pos
    {tau mu nu : ℚ} (htau : 0 ≤ tau)
    (hplus : 0 ≤ mu + nu) :
    0 < 1 + 5 * tau * (mu + nu) := by
  nlinarith

theorem minus_denominator_pos
    {tau mu nu : ℚ} (htau : 0 ≤ tau)
    (hminus : 0 ≤ mu - nu) :
    0 < 1 + 3 * tau * (mu - nu) := by
  nlinarith

theorem compactExplicitUpdate_plus
    (tau mu nu : ℚ) (qPrime : Cut) (z f : Face) :
    facePlus (compactExplicitUpdate tau mu nu qPrime z f) =
      compactPlusUpdate tau mu nu qPrime z f := by
  exact faceOfPlusMinus_plus _ _

theorem compactExplicitUpdate_minus
    (tau mu nu : ℚ) (qPrime : Cut) (z f : Face) :
    faceMinus (compactExplicitUpdate tau mu nu qPrime z f) =
      compactMinusUpdate tau mu nu qPrime z f := by
  exact faceOfPlusMinus_minus _ _

theorem compactExplicitUpdate_solves
    {tau mu nu : ℚ} (htau : 0 ≤ tau)
    (hplus : 0 ≤ mu + nu) (hminus : 0 ≤ mu - nu)
    (q u : Cut) (z f : Face) :
    compactLaw tau mu nu q u f z
      (compactExplicitUpdate tau mu nu (q + u) z f) := by
  have hdenPlus : 1 + 5 * tau * (mu + nu) ≠ 0 :=
    (plus_denominator_pos htau hplus).ne'
  have hdenMinus : 1 + 3 * tau * (mu - nu) ≠ 0 :=
    (minus_denominator_pos htau hminus).ne'
  unfold compactLaw compactExplicitUpdate
  apply face_eq_of_plus_minus_eq
  · simp only [facePlus]
    dsimp [faceMetric, cutFaceCoupling, materialMap, facePlus, faceOfPlusMinus,
      compactPlusUpdate]
    field_simp [hdenPlus, hdenMinus]
    ring
  · simp only [faceMinus]
    dsimp [faceMetric, cutFaceCoupling, materialMap, faceMinus, faceOfPlusMinus,
      compactMinusUpdate]
    field_simp [hdenPlus, hdenMinus]
    ring

theorem compactLaw_unique
    {tau mu nu : ℚ}
    (hplus : 0 < 1 + 5 * tau * (mu + nu))
    (hminus : 0 < 1 + 3 * tau * (mu - nu))
    (q u : Cut) (z f left right : Face)
    (hleft : compactLaw tau mu nu q u f z left)
    (hright : compactLaw tau mu nu q u f z right) :
    left = right := by
  have hleftPlus := congrArg facePlus hleft
  have hrightPlus := congrArg facePlus hright
  have hleftMinus := congrArg faceMinus hleft
  have hrightMinus := congrArg faceMinus hright
  dsimp [compactLaw, facePlus, faceMinus, faceMetric, cutFaceCoupling,
    materialMap] at hleftPlus hrightPlus hleftMinus hrightMinus
  ring_nf at hleftPlus hrightPlus hleftMinus hrightMinus
  have hplusEq :
      (1 + 5 * tau * (mu + nu)) *
          ((left 0 + left 1) - (right 0 + right 1)) = 0 := by
    linear_combination hleftPlus - hrightPlus
  have hminusEq :
      (1 + 3 * tau * (mu - nu)) *
          ((left 0 - left 1) - (right 0 - right 1)) = 0 := by
    linear_combination hleftMinus - hrightMinus
  apply face_eq_of_plus_minus_eq
  · change left 0 + left 1 = right 0 + right 1
    nlinarith [hplusEq, hplus]
  · change left 0 - left 1 = right 0 - right 1
    nlinarith [hminusEq, hminus]

theorem decodedCurrent_cut
    (J : Cut →ₗ[ℚ] Current) (D : Face →ₗ[ℚ] Current)
    (C : Current →ₗ[ℚ] Cut)
    (q : Cut) (z : Face) (r : Current)
    (hCJ : C.comp J = LinearMap.id)
    (hCD : C.comp D = 0)
    (hCr : C r = 0) :
    C (decodedCurrent J D q z r) = q := by
  unfold decodedCurrent
  rw [map_add, map_add]
  have hJ : C (J q) = q := by
    simpa using congrArg (fun L : Cut →ₗ[ℚ] Cut ↦ L q) hCJ
  have hD : C (D z) = 0 := by
    simpa using congrArg (fun L : Face →ₗ[ℚ] Cut ↦ L z) hCD
  rw [hJ, hD, hCr]
  simp

theorem decodedCurrent_face
    (J : Cut →ₗ[ℚ] Current) (D : Face →ₗ[ℚ] Current)
    (Dt : Current →ₗ[ℚ] Face)
    (q : Cut) (z : Face) (r : Current)
    (hDtJ : Dt.comp J = cutFaceCoupling)
    (hDtD : Dt.comp D = faceMetric)
    (hDtr : Dt r = 0) :
    Dt (decodedCurrent J D q z r) =
      cutFaceCoupling q + faceMetric z := by
  unfold decodedCurrent
  rw [map_add, map_add]
  have hJ : Dt (J q) = cutFaceCoupling q := by
    simpa using congrArg (fun L : Cut →ₗ[ℚ] Face ↦ L q) hDtJ
  have hD : Dt (D z) = faceMetric z := by
    simpa using congrArg (fun L : Face →ₗ[ℚ] Face ↦ L z) hDtD
  rw [hJ, hD, hDtr]
  simp

theorem decodedCurrent_compact_solves_fine
    {tau mu nu : ℚ} (J : Cut →ₗ[ℚ] Current)
    (D : Face →ₗ[ℚ] Current) (Dt : Current →ₗ[ℚ] Face)
    (q u : Cut) (z f z' : Face) (r : Current)
    (hDtJ : Dt.comp J = cutFaceCoupling)
    (hDtD : Dt.comp D = faceMetric)
    (hDtr : Dt r = 0)
    (hcompact : compactLaw tau mu nu q u f z z') :
    fineLaw tau mu nu J D Dt
      (decodedCurrent J D q z r)
      (decodedCurrent J D (q + u) z' r) u f := by
  have hfaceAfter :
      Dt (decodedCurrent J D (q + u) z' r) =
        cutFaceCoupling (q + u) + faceMetric z' :=
    decodedCurrent_face J D Dt (q + u) z' r hDtJ hDtD hDtr
  have hfaceAfter' :
      Dt (J (q + u) + D z' + r) =
        cutFaceCoupling (q + u) + faceMetric z' := by
    simpa [decodedCurrent] using hfaceAfter
  have hcompactD := congrArg (fun w : Face ↦ D w) hcompact
  change D (z' + tau • materialMap mu nu
      (cutFaceCoupling (q + u) + faceMetric z')) = D (z + f) at hcompactD
  rw [map_add, map_smul] at hcompactD
  unfold fineLaw decodedCurrent
  rw [hfaceAfter']
  calc
    J (q + u) + D z' + r +
        tau • D (materialMap mu nu
          (cutFaceCoupling (q + u) + faceMetric z')) =
      J (q + u) + r +
        (D z' + tau • D (materialMap mu nu
          (cutFaceCoupling (q + u) + faceMetric z'))) := by module
    _ = J (q + u) + r + D (z + f) := by rw [hcompactD]
    _ = J q + D z + r + J u + D f := by rw [J.map_add, D.map_add]; module

theorem decodedCurrent_explicitUpdate_solves_fine
    {tau mu nu : ℚ} (htau : 0 ≤ tau)
    (hplus : 0 ≤ mu + nu) (hminus : 0 ≤ mu - nu)
    (J : Cut →ₗ[ℚ] Current) (D : Face →ₗ[ℚ] Current)
    (Dt : Current →ₗ[ℚ] Face)
    (q u : Cut) (z f : Face) (r : Current)
    (hDtJ : Dt.comp J = cutFaceCoupling)
    (hDtD : Dt.comp D = faceMetric)
    (hDtr : Dt r = 0) :
    fineLaw tau mu nu J D Dt
      (decodedCurrent J D q z r)
      (decodedCurrent J D (q + u)
        (compactExplicitUpdate tau mu nu (q + u) z f) r) u f := by
  apply decodedCurrent_compact_solves_fine J D Dt q u z f
    (compactExplicitUpdate tau mu nu (q + u) z f) r hDtJ hDtD hDtr
  exact compactExplicitUpdate_solves htau hplus hminus q u z f

theorem decodedCurrent_cut_after
    (J : Cut →ₗ[ℚ] Current) (D : Face →ₗ[ℚ] Current)
    (C : Current →ₗ[ℚ] Cut)
    (qPrime : Cut) (zPrime : Face) (r : Current)
    (hCJ : C.comp J = LinearMap.id)
    (hCD : C.comp D = 0)
    (hCr : C r = 0) :
    C (decodedCurrent J D qPrime zPrime r) = qPrime := by
  exact decodedCurrent_cut J D C qPrime zPrime r hCJ hCD hCr

/-- With the complete source and forcing fixed, the fine response is unique.
Distinct sources can still retain distinct jointly blind residuals. -/
theorem fineLaw_unique {tau mu nu : ℚ}
 (J : Cut →ₗ[ℚ] Current) (D : Face →ₗ[ℚ] Current) (Dt : Current →ₗ[ℚ] Face)
 (hDtD : Dt.comp D = faceMetric)
 (hplus : 0 < 1 + 5 * tau * (mu + nu))
 (hminus : 0 < 1 + 3 * tau * (mu - nu))
 (before left right : Current) (u : Cut) (f : Face)
 (hl : fineLaw tau mu nu J D Dt before left u f)
 (hr : fineLaw tau mu nu J D Dt before right u f) : left = right := by
 have h := hl.trans hr.symm
 have hDt := congrArg Dt h
 simp only [map_add, map_smul] at hDt
 have hd (v : Face) : Dt (D v) = faceMetric v := by
  exact LinearMap.congr_fun hDtD v
 have hc (v : Face) : faceMetric (materialMap mu nu v) = materialMap mu nu (faceMetric v) := by
  exact LinearMap.congr_fun (faceMetric_material_commute mu nu) v
 simp_rw [hd, hc] at hDt
 let z := Dt left + tau • materialMap mu nu (faceMetric (Dt left))
 have hlc : compactLaw tau mu nu 0 0 0 z (Dt left) := by
  simp [compactLaw, z]
 have hrc : compactLaw tau mu nu 0 0 0 z (Dt right) := by
  simpa [compactLaw, z] using hDt.symm
 have he := compactLaw_unique hplus hminus 0 0 z 0 (Dt left) (Dt right) hlc hrc
 rw [he] at h
 exact add_right_cancel h

end Soma.Holonics.Physics.TwoFaceConstitutive

section Audit
open Soma.Holonics.Physics.TwoFaceConstitutive
#print axioms compactExplicitUpdate_solves
#print axioms compactLaw_unique
#print axioms fineLaw_unique
#print axioms decodedCurrent_cut
#print axioms decodedCurrent_face
#print axioms decodedCurrent_compact_solves_fine
#print axioms decodedCurrent_explicitUpdate_solves_fine
end Audit
