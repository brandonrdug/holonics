import ElementaryHolonics.Physics.TwoFaceConstitutive

/-!
# Cold residual decoding for the two-face constitutive current

The four cut coordinates and two active face coordinates form a six-dimensional
decoded image inside an arbitrary finite current module.  Every current is
reconstructed as that image plus a retained residual.  The residual is blind to
both receivers and remains available as a cold fibre; a fixed-source fine law
may still determine it through the original current equation.

Uniqueness is stated on the decoded image.  Arbitrary fine currents have the
same reduced response precisely up to their retained cold residual; no claim is
made that the receivers identify those residuals.
-/

noncomputable section

namespace Soma.Holonics.Physics.ConstitutiveCurrentReduction

open Soma.Holonics.Physics.TwoFaceConstitutive

abbrev Cut := Fin 4 → ℚ
abbrev Face := Fin 2 → ℚ

variable {Current : Type*} [AddCommGroup Current] [Module ℚ Current]

structure ConstitutiveChart (Current : Type*) [AddCommGroup Current]
    [Module ℚ Current] where
  C : Current →ₗ[ℚ] Cut
  J : Cut →ₗ[ℚ] Current
  D : Face →ₗ[ℚ] Current
  Dt : Current →ₗ[ℚ] Face
  CJ : C.comp J = LinearMap.id
  CD : C.comp D = 0
  DtJ : Dt.comp J = cutFaceCoupling
  DtD : Dt.comp D = faceMetric

def faceMetricInverse : Face →ₗ[ℚ] Face where
  toFun := fun z ↦ ![(4 * z 0 - z 1) / 15, (-z 0 + 4 * z 1) / 15]
  map_add' := by
    intro left right
    funext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro scalar z
    funext i
    fin_cases i <;> simp <;> ring

theorem faceMetricInverse_faceMetric :
    faceMetricInverse.comp faceMetric = LinearMap.id := by
  apply LinearMap.ext
  intro z
  funext i
  fin_cases i <;> simp [faceMetric, faceMetricInverse] <;> ring

theorem faceMetric_faceMetricInverse :
    faceMetric.comp faceMetricInverse = LinearMap.id := by
  apply LinearMap.ext
  intro z
  funext i
  fin_cases i <;> simp [faceMetric, faceMetricInverse] <;> ring

def extractedCut (chart : ConstitutiveChart Current) (j : Current) : Cut :=
  chart.C j

def extractedFace (chart : ConstitutiveChart Current) (j : Current) : Face :=
  faceMetricInverse (chart.Dt j - cutFaceCoupling (chart.C j))

def extractedResidual (chart : ConstitutiveChart Current) (j : Current) : Current :=
  j - chart.J (extractedCut chart j) - chart.D (extractedFace chart j)

def decodedZero (chart : ConstitutiveChart Current) (q : Cut) (z : Face) : Current :=
  decodedCurrent chart.J chart.D q z 0

theorem extractedFace_metric_eq_receiver_difference
    (chart : ConstitutiveChart Current) (j : Current) :
    faceMetric (extractedFace chart j) =
      chart.Dt j - cutFaceCoupling (chart.C j) := by
  unfold extractedFace
  have h := congrArg
    (fun L : Face →ₗ[ℚ] Face ↦ L (chart.Dt j - cutFaceCoupling (chart.C j)))
    faceMetric_faceMetricInverse
  simpa using h

theorem extractedResidual_cut_zero
    (chart : ConstitutiveChart Current) (j : Current) :
    chart.C (extractedResidual chart j) = 0 := by
  unfold extractedResidual extractedCut
  rw [map_sub, map_sub]
  have hJ : chart.C (chart.J (chart.C j)) = chart.C j := by
    simpa using congrArg (fun L : Cut →ₗ[ℚ] Cut ↦ L (chart.C j)) chart.CJ
  have hD : chart.C (chart.D (extractedFace chart j)) = 0 := by
    simpa using congrArg (fun L : Face →ₗ[ℚ] Cut ↦ L (extractedFace chart j)) chart.CD
  rw [hJ, hD]
  abel

theorem extractedResidual_face_zero
    (chart : ConstitutiveChart Current) (j : Current) :
    chart.Dt (extractedResidual chart j) = 0 := by
  unfold extractedResidual extractedCut
  rw [map_sub, map_sub]
  have hJ : chart.Dt (chart.J (chart.C j)) = cutFaceCoupling (chart.C j) := by
    simpa using congrArg (fun L : Cut →ₗ[ℚ] Face ↦ L (chart.C j)) chart.DtJ
  have hD : chart.Dt (chart.D (extractedFace chart j)) =
      faceMetric (extractedFace chart j) := by
    simpa using congrArg (fun L : Face →ₗ[ℚ] Face ↦ L (extractedFace chart j)) chart.DtD
  rw [hJ, hD, extractedFace_metric_eq_receiver_difference]
  abel

theorem decode_extractedCurrent_exact
    (chart : ConstitutiveChart Current) (j : Current) :
    decodedCurrent chart.J chart.D
        (extractedCut chart j) (extractedFace chart j)
        (extractedResidual chart j) = j := by
  unfold decodedCurrent extractedResidual
  abel

theorem extractedCurrent_cut
    (chart : ConstitutiveChart Current) (q : Cut) (z : Face) :
    extractedCut chart (decodedZero chart q z) = q := by
  unfold extractedCut decodedZero decodedCurrent
  rw [map_add, map_add]
  have hJ : chart.C (chart.J q) = q := by
    simpa using congrArg (fun L : Cut →ₗ[ℚ] Cut ↦ L q) chart.CJ
  have hD : chart.C (chart.D z) = 0 := by
    simpa using congrArg (fun L : Face →ₗ[ℚ] Cut ↦ L z) chart.CD
  rw [hJ, hD]
  simp

theorem extractedCurrent_face
    (chart : ConstitutiveChart Current) (q : Cut) (z : Face) :
    extractedFace chart (decodedZero chart q z) = z := by
  apply faceMetric_injective
  rw [extractedFace_metric_eq_receiver_difference]
  unfold decodedZero decodedCurrent
  rw [map_add, map_add]
  have hJ : chart.Dt (chart.J q) = cutFaceCoupling q := by
    simpa using congrArg (fun L : Cut →ₗ[ℚ] Face ↦ L q) chart.DtJ
  have hD : chart.Dt (chart.D z) = faceMetric z := by
    simpa using congrArg (fun L : Face →ₗ[ℚ] Face ↦ L z) chart.DtD
  rw [hJ, hD]
  have hCj : chart.C (chart.J q) = q := by
    simpa using congrArg (fun L : Cut →ₗ[ℚ] Cut ↦ L q) chart.CJ
  have hCd : chart.C (chart.D z) = 0 := by
    simpa using congrArg (fun L : Face →ₗ[ℚ] Cut ↦ L z) chart.CD
  have hCsum : chart.C (chart.J q + chart.D z + 0) = q := by
    rw [map_add, map_add, hCj, hCd]
    simp
  rw [hCsum]
  simp

theorem extractedResidual_decodedCurrent
    (chart : ConstitutiveChart Current) (q : Cut) (z : Face) (r : Current)
    (hCr : chart.C r = 0) (hDtr : chart.Dt r = 0) :
    extractedResidual chart
        (decodedCurrent chart.J chart.D q z r) = r := by
  have hcut : extractedCut chart
      (decodedCurrent chart.J chart.D q z r) = q :=
    decodedCurrent_cut chart.J chart.D chart.C q z r chart.CJ chart.CD hCr
  have hDt : chart.Dt (decodedCurrent chart.J chart.D q z r) =
      cutFaceCoupling q + faceMetric z :=
    decodedCurrent_face chart.J chart.D chart.Dt q z r chart.DtJ chart.DtD hDtr
  have hC : chart.C (decodedCurrent chart.J chart.D q z r) = q :=
    decodedCurrent_cut chart.J chart.D chart.C q z r chart.CJ chart.CD hCr
  have hfaceMetric : faceMetric (extractedFace chart
      (decodedCurrent chart.J chart.D q z r)) = faceMetric z := by
    rw [extractedFace_metric_eq_receiver_difference, hDt, hC]
    simp
  have hface : extractedFace chart
      (decodedCurrent chart.J chart.D q z r) = z :=
    faceMetric_injective hfaceMetric
  unfold extractedResidual
  rw [hcut, hface]
  unfold decodedCurrent
  module

theorem extractedCurrent_residual_zero
    (chart : ConstitutiveChart Current) (q : Cut) (z : Face) :
    extractedResidual chart (decodedZero chart q z) = 0 := by
  unfold extractedResidual decodedZero decodedCurrent
  have hcut : extractedCut chart (chart.J q + chart.D z + 0) = q := by
    simpa [decodedZero, decodedCurrent] using extractedCurrent_cut chart q z
  have hface : extractedFace chart (chart.J q + chart.D z + 0) = z := by
    simpa [decodedZero, decodedCurrent] using extractedCurrent_face chart q z
  rw [hcut, hface]
  simp

def reducedRead (chart : ConstitutiveChart Current) (j : Current) : Cut × Face :=
  (extractedCut chart j, extractedFace chart j)

theorem reducedRead_decodedZero
    (chart : ConstitutiveChart Current) (q : Cut) (z : Face) :
    reducedRead chart (decodedZero chart q z) = (q, z) := by
  have hcut : extractedCut chart (decodedZero chart q z) = q := by
    simpa [decodedZero] using extractedCurrent_cut chart q z
  have hface : extractedFace chart (decodedZero chart q z) = z := by
    simpa [decodedZero] using extractedCurrent_face chart q z
  exact Prod.ext hcut hface

def reducedScaleTransport
    {Source Target : Type*}
    [AddCommGroup Source] [Module ℚ Source]
    [AddCommGroup Target] [Module ℚ Target]
    (source : ConstitutiveChart Source) (target : ConstitutiveChart Target)
    (j : Source) : Target :=
  decodedZero target
    (extractedCut source j) (extractedFace source j)

theorem reducedScaleTransport_factors_through_read
    {Source Target : Type*}
    [AddCommGroup Source] [Module ℚ Source]
    [AddCommGroup Target] [Module ℚ Target]
    (source : ConstitutiveChart Source) (target : ConstitutiveChart Target)
    (j : Source) :
    reducedScaleTransport source target j =
      decodedZero target (reducedRead source j).1 (reducedRead source j).2 := rfl

theorem reducedScaleTransport_on_decodedZero
    {Source Target : Type*}
    [AddCommGroup Source] [Module ℚ Source]
    [AddCommGroup Target] [Module ℚ Target]
    (source : ConstitutiveChart Source) (target : ConstitutiveChart Target)
    (q : Cut) (z : Face) :
    reducedScaleTransport source target (decodedZero source q z) =
      decodedZero target q z := by
  unfold reducedScaleTransport
  have hcut : extractedCut source (decodedZero source q z) = q := by
    simpa [decodedZero] using extractedCurrent_cut source q z
  have hface : extractedFace source (decodedZero source q z) = z := by
    simpa [decodedZero] using extractedCurrent_face source q z
  rw [hcut, hface]

theorem reducedRead_scaleTransport
    {Source Target : Type*}
    [AddCommGroup Source] [Module ℚ Source]
    [AddCommGroup Target] [Module ℚ Target]
    (source : ConstitutiveChart Source) (target : ConstitutiveChart Target)
    (j : Source) :
    reducedRead target (reducedScaleTransport source target j) =
      reducedRead source j := by
  have h := reducedRead_decodedZero target
    (extractedCut source j) (extractedFace source j)
  simpa [reducedRead, reducedScaleTransport] using h

def currentStep
    (chart : ConstitutiveChart Current)
    (tau mu nu : ℚ) (u : Cut) (f : Face) (j : Current) : Current :=
  decodedCurrent chart.J chart.D
    (extractedCut chart j + u)
    (compactExplicitUpdate tau mu nu
      (extractedCut chart j + u) (extractedFace chart j) f)
    (extractedResidual chart j)

theorem currentStep_cut
    (chart : ConstitutiveChart Current)
    (tau mu nu : ℚ) (u : Cut) (f : Face) (j : Current) :
    extractedCut chart (currentStep chart tau mu nu u f j) =
      extractedCut chart j + u := by
  unfold currentStep
  exact decodedCurrent_cut chart.J chart.D chart.C
    (extractedCut chart j + u)
    (compactExplicitUpdate tau mu nu
      (extractedCut chart j + u) (extractedFace chart j) f)
    (extractedResidual chart j)
    chart.CJ chart.CD (extractedResidual_cut_zero chart j)

theorem currentStep_face
    (chart : ConstitutiveChart Current)
    (tau mu nu : ℚ) (u : Cut) (f : Face) (j : Current) :
    extractedFace chart (currentStep chart tau mu nu u f j) =
      compactExplicitUpdate tau mu nu
        (extractedCut chart j + u) (extractedFace chart j) f := by
  apply faceMetric_injective
  rw [extractedFace_metric_eq_receiver_difference]
  unfold currentStep
  rw [decodedCurrent_face chart.J chart.D chart.Dt
    (extractedCut chart j + u)
    (compactExplicitUpdate tau mu nu
      (extractedCut chart j + u) (extractedFace chart j) f)
    (extractedResidual chart j) chart.DtJ chart.DtD
      (extractedResidual_face_zero chart j)]
  have hC := decodedCurrent_cut chart.J chart.D chart.C
    (extractedCut chart j + u)
    (compactExplicitUpdate tau mu nu
      (extractedCut chart j + u) (extractedFace chart j) f)
    (extractedResidual chart j) chart.CJ chart.CD
      (extractedResidual_cut_zero chart j)
  rw [hC]
  simp

theorem currentStep_residual
    (chart : ConstitutiveChart Current)
    (tau mu nu : ℚ) (u : Cut) (f : Face) (j : Current) :
    extractedResidual chart (currentStep chart tau mu nu u f j) =
      extractedResidual chart j := by
  unfold currentStep
  exact extractedResidual_decodedCurrent chart
    (extractedCut chart j + u)
    (compactExplicitUpdate tau mu nu
      (extractedCut chart j + u) (extractedFace chart j) f)
    (extractedResidual chart j)
    (extractedResidual_cut_zero chart j)
    (extractedResidual_face_zero chart j)

theorem currentStep_solves_fine
    {tau mu nu : ℚ} (htau : 0 ≤ tau)
    (hplus : 0 ≤ mu + nu) (hminus : 0 ≤ mu - nu)
    (chart : ConstitutiveChart Current)
    (u : Cut) (f : Face) (j : Current) :
    fineLaw tau mu nu chart.J chart.D chart.Dt j
      (currentStep chart tau mu nu u f j) u f := by
  have hfine := decodedCurrent_explicitUpdate_solves_fine
    htau hplus hminus chart.J chart.D chart.Dt
    (extractedCut chart j) u (extractedFace chart j) f
    (extractedResidual chart j) chart.DtJ chart.DtD
    (extractedResidual_face_zero chart j)
  rw [decode_extractedCurrent_exact chart j] at hfine
  simpa [currentStep] using hfine

theorem reducedScaleTransport_currentStep_square
    {Source Target : Type*}
    [AddCommGroup Source] [Module ℚ Source]
    [AddCommGroup Target] [Module ℚ Target]
    (source : ConstitutiveChart Source) (target : ConstitutiveChart Target)
    (tau mu nu : ℚ) (u : Cut) (f : Face) (j : Source) :
    reducedScaleTransport source target
        (currentStep source tau mu nu u f j) =
      currentStep target tau mu nu u f
        (reducedScaleTransport source target j) := by
  have hsourceCut := currentStep_cut source tau mu nu u f j
  have hsourceFace := currentStep_face source tau mu nu u f j
  have hread := reducedRead_scaleTransport source target j
  have htargetCut :
      extractedCut target (reducedScaleTransport source target j) =
        extractedCut source j := congrArg Prod.fst hread
  have htargetFace :
      extractedFace target (reducedScaleTransport source target j) =
        extractedFace source j := congrArg Prod.snd hread
  have htargetResidual :
      extractedResidual target (reducedScaleTransport source target j) = 0 := by
    simpa [reducedScaleTransport, decodedZero] using
      extractedCurrent_residual_zero target
        (extractedCut source j) (extractedFace source j)
  change decodedZero target
      (extractedCut source (currentStep source tau mu nu u f j))
      (extractedFace source (currentStep source tau mu nu u f j)) =
    currentStep target tau mu nu u f
      (reducedScaleTransport source target j)
  rw [hsourceCut, hsourceFace]
  unfold currentStep
  rw [htargetCut, htargetFace, htargetResidual]
  simp [decodedZero]

theorem reducedScaleTransport_currentStep_target_residual_zero
    {Source Target : Type*}
    [AddCommGroup Source] [Module ℚ Source]
    [AddCommGroup Target] [Module ℚ Target]
    (source : ConstitutiveChart Source) (target : ConstitutiveChart Target)
    (tau mu nu : ℚ) (u : Cut) (f : Face) (j : Source) :
    extractedResidual target
        (reducedScaleTransport source target
          (currentStep source tau mu nu u f j)) = 0 := by
  unfold reducedScaleTransport
  exact extractedCurrent_residual_zero target _ _

theorem decodedCurrent_fineLaw_of_compact
    {tau mu nu : ℚ} (chart : ConstitutiveChart Current)
    (q u : Cut) (z f z' : Face) (r : Current)
    (hblind : chart.Dt r = 0)
    (hcompact : compactLaw tau mu nu q u f z z') :
    fineLaw tau mu nu chart.J chart.D chart.Dt
      (decodedCurrent chart.J chart.D q z r)
      (decodedCurrent chart.J chart.D (q + u) z' r) u f := by
  exact decodedCurrent_compact_solves_fine
    chart.J chart.D chart.Dt q u z f z' r chart.DtJ chart.DtD hblind hcompact

end Soma.Holonics.Physics.ConstitutiveCurrentReduction

section Audit
open Soma.Holonics.Physics.ConstitutiveCurrentReduction
#print axioms faceMetricInverse_faceMetric
#print axioms extractedResidual_cut_zero
#print axioms extractedResidual_face_zero
#print axioms decode_extractedCurrent_exact
#print axioms reducedRead_decodedZero
#print axioms reducedScaleTransport_on_decodedZero
#print axioms reducedRead_scaleTransport
#print axioms currentStep_cut
#print axioms currentStep_face
#print axioms currentStep_residual
#print axioms currentStep_solves_fine
#print axioms reducedScaleTransport_currentStep_square
#print axioms reducedScaleTransport_currentStep_target_residual_zero
#print axioms decodedCurrent_fineLaw_of_compact
end Audit
