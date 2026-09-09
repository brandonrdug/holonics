import ElementaryHolonics.Physics.FourTorusTwoFace
import ElementaryHolonics.Physics.CoupledIncidence
import ElementaryHolonics.Physics.ConstitutiveScale

/-!
# The active torus current in the existing coupled Parametron response

The physical response owner is real-valued. This chart casts the exact rational branch-current
coordinates into that owner, using the two actual square currents as its incidence rows. The
result identifies the finite algebraic response `D M Dᵀ j`. It supplies no units or claim that
this first-order constitutive law is the complete second-order LC or phase-locking dynamics.
-/

namespace Soma.Holonics.Physics.FourTorusParametronCurrent

noncomputable section

open scoped BigOperators
open Soma.Holonics.Physics.FourTorusCurrentChart
open Soma.Holonics.Physics.FourTorusTwoFace
open Soma.Holonics.Physics.TwoFaceConstitutive
open Soma.Holonics.Millennium.HolonicFourTorusCarrier
open Soma.Holonics.Millennium.HolonicComplexParametron

def realCurrent (current : RationalCurrent grain) : Edge grain → ℝ :=
  fun edge ↦ (current edge : ℝ)

def activeIncidence (grain : ℕ) : Fin 2 → Edge grain → ℝ :=
  ![fun edge ↦ (c0 grain edge : ℝ), fun edge ↦ (c1 grain edge : ℝ)]

def activeMaterial (mu nu : ℚ) : Fin 2 → Fin 2 → ℝ :=
  ![![(mu : ℝ), (nu : ℝ)], ![(nu : ℝ), (mu : ℝ)]]

theorem branchDrop_activeIncidence (grain : ℕ) (current : RationalCurrent grain)
    (face : Fin 2) :
    branchDrop (activeIncidence grain) (realCurrent current) face =
      ((twoFaceTranspose grain current face : ℚ) : ℝ) := by
  fin_cases face <;>
    simp [branchDrop, activeIncidence, realCurrent, twoFaceTranspose, mul_comm]

theorem coupledResponse_current (grain : ℕ) (mu nu : ℚ)
    (current : RationalCurrent grain) (edge : Edge grain) :
    coupledResponse (activeMaterial mu nu) (activeIncidence grain)
      (realCurrent current) edge =
      ((twoFace grain (materialMap mu nu (twoFaceTranspose grain current)) edge : ℚ) : ℝ) := by
  simp only [coupledResponse, branchDrop_activeIncidence, Fin.sum_univ_two]
  simp [activeMaterial, activeIncidence, twoFace, materialMap]
  ring

/-! ## The concrete current, clocked tube and scale construction -/

open Soma.Holonics.Physics.ConstitutiveCurrentReduction
open Soma.Holonics.Physics.ConstitutiveWorldTube
open Soma.Holonics.Physics.ConstitutiveScale
open Soma.Holonics.Millennium.HolonicGranularBoundaryRadiation

/-- Both grains use their actual proved square/winding chart. This is a receiver quotient
passage; the source's cold residual remains a source fibre, not a geometric refinement map. -/
def currentScalePassage (sourceGrain targetGrain : ℕ)
    (sourceAdmitted : sourceGrain = 1 ∨ sourceGrain = 2)
    (targetAdmitted : targetGrain = 1 ∨ targetGrain = 2) :
    BoundaryScalePassage ℚ (RationalCurrent sourceGrain) ReducedFace
      (RationalCurrent targetGrain) ReducedFace :=
  scalePassage (constitutiveChart sourceGrain sourceAdmitted)
    (constitutiveChart targetGrain targetAdmitted)

theorem currentScalePassage_input_square (sourceGrain targetGrain : ℕ)
    (sourceAdmitted : sourceGrain = 1 ∨ sourceGrain = 2)
    (targetAdmitted : targetGrain = 1 ∨ targetGrain = 2)
    (input : Input) (current : RationalCurrent sourceGrain) :
    (currentScalePassage sourceGrain targetGrain sourceAdmitted targetAdmitted).interiorTransport
        (inputSourceTransport (constitutiveChart sourceGrain sourceAdmitted) input current) =
      inputSourceTransport (constitutiveChart targetGrain targetAdmitted) input
        ((currentScalePassage sourceGrain targetGrain sourceAdmitted targetAdmitted).interiorTransport
          current) := by
  simpa only [currentScalePassage, scalePassage, scaleLinear_apply, inputSourceTransport] using
    reducedScaleTransport_currentStep_square
      (constitutiveChart sourceGrain sourceAdmitted)
      (constitutiveChart targetGrain targetAdmitted)
      input.tau input.mu input.nu input.u input.f current

/-- An actual complete branch current supplies the entire initial tube state by exact extraction. -/
def clockedCurrent (grain : ℕ) (admitted : grain = 1 ∨ grain = 2)
    (input : Input) (current : RationalCurrent grain) (clock : ℚ) :=
  let chart := constitutiveChart grain admitted
  actualSpan chart input
    (extractedCut chart current, extractedFace chart current, extractedResidual chart current, clock)
    (extractedResidual_cut_zero chart current) (extractedResidual_face_zero chart current)

/-- The concrete torus current inherits the complete admitted input-word receiver family. -/
def currentHistory (grain : ℕ) (admitted : grain = 1 ∨ grain = 2) :=
  inputHistoryCompression (constitutiveChart grain admitted)

end

#print axioms branchDrop_activeIncidence
#print axioms coupledResponse_current
#print axioms currentScalePassage_input_square
#print axioms clockedCurrent
#print axioms currentHistory

end Soma.Holonics.Physics.FourTorusParametronCurrent
