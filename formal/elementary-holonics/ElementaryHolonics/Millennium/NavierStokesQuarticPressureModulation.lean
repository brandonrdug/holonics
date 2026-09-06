import ElementaryHolonics.Millennium.NavierStokesPressureJetReceivers
import ElementaryHolonics.Millennium.NavierStokesAnisotropicViscousClock
import ElementaryHolonics.Millennium.NavierStokesAnisotropicQuarticCurrent

/-!
# Quartic pressure modulation follows the actual source

Five addressed Taylor coefficients split into two Poisson-source coefficients and three
harmonic force coefficients. In the diagonal frame they have two factored weights. Their
time derivative is obtained from the actual pressure source, with the physical clock retained.
Reconstruction of an entire quartic from these five coefficients requires its declared symmetry
family; the general pressure-word receiver retains every other addressed derivative.
-/

noncomputable section
open Function Set Filter
open scoped Topology NNReal

namespace Soma.Holonics.Millennium.NavierStokesQuarticPressureModulation
open Soma.Holonics.Millennium.NavierStokes
open Soma.Holonics.Millennium.NavierStokesWeightedSobolevHilbert
open Soma.Holonics.Millennium.NavierStokesWeightedPathSpace
open Soma.Holonics.Millennium.NavierStokesWeightedSmoothPathTower
open Soma.Holonics.Millennium.NavierStokesWeightedMildRestart
open Soma.Holonics.Millennium.NavierStokesWeightedPathInvariants
open Soma.Holonics.Millennium.NavierStokesWeightedReality
open Soma.Holonics.Millennium.NavierStokesWeightedPressureTimeSmoothness
open Soma.Holonics.Millennium.NavierStokesPressureEvolution
open Soma.Holonics.Millennium.NavierStokesPressureJetReceivers
open Soma.Holonics.Millennium.NavierStokesAnisotropicViscousClock
open Soma.Holonics.Millennium.NavierStokesAnisotropicFrame
open Soma.Holonics.Millennium.NavierStokesAxisymmetricChart
open Soma.Holonics.Millennium.NavierStokesQuarticPressureCurrent
open Soma.Holonics.Millennium.NavierStokesAnisotropicQuarticCurrent

abbrev QuarticCoefficients := Fin 5 → ℝ

/-- Raw coefficients are addressed as `(x⁴+y⁴, x²y², (x²+y²)z², z⁴, xy(x²-y²))`. -/
def rawQuarticReceiver (x : Space) : Fin 5 → (PeriodicWeightedSobolev 7 →L[ℝ] ℝ) :=
  ![(1 / 24 : ℝ) • pressureWordReceiver 4 4 (by omega) ![0, 0, 0, 0] x,
    (1 / 4 : ℝ) • pressureWordReceiver 4 4 (by omega) ![0, 0, 1, 1] x,
    (1 / 4 : ℝ) • pressureWordReceiver 4 4 (by omega) ![0, 0, 2, 2] x,
    (1 / 24 : ℝ) • pressureWordReceiver 4 4 (by omega) ![2, 2, 2, 2] x,
    (1 / 6 : ℝ) • pressureWordReceiver 4 4 (by omega) ![0, 0, 0, 1] x]

/-- `(L,M,kappa,b,c)` retains the trace/source part and the harmonic force amplitudes. -/
def adaptedCoefficients (epsilon : ℝ) (v : QuarticCoefficients) : QuarticCoefficients :=
  ![(6 * v 0 + v 1 - 3 * epsilon ^ 2 * v 3) / 8,
    v 2 + 3 * epsilon * v 3, epsilon * v 3, (2 * v 0 - v 1) / 8, v 4]

def adaptedReceiverFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : Fin 5 → (E →L[ℝ] ℝ)) : Fin 5 → (E →L[ℝ] ℝ) :=
  ![(1 / 8 : ℝ) • (6 • R 0 + R 1 - 3 • R 3),
    R 2 + 3 • R 3, R 3, (1 / 8 : ℝ) • (2 • R 0 - R 1), R 4]

theorem adaptedReceiverFamily_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (R : Fin 5 → (E →L[ℝ] ℝ)) (v : E) (i : Fin 5) :
    adaptedReceiverFamily R i v = adaptedCoefficients 1 (fun j ↦ R j v) i := by
  fin_cases i <;> simp [adaptedReceiverFamily, adaptedCoefficients] <;> ring

def adaptedPressureReceiver (x : Space) : Fin 5 → (PeriodicWeightedSobolev 7 →L[ℝ] ℝ) :=
  adaptedReceiverFamily (rawQuarticReceiver x)

theorem adaptedPressureReceiver_apply (x : Space) (state : PeriodicWeightedSobolev 7) (i : Fin 5) :
    adaptedPressureReceiver x i state =
      adaptedCoefficients 1 (fun j ↦ rawQuarticReceiver x j state) i :=
  adaptedReceiverFamily_apply (rawQuarticReceiver x) state i

def horizontalWeight (r K : ℝ) : ℝ := r ^ 6 / K ^ 2
def mixedWeight (r z K : ℝ) : ℝ := r ^ 4 * z ^ 2 / K ^ 2

def frameWeights (r z K : ℝ) : QuarticCoefficients :=
  ![horizontalWeight r K, mixedWeight r z K, mixedWeight r z K,
    horizontalWeight r K, horizontalWeight r K]

def frameRates (r z rJet zJet : ℝ) : QuarticCoefficients :=
  ![6 * rJet / r, 4 * rJet / r + 2 * zJet / z, 4 * rJet / r + 2 * zJet / z,
    6 * rJet / r, 6 * rJet / r]

def rawFrameCoefficients (r z K : ℝ) (v : QuarticCoefficients) : QuarticCoefficients :=
  ![r ^ 6 / K ^ 2 * v 0, r ^ 6 / K ^ 2 * v 1,
    r ^ 4 * z ^ 2 / K ^ 2 * v 2, r ^ 2 * z ^ 4 / K ^ 2 * v 3,
    r ^ 6 / K ^ 2 * v 4]

/-- These weights come from the actual diagonal pullback of the quartic polynomial. The
polynomial variable is displacement from its fixed Taylor centre. -/
theorem fiveTermQuarticPressure_frame_pullback (r z K : ℝ) (hK : K ≠ 0)
    (v : QuarticCoefficients) (x : Space) :
    (r / K) ^ 2 * fiveTermQuarticPressure (v 0) (v 1) (v 2) (v 3) (v 4)
        (diagonalFrame r z x) =
      fiveTermQuarticPressure
        (rawFrameCoefficients r z K v 0) (rawFrameCoefficients r z K v 1)
        (rawFrameCoefficients r z K v 2) (rawFrameCoefficients r z K v 3)
        (rawFrameCoefficients r z K v 4) x := by
  rw [diagonalFrame_apply]
  simp [fiveTermQuarticPressure, rawFrameCoefficients, radiusSq, Hsin, assemble]
  field_simp <;> ring

/-- The adapted force/source chart diagonalizes the actual quartic frame weights. No inverse
aspect factor occurs in the returned coefficients. -/
theorem adaptedCoefficients_frame_transport (r z K : ℝ) (hz : z ≠ 0) (hK : K ≠ 0)
    (v : QuarticCoefficients) :
    adaptedCoefficients (aspect r z) (rawFrameCoefficients r z K v) =
      fun i ↦ frameWeights r z K i * adaptedCoefficients 1 v i := by
  funext i
  fin_cases i <;>
    simp [adaptedCoefficients, aspect, rawFrameCoefficients, frameWeights,
      horizontalWeight, mixedWeight] <;> field_simp <;> ring

theorem fiveTerm_force_eq_adapted (epsilon : ℝ) (v : QuarticCoefficients) (y : Space) :
    -diagonalFrame 1 epsilon
        (gradient (fiveTermQuarticPressure (v 0) (v 1) (v 2) (v 3) (v 4)) y) =
      fullQuarticPressureForce epsilon
        (adaptedCoefficients epsilon v 0) (adaptedCoefficients epsilon v 1)
        (adaptedCoefficients epsilon v 2) (adaptedCoefficients epsilon v 3)
        (adaptedCoefficients epsilon v 4) y := by
  have heq : fiveTermQuarticPressure (v 0) (v 1) (v 2) (v 3) (v 4) =
      fun x ↦ quarticTracePressure ((6 * v 0 + v 1 - 3 * epsilon ^ 2 * v 3) / 8)
          (v 2 + 3 * epsilon * v 3) x +
        anisotropicQuarticPressure epsilon (v 3) ((2 * v 0 - v 1) / 8) (v 4) x := by
    funext x
    simpa only [quarticTracePressure, anisotropicQuarticPressure, add_assoc] using
      fiveTermQuarticPressure_split (v 0) (v 1) (v 2) (v 3) (v 4) epsilon x
  rw [heq, fullQuarticPressureForce_eq_negative_gradient]
  rfl

theorem frame_force_eq_actual_pullback (r z K : ℝ) (hz : z ≠ 0) (hK : K ≠ 0)
    (v : QuarticCoefficients) (y : Space) :
    let C := fun i ↦ frameWeights r z K i * adaptedCoefficients 1 v i
    fullQuarticPressureForce (aspect r z) (C 0) (C 1) (C 2) (C 3) (C 4) y =
      -diagonalFrame 1 (aspect r z)
        (gradient (fun x ↦ (r / K) ^ 2 *
          fiveTermQuarticPressure (v 0) (v 1) (v 2) (v 3) (v 4) (diagonalFrame r z x)) y) := by
  dsimp only
  have heq := funext (fiveTermQuarticPressure_frame_pullback r z K hK v)
  rw [heq, fiveTerm_force_eq_adapted, adaptedCoefficients_frame_transport r z K hz hK v]


theorem horizontalWeight_hasDerivAt (r : ℝ → ℝ) (K rJet τ : ℝ)
    (hr : HasDerivAt r rJet τ) (hrne : r τ ≠ 0) :
    HasDerivAt (fun σ ↦ horizontalWeight (r σ) K)
      ((6 * rJet / r τ) * horizontalWeight (r τ) K) τ := by
  have h := (hr.pow 6).div_const (K ^ 2)
  convert h using 1 <;> first | rfl |
    (unfold horizontalWeight; field_simp [hrne]; ring)

theorem mixedWeight_hasDerivAt (r z : ℝ → ℝ) (K rJet zJet τ : ℝ)
    (hr : HasDerivAt r rJet τ) (hz : HasDerivAt z zJet τ)
    (hrne : r τ ≠ 0) (hzne : z τ ≠ 0) :
    HasDerivAt (fun σ ↦ mixedWeight (r σ) (z σ) K)
      ((4 * rJet / r τ + 2 * zJet / z τ) * mixedWeight (r τ) (z τ) K) τ := by
  have h := ((hr.pow 4).mul (hz.pow 2)).div_const (K ^ 2)
  convert h using 1 <;> first | rfl |
    (simp only [Pi.pow_apply, Pi.mul_apply]; unfold mixedWeight; field_simp [hrne, hzne]; ring)

theorem frameWeights_hasDerivAt (r z : ℝ → ℝ) (K rJet zJet τ : ℝ)
    (hr : HasDerivAt r rJet τ) (hz : HasDerivAt z zJet τ)
    (hrne : r τ ≠ 0) (hzne : z τ ≠ 0) (i : Fin 5) :
    HasDerivAt (fun σ ↦ frameWeights (r σ) (z σ) K i)
      (frameRates (r τ) (z τ) rJet zJet i * frameWeights (r τ) (z τ) K i) τ := by
  fin_cases i
  all_goals first
  | exact horizontalWeight_hasDerivAt r K rJet τ hr hrne
  | exact mixedWeight_hasDerivAt r z K rJet zJet τ hr hz hrne hzne

def modulatedPressureCoefficient
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (r z clock : ℝ → ℝ)
    (K : ℝ) (x : Space) (i : Fin 5) (τ : ℝ) : ℝ :=
  frameWeights (r τ) (z τ) K i *
    adaptedPressureReceiver x i (nativePressureExtensionAtOrder hT tower 4 (clock τ))

/-- The actual pressure time source and physical clock drive every adapted quartic coefficient. -/
theorem modulatedPressureCoefficient_hasDerivAt
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (r z clock : ℝ → ℝ) (K : ℝ) (x : Space) (i : Fin 5) (τ rJet zJet : ℝ)
    (ht : clock τ ∈ Ioo (0 : ℝ) T)
    (hr : HasDerivAt r rJet τ) (hz : HasDerivAt z zJet τ)
    (hclock : HasDerivAt clock (clockRate K (r τ)) τ)
    (hrne : r τ ≠ 0) (hzne : z τ ≠ 0) :
    HasDerivAt (modulatedPressureCoefficient hT tower r z clock K x i)
      (frameRates (r τ) (z τ) rJet zJet i *
          modulatedPressureCoefficient hT tower r z clock K x i τ +
        clockRate K (r τ) * frameWeights (r τ) (z τ) K i *
          adaptedPressureReceiver x i (pressureTimeJetAtOrder hT tower nu 4 (clock τ))) τ := by
  have hp : HasDerivAt (nativePressureExtensionAtOrder hT tower 4)
      (pressureTimeJetAtOrder hT tower nu 4 (clock τ)) (clock τ) :=
    hasDerivAt_nativePressureExtensionAtOrder hT tower nu hnu initial hfixed hreal 4 ht
  have hL : HasDerivAt
      (fun t ↦ adaptedPressureReceiver x i (nativePressureExtensionAtOrder hT tower 4 t))
      (adaptedPressureReceiver x i (pressureTimeJetAtOrder hT tower nu 4 (clock τ))) (clock τ) := by
    simpa only [ContinuousLinearMap.zero_apply, zero_add] using
      (hasDerivAt_const (clock τ) (adaptedPressureReceiver x i)).clm_apply hp
  have hsource := hL.comp τ hclock
  have hweight := frameWeights_hasDerivAt r z K rJet zJet τ hr hz hrne hzne i
  have h := hweight.fun_mul hsource
  convert h using 1 <;> first | rfl | (simp only [Function.comp_apply]; unfold modulatedPressureCoefficient; ring)

/-- The same modulation reaches the initial face when the actual clock maps the declared
half-open chart aperture into the physical solution aperture. -/
theorem modulatedPressureCoefficient_hasDerivWithinAt_Ico
    {T S : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (r z clock : ℝ → ℝ) (K : ℝ) (x : Space) (i : Fin 5) (τ rJet zJet : ℝ)
    (hτ : τ ∈ Ico (0 : ℝ) S) (hmaps : MapsTo clock (Ico (0 : ℝ) S) (Ico (0 : ℝ) T))
    (hr : HasDerivAt r rJet τ) (hz : HasDerivAt z zJet τ)
    (hclock : HasDerivWithinAt clock (clockRate K (r τ)) (Ico (0 : ℝ) S) τ)
    (hrne : r τ ≠ 0) (hzne : z τ ≠ 0) :
    HasDerivWithinAt (modulatedPressureCoefficient hT tower r z clock K x i)
      (frameRates (r τ) (z τ) rJet zJet i *
          modulatedPressureCoefficient hT tower r z clock K x i τ +
        clockRate K (r τ) * frameWeights (r τ) (z τ) K i *
          adaptedPressureReceiver x i (pressureTimeJetAtOrder hT tower nu 4 (clock τ)))
      (Ico (0 : ℝ) S) τ := by
  have hp := hasDerivWithinAt_nativePressureExtensionAtOrder_Ico
    hT tower nu hnu initial hfixed hreal 4 (hmaps hτ)
  have hL : HasDerivWithinAt
      (fun t ↦ adaptedPressureReceiver x i (nativePressureExtensionAtOrder hT tower 4 t))
      (adaptedPressureReceiver x i (pressureTimeJetAtOrder hT tower nu 4 (clock τ)))
      (Ico (0 : ℝ) T) (clock τ) := by
    have h :=
      (hasDerivWithinAt_const (clock τ) (Ico (0 : ℝ) T) (adaptedPressureReceiver x i)).clm_apply hp
    simp only [ContinuousLinearMap.zero_apply, zero_add] at h
    convert h using 1 <;> rfl
  have hsource := hL.comp τ hclock hmaps
  have hweight : HasDerivWithinAt (fun σ ↦ frameWeights (r σ) (z σ) K i)
      (frameRates (r τ) (z τ) rJet zJet i * frameWeights (r τ) (z τ) K i)
      (Ico (0 : ℝ) S) τ :=
    (frameWeights_hasDerivAt r z K rJet zJet τ hr hz hrne hzne i).hasDerivWithinAt
  have h := hweight.fun_mul hsource
  convert h using 1 <;> first | rfl | (simp only [Function.comp_apply]; unfold modulatedPressureCoefficient; ring)

def modulatedPressureCoefficientRate
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (nu : ℝ≥0) (r z clock : ℝ → ℝ)
    (K : ℝ) (centre : Space) (i : Fin 5) (τ rJet zJet : ℝ) : ℝ :=
  frameRates (r τ) (z τ) rJet zJet i *
      modulatedPressureCoefficient hT tower r z clock K centre i τ +
    clockRate K (r τ) * frameWeights (r τ) (z τ) K i *
      adaptedPressureReceiver centre i (pressureTimeJetAtOrder hT tower nu 4 (clock τ))

/-- The full force of the declared five-coefficient quartic pressure chart. -/
def sourcedQuarticPressureForce
    {T : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base) (r z clock : ℝ → ℝ)
    (K : ℝ) (centre : Space) : VelocityField := fun y τ ↦
  let C := fun i ↦ modulatedPressureCoefficient hT tower r z clock K centre i τ
  fullQuarticPressureForce (aspect (r τ) (z τ)) (C 0) (C 1) (C 2) (C 3) (C 4) y

/-- Both source coefficients, all harmonic coefficients, and the moving-basis connection
receive the same actual pressure time source, including at the initial right face. -/
theorem sourcedQuarticPressureForce_hasDerivWithinAt_Ico
    {T S : ℝ} (hT : 0 ≤ T) {base : WeightedH3Path T}
    (tower : CoherentWeightedSmoothPathTower base)
    (nu : ℝ≥0) (hnu : 0 < (nu : ℝ)) (initial : PeriodicVectorWeightedSobolev 3)
    (hfixed : IsFixedPt (weightedMildMap nu hnu hT initial) base)
    (hreal : IsWeightedFourierRealPath base)
    (r z clock : ℝ → ℝ) (K : ℝ) (centre y : Space) (τ rJet zJet : ℝ)
    (hτ : τ ∈ Ico (0 : ℝ) S) (hmaps : MapsTo clock (Ico (0 : ℝ) S) (Ico (0 : ℝ) T))
    (hr : HasDerivAt r rJet τ) (hz : HasDerivAt z zJet τ)
    (hclock : HasDerivWithinAt clock (clockRate K (r τ)) (Ico (0 : ℝ) S) τ)
    (hrne : r τ ≠ 0) (hzne : z τ ≠ 0) :
    let C := fun i ↦ modulatedPressureCoefficient hT tower r z clock K centre i τ
    let R := fun i ↦ modulatedPressureCoefficientRate hT tower nu r z clock K centre i τ rJet zJet
    let epsilon := aspect (r τ) (z τ)
    let epsilonJet := 2 * (rJet / r τ - zJet / z τ) * epsilon
    HasDerivWithinAt (sourcedQuarticPressureForce hT tower r z clock K centre y)
      (fullQuarticPressureForce epsilon (R 0) (R 1) (R 2) (R 3) (R 4) y +
        epsilonJet • (C 1 • mixedTraceConnection y + C 2 • axialFrameCurrent y))
      (Ico (0 : ℝ) S) τ := by
  dsimp only
  have hC (i : Fin 5) : HasDerivWithinAt
      (modulatedPressureCoefficient hT tower r z clock K centre i)
      (modulatedPressureCoefficientRate hT tower nu r z clock K centre i τ rJet zJet)
      (Ico (0 : ℝ) S) τ :=
    modulatedPressureCoefficient_hasDerivWithinAt_Ico hT tower nu hnu initial hfixed hreal
      r z clock K centre i τ rJet zJet hτ hmaps hr hz hclock hrne hzne
  have he : HasDerivWithinAt (fun t ↦ aspect (r t) (z t))
      (2 * (rJet / r τ - zJet / z τ) * aspect (r τ) (z τ)) (Ico (0 : ℝ) S) τ := by
    convert (aspect_hasDerivAt r z rJet zJet τ hr hz hrne hzne).hasDerivWithinAt
      (s := Ico (0 : ℝ) S) using 1 <;> rfl
  exact fullQuarticPressureForce_hasDerivWithinAt
    (fun t ↦ aspect (r t) (z t))
    (modulatedPressureCoefficient hT tower r z clock K centre 0)
    (modulatedPressureCoefficient hT tower r z clock K centre 1)
    (modulatedPressureCoefficient hT tower r z clock K centre 2)
    (modulatedPressureCoefficient hT tower r z clock K centre 3)
    (modulatedPressureCoefficient hT tower r z clock K centre 4)
    (Ico (0 : ℝ) S) τ _ _ _ _ _ _ he (hC 0) (hC 1) (hC 2) (hC 3) (hC 4) y

#print axioms adaptedPressureReceiver_apply
#print axioms fiveTermQuarticPressure_frame_pullback
#print axioms adaptedCoefficients_frame_transport
#print axioms frame_force_eq_actual_pullback
#print axioms frameWeights_hasDerivAt
#print axioms modulatedPressureCoefficient_hasDerivAt
#print axioms modulatedPressureCoefficient_hasDerivWithinAt_Ico
#print axioms sourcedQuarticPressureForce_hasDerivWithinAt_Ico
end Soma.Holonics.Millennium.NavierStokesQuarticPressureModulation
