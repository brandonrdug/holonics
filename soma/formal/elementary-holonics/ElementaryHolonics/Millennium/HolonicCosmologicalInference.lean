import ElementaryHolonics.Millennium.HolonicTypedOriginDimensions

/-!
# Exact cosmological-inference receivers

**[proved-derived]** A reported cosmological constant is ordinarily not a direct local reading.
Within a constant-`Λ` expansion chart it is the nonlinear receiver

`Λ = 3 * Ω_Λ * H₀² / c²`.

This file retains the two expansion-rate occurrences in the dimension ledger, constructs the
nonlinear reconstruction fibre of this receiver, and proves that the receiver is not injective.
It also gives an exact finite pushforward for rationally weighted parameter populations: total
weight is conserved before a later summary collapses the returned `Λ` population to a centre and
band.

No decimal in this file is a floating-point quantity.  `ExactDecimal` records an exterior decimal
report as an exact rational coordinate together with the radix depth that produced it.  This makes
the paper's printed coordinate exact without claiming that the underlying physical parameter has
thereby been known exactly.
-/

noncomputable section

namespace Soma.Holonics.Millennium.HolonicCosmologicalInference

open Soma.Holonics.Millennium.HolonicTypedOriginDimensions

/-! ## The typed origin of the inverse-area reading -/

def sourceHubbleDim : OriginDim := -sourceTimeDim
def receiverHubbleDim : OriginDim := -receiverTimeDim

/-- The two factors in `H₀²` remain distinct addressed rate occurrences before symmetrization. -/
def hubbleProductDim : OriginDim := sourceHubbleDim + receiverHubbleDim

/-- The dimension returned by `H₀² / c²`; `Ω_Λ` and the coefficient three are dimensionless. -/
def lambdaInferenceDim : OriginDim := hubbleProductDim - speedSquaredDim

theorem lambdaInferenceDim_eq_cosmologicalConstantDim :
    lambdaInferenceDim = cosmologicalConstantDim := by
  funext axis
  cases axis with
  | length =>
      simp [lambdaInferenceDim, hubbleProductDim, sourceHubbleDim,
        receiverHubbleDim, speedSquaredDim, sourceSpeedDim, receiverSpeedDim,
        cosmologicalConstantDim, curvatureDim, lengthDim, sourceTimeDim,
        receiverTimeDim, axisDim]
  | mass =>
      simp [lambdaInferenceDim, hubbleProductDim, sourceHubbleDim,
        receiverHubbleDim, speedSquaredDim, sourceSpeedDim, receiverSpeedDim,
        cosmologicalConstantDim, curvatureDim, lengthDim, sourceTimeDim,
        receiverTimeDim, axisDim]
  | time origin =>
      cases origin <;>
        simp [lambdaInferenceDim, hubbleProductDim, sourceHubbleDim,
          receiverHubbleDim, speedSquaredDim, sourceSpeedDim, receiverSpeedDim,
          cosmologicalConstantDim, curvatureDim, lengthDim, sourceTimeDim,
          receiverTimeDim, axisDim]

/-! ## Exact exterior decimal reports -/

/-- An exact radix-ten coordinate as printed by an exterior source.  The radix depth is retained. -/
structure ExactDecimal where
  mantissa : ℤ
  radixDepth : ℕ
  deriving DecidableEq, Repr

def ExactDecimal.coordinate (report : ExactDecimal) : ℚ :=
  report.mantissa / (10 : ℚ) ^ report.radixDepth

/-- A paper's asymmetric three-coordinate summary, kept distinct from its full inference fibre. -/
structure ExactReportedBand where
  centre : ExactDecimal
  lowerWidth : ExactDecimal
  upperWidth : ExactDecimal
  deriving DecidableEq, Repr

/-- A typed exact interval whose origin retains the dataset/chart/model/joint-cell lineage. -/
structure QuantityBand (Origin : Type*) (dimension : OriginDim) where
  origin : Origin
  lower : ℚ
  upper : ℚ
  lower_le_upper : lower ≤ upper

abbrev CosmologicalConstantBand (Origin : Type*) :=
  QuantityBand Origin cosmologicalConstantDim

/-! ## The constant-`Λ` parameter receiver and its retained fibre -/

abbrev ExpansionParameters := ℚ × ℚ

/-- `parameters.1` is the Hubble-rate coordinate and `parameters.2` is `Ω_Λ`.
The nonzero light-speed coordinate is supplied by the surrounding calibrated chart. -/
def lambdaReceiver (lightSpeed : ℚ) (parameters : ExpansionParameters) : ℚ :=
  3 * parameters.2 * parameters.1 ^ 2 / lightSpeed ^ 2

abbrev LambdaReconstructionFibre (lightSpeed reading : ℚ) :=
  {parameters : ExpansionParameters // lambdaReceiver lightSpeed parameters = reading}

def omegaLambdaFromLambda (lightSpeed hubble lambda : ℚ) : ℚ :=
  lambda * lightSpeed ^ 2 / (3 * hubble ^ 2)

theorem omegaLambdaFromLambda_lambdaReceiver
    (lightSpeed hubble omegaLambda : ℚ)
    (hLight : lightSpeed ≠ 0) (hHubble : hubble ≠ 0) :
    omegaLambdaFromLambda lightSpeed hubble
        (lambdaReceiver lightSpeed (hubble, omegaLambda)) = omegaLambda := by
  unfold omegaLambdaFromLambda lambdaReceiver
  apply (div_eq_iff (mul_ne_zero (by norm_num) (pow_ne_zero 2 hHubble))).2
  field_simp [hLight]

/-- Scaling the rate by `scale` and the density fraction by `scale⁻²` stays in one exact
`Λ` reconstruction fibre. -/
theorem lambdaReceiver_scale_fibre
    (lightSpeed hubble omegaLambda scale : ℚ) (hScale : scale ≠ 0) :
    lambdaReceiver lightSpeed (scale * hubble, omegaLambda / scale ^ 2) =
      lambdaReceiver lightSpeed (hubble, omegaLambda) := by
  have numerator :
      3 * (omegaLambda / scale ^ 2) * (scale * hubble) ^ 2 =
        3 * omegaLambda * hubble ^ 2 := by
    field_simp [hScale]
  simpa [lambdaReceiver] using congrArg (fun value : ℚ ↦ value / lightSpeed ^ 2) numerator

theorem lambdaReceiver_not_injective (lightSpeed : ℚ) :
    ¬ Function.Injective (lambdaReceiver lightSpeed) := by
  intro injective
  have sameReading :
    lambdaReceiver lightSpeed ((1 : ℚ), (1 : ℚ)) =
        lambdaReceiver lightSpeed ((2 : ℚ), (1 / 4 : ℚ)) := by
    unfold lambdaReceiver
    congr 1
    norm_num
  have sameParameters := injective sameReading
  have sameHubble := congrArg Prod.fst sameParameters
  norm_num at sameHubble

/-- The exact returned difference separates a rate-square change from a density-fraction change.
This is an algebraic ledger, not a first-order error propagation. -/
theorem lambdaDifference_decomposition
    (lightSpeed hubbleSource hubbleReceiver omegaSource omegaReceiver : ℚ) :
    lambdaReceiver lightSpeed (hubbleReceiver, omegaReceiver) -
        lambdaReceiver lightSpeed (hubbleSource, omegaSource) =
      (3 / lightSpeed ^ 2) *
        (omegaReceiver * (hubbleReceiver ^ 2 - hubbleSource ^ 2) +
          (omegaReceiver - omegaSource) * hubbleSource ^ 2) := by
  unfold lambdaReceiver
  ring

/-- The same total difference admits the complementary path ordering.  The two ledgers allocate
the interaction term differently but return one invariant exterior difference. -/
theorem lambdaDifference_decomposition_reversed
    (lightSpeed hubbleSource hubbleReceiver omegaSource omegaReceiver : ℚ) :
    lambdaReceiver lightSpeed (hubbleReceiver, omegaReceiver) -
        lambdaReceiver lightSpeed (hubbleSource, omegaSource) =
      (3 / lightSpeed ^ 2) *
        (omegaSource * (hubbleReceiver ^ 2 - hubbleSource ^ 2) +
          (omegaReceiver - omegaSource) * hubbleReceiver ^ 2) := by
  unfold lambdaReceiver
  ring

/-! ## Exact finite pushforward of a joint inference population -/

/-- Push an exact rational weight population through a receiver without choosing a mean, median,
maximum, Gaussian fit, or decimal rounding. -/
def pushforwardWeight {Sample Target : Type*} [Fintype Sample] [DecidableEq Target]
    (weight : Sample → ℚ) (target : Sample → Target) (reading : Target) : ℚ :=
  ∑ sample : Sample, if target sample = reading then weight sample else 0

theorem pushforwardWeight_total {Sample Target : Type*}
    [Fintype Sample] [Fintype Target] [DecidableEq Target]
    (weight : Sample → ℚ) (target : Sample → Target) :
    (∑ reading : Target, pushforwardWeight weight target reading) =
      ∑ sample : Sample, weight sample := by
  classical
  simp only [pushforwardWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  simp

/-- The same conservation theorem when the target type is not finite: sum only over the finite
image actually returned by this population. -/
theorem pushforwardWeight_total_on_image {Sample Target : Type*}
    [Fintype Sample] [DecidableEq Target]
    (weight : Sample → ℚ) (target : Sample → Target) :
    (∑ reading ∈ Finset.univ.image target, pushforwardWeight weight target reading) =
      ∑ sample : Sample, weight sample := by
  classical
  simp only [pushforwardWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  simp

def lambdaPushforwardWeight {Sample : Type*} [Fintype Sample]
    (weight : Sample → ℚ) (lightSpeed : ℚ)
    (parameters : Sample → ExpansionParameters) (reading : ℚ) : ℚ :=
  pushforwardWeight weight (lambdaReceiver lightSpeed ∘ parameters) reading

/-- The retained finite inference body.  `Dataset`, `UnitChart`, and `Model` remain type parameters
and stored occurrences; a sample is a complete admitted joint parameter/nuisance cell. -/
structure LambdaInferenceAtlas
    (Dataset UnitChart Model Sample : Type*) [Fintype Sample] where
  dataset : Dataset
  unitChart : UnitChart
  model : Model
  sampleWeight : Sample → ℚ
  lightSpeed : ℚ
  parameters : Sample → ExpansionParameters

def LambdaInferenceAtlas.lambdaWeight
    {Dataset UnitChart Model Sample : Type*} [Fintype Sample]
    (atlas : LambdaInferenceAtlas Dataset UnitChart Model Sample)
    (reading : ℚ) : ℚ :=
  lambdaPushforwardWeight atlas.sampleWeight atlas.lightSpeed atlas.parameters reading

theorem lambdaPushforwardWeight_total {Sample : Type*} [Fintype Sample]
    (weight : Sample → ℚ) (lightSpeed : ℚ)
    (parameters : Sample → ExpansionParameters) :
    (∑ reading ∈ Finset.univ.image (lambdaReceiver lightSpeed ∘ parameters),
        lambdaPushforwardWeight weight lightSpeed parameters reading) =
      ∑ sample : Sample, weight sample :=
  pushforwardWeight_total_on_image weight (lambdaReceiver lightSpeed ∘ parameters)

theorem LambdaInferenceAtlas.lambdaWeight_total
    {Dataset UnitChart Model Sample : Type*} [Fintype Sample]
    (atlas : LambdaInferenceAtlas Dataset UnitChart Model Sample) :
    (∑ reading ∈ Finset.univ.image
        (lambdaReceiver atlas.lightSpeed ∘ atlas.parameters),
        atlas.lambdaWeight reading) =
      ∑ sample : Sample, atlas.sampleWeight sample :=
  lambdaPushforwardWeight_total atlas.sampleWeight atlas.lightSpeed atlas.parameters

/-! ## Window gluing and the exact nonconstant remainder -/

def returnedLambdaDefect {Window : Type*} (lambdaSection : Window → ℚ)
    (source receiver : Window) : ℚ :=
  lambdaSection receiver - lambdaSection source

def GluesToConstant {Window : Type*} (lambdaSection : Window → ℚ) : Prop :=
  ∃ lambda, ∀ window, lambdaSection window = lambda

theorem gluesToConstant_iff_all_returned_defects_zero {Window : Type*}
    [Nonempty Window] (lambdaSection : Window → ℚ) :
    GluesToConstant lambdaSection ↔
      ∀ source receiver, returnedLambdaDefect lambdaSection source receiver = 0 := by
  constructor
  · rintro ⟨lambda, hLambda⟩ source receiver
    simp [returnedLambdaDefect, hLambda source, hLambda receiver]
  · intro defects
    let base : Window := Classical.choice (inferInstance : Nonempty Window)
    refine ⟨lambdaSection base, ?_⟩
    intro window
    have returned := defects base window
    simpa [returnedLambdaDefect, sub_eq_zero] using returned

end Soma.Holonics.Millennium.HolonicCosmologicalInference

section Audit
open Soma.Holonics.Millennium.HolonicCosmologicalInference
#print axioms lambdaInferenceDim_eq_cosmologicalConstantDim
#print axioms omegaLambdaFromLambda_lambdaReceiver
#print axioms lambdaReceiver_scale_fibre
#print axioms lambdaReceiver_not_injective
#print axioms lambdaDifference_decomposition
#print axioms lambdaDifference_decomposition_reversed
#print axioms pushforwardWeight_total
#print axioms pushforwardWeight_total_on_image
#print axioms lambdaPushforwardWeight_total
#print axioms LambdaInferenceAtlas.lambdaWeight_total
#print axioms gluesToConstant_iff_all_returned_defects_zero
end Audit
