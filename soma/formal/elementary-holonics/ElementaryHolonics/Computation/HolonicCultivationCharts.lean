import ElementaryHolonics.Computation.ErosAthenaNeuralObjects

/-!
# Industry cultivation mechanisms as bounded charts of returned morphology

Supervised objectives, policy returns, autoencoders, factorized overlays, and distillation do not
found separate native machines.  This file states the exact finite/chart obligations by which each
can participate in Eros cultivation.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicCultivationCharts

open Soma.Holonics.Computation.HolonicAdjointNormalization

universe uNative uLatent uMorphology uInput uHidden uOutput uSource uCandidate
  uQuery uReceiver uFace uAction uWorld uDifference

/-! ## Scalar objectives are receiver quotients -/

structure ScalarObjective (Native : Type uNative) where
  face : Native → ℝ

namespace ScalarObjective

variable {Native : Type uNative} (objective : ScalarObjective Native)

def reconstructionFibre (reading : ℝ) : Set Native :=
  {native | objective.face native = reading}

theorem no_complete_descent_of_separator
    {Complete : Type*} (complete : Native → Complete) {left right : Native}
    (sameFace : objective.face left = objective.face right)
    (separated : complete left ≠ complete right) :
    ¬ ∃ descend : ℝ → Complete, ∀ native, complete native = descend (objective.face native) := by
  rintro ⟨descend, factors⟩
  apply separated
  calc
    complete left = descend (objective.face left) := factors left
    _ = descend (objective.face right) := congrArg descend sameFace
    _ = complete right := (factors right).symm

end ScalarObjective

/-! ## Gradient-based optimization is one chart for proposing a morphology return -/

structure GradientProposal (Morphology : Type uMorphology)
    [AddCommGroup Morphology] [Module ℝ Morphology] where
  differential : Morphology → Module.Dual ℝ Morphology
  metric : Morphology → MetricGradientChart Morphology
  learningRate : ℝ

namespace GradientProposal

variable {Morphology : Type uMorphology}
  [AddCommGroup Morphology] [Module ℝ Morphology]
  (proposal : GradientProposal Morphology)

def candidate (morphology : Morphology) : Morphology :=
  morphology - proposal.learningRate •
    (proposal.metric morphology).gradient (proposal.differential morphology)

/-- The scalar differential does not become a vector until the declared metric raises it. -/
theorem candidate_is_metric_raised_return (morphology : Morphology) :
    proposal.candidate morphology = morphology - proposal.learningRate •
      (proposal.metric morphology).tangentToCotangent.symm
        (proposal.differential morphology) := rfl

end GradientProposal

/-! ## Autoencoding is a quotient with an explicit reconstruction fibre -/

structure AutoencodingChart (Native : Type uNative) (Latent : Type uLatent) where
  encode : Native → Latent
  decode : Latent → Native

namespace AutoencodingChart

variable {Native : Type uNative} {Latent : Type uLatent}
  (chart : AutoencodingChart Native Latent)

def reconstructionFibre (latent : Latent) : Set Native :=
  {native | chart.encode native = latent}

def ExactOn (region : Set Native) : Prop :=
  ∀ native, native ∈ region → chart.decode (chart.encode native) = native

/-- Any pair collapsed by the encoder prevents exact reconstruction on a region containing both. -/
theorem collapsed_pair_obstructs_exact_reconstruction
    (region : Set Native) {left right : Native}
    (leftIn : left ∈ region) (rightIn : right ∈ region)
    (collapsed : chart.encode left = chart.encode right) (distinct : left ≠ right) :
    ¬ chart.ExactOn region := by
  intro exactOn
  apply distinct
  calc
    left = chart.decode (chart.encode left) := (exactOn left leftIn).symm
    _ = chart.decode (chart.encode right) := congrArg chart.decode collapsed
    _ = right := exactOn right rightIn

end AutoencodingChart

/-! ## A LoRA-like overlay is a restricted factorized morphology passage -/

structure FactorizedLinearOverlay
    (Input : Type uInput) (Hidden : Type uHidden) (Output : Type uOutput)
    [AddCommMonoid Input] [AddCommMonoid Hidden] [AddCommMonoid Output]
    [Module ℝ Input] [Module ℝ Hidden] [Module ℝ Output] where
  base : Input →ₗ[ℝ] Output
  inward : Input →ₗ[ℝ] Hidden
  outward : Hidden →ₗ[ℝ] Output

namespace FactorizedLinearOverlay

variable
    {Input : Type uInput} {Hidden : Type uHidden} {Output : Type uOutput}
    [AddCommMonoid Input] [AddCommMonoid Hidden] [AddCommMonoid Output]
    [Module ℝ Input] [Module ℝ Hidden] [Module ℝ Output]
    (overlay : FactorizedLinearOverlay Input Hidden Output)

def apply (input : Input) : Output :=
  overlay.base input + overlay.outward (overlay.inward input)

/-- The overlay is additive transported morphology, not an elementwise mask. -/
@[simp] theorem apply_eq_base_add_factorized (input : Input) :
    overlay.apply input =
      overlay.base input + overlay.outward (overlay.inward input) := rfl

/-- The apparatus hidden carrier bounds only this proposed update chart. -/
def update : Input →ₗ[ℝ] Output :=
  overlay.outward.comp overlay.inward

@[simp] theorem update_apply (input : Input) :
    overlay.update input = overlay.outward (overlay.inward input) := rfl

end FactorizedLinearOverlay

/-! ## Distillation is familywise receiver transport condensation -/

structure FamilyDistillationChart
    (Source : Type uSource) (Candidate : Type uCandidate)
    (Query : Type uQuery) (Receiver : Type uReceiver) (Face : Type uFace) where
  sourceConduct : Source → Query → Receiver → Face
  candidateConduct : Candidate → Query → Receiver → Face
  condense : Source → Candidate
  exact : ∀ source query receiver,
    candidateConduct (condense source) query receiver = sourceConduct source query receiver

namespace FamilyDistillationChart

variable
    {Source : Type uSource} {Candidate : Type uCandidate}
    {Query : Type uQuery} {Receiver : Type uReceiver} {Face : Type uFace}
    (chart : FamilyDistillationChart Source Candidate Query Receiver Face)

theorem every_declared_face_factors (source : Source) (query : Query) (receiver : Receiver) :
    chart.candidateConduct (chart.condense source) query receiver =
      chart.sourceConduct source query receiver := chart.exact source query receiver

def Defect (source : Source) (candidate : Candidate) : Prop :=
  ∃ query receiver,
    chart.candidateConduct candidate query receiver ≠ chart.sourceConduct source query receiver

/-- One separating receiver/query pair is the exact obstruction to claiming receiver-exact
distillation for that candidate. -/
theorem defect_obstructs_exact
    (source : Source) (candidate : Candidate) (defect : chart.Defect source candidate) :
    ¬ ∀ query receiver,
      chart.candidateConduct candidate query receiver =
        chart.sourceConduct source query receiver := by
  rintro alleged
  obtain ⟨query, receiver, separates⟩ := defect
  exact separates (alleged query receiver)

end FamilyDistillationChart

/-! ## Reinforcement learning is a world-return cultivation chart -/

structure WorldReturnedCultivation
    (Morphology : Type uMorphology) (Action : Type uAction) (World : Type uWorld)
    (Difference : Type uDifference) where
  act : Morphology → Action
  worldConsequence : Action → World
  difference : Morphology → Action → World → Difference
  returnMorphology : Difference → Morphology → Morphology

namespace WorldReturnedCultivation

variable
    {Morphology : Type uMorphology} {Action : Type uAction}
    {World : Type uWorld} {Difference : Type uDifference}
    (cultivation : WorldReturnedCultivation Morphology Action World Difference)

def occurrence (morphology : Morphology) : Action × World × Difference × Morphology :=
  let action := cultivation.act morphology
  let consequence := cultivation.worldConsequence action
  let returned := cultivation.difference morphology action consequence
  (action, consequence, returned, cultivation.returnMorphology returned morphology)

@[simp] theorem occurrence_action (morphology : Morphology) :
    (cultivation.occurrence morphology).1 = cultivation.act morphology := rfl

/-- A conventional scalar reward is optional receiver testimony; the complete world consequence
and returned difference already precede it. -/
def rewardFace (reward : World → ℝ) (morphology : Morphology) : ℝ :=
  reward (cultivation.occurrence morphology).2.1

end WorldReturnedCultivation

section Audit

#print axioms ScalarObjective.no_complete_descent_of_separator
#print axioms GradientProposal.candidate_is_metric_raised_return
#print axioms AutoencodingChart.collapsed_pair_obstructs_exact_reconstruction
#print axioms FactorizedLinearOverlay.apply_eq_base_add_factorized
#print axioms FamilyDistillationChart.every_declared_face_factors
#print axioms FamilyDistillationChart.defect_obstructs_exact
#print axioms WorldReturnedCultivation.occurrence_action

end Audit

end Soma.Holonics.Computation.HolonicCultivationCharts
