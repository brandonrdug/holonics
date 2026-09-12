import ElementaryHolonics.Foundation.ReceiverCodeCost
import ElementaryHolonics.Foundation.ReceiverHistoryCompression
import ElementaryHolonics.Computation.HolonicAdjointNormalization
import ElementaryHolonics.Physics.InformationDifference

/-!
# Generator inference through description, loss and sufficient representations

The candidate type may contain programs, factorizations, parameters or dependent architecture/
parameter pairs. Feasibility is represented by its admitted subtype before this finite positive
probability chart is used. No measure is imposed on an arbitrary source fibre.

This composes the existing normalized-exponential receiver, Gibbs/KL identity, addressed code-cost
law and dynamic receiver quotient. It supplies no new optimizer or native learning law.
Ideal code units are bits; literal packet overhead remains part of the supplied description.
-/

noncomputable section

namespace Soma.Holonics.Foundation.GeneratorInference

open scoped BigOperators
open Soma.Holonics.Computation.HolonicInformationTheory
open Soma.Holonics.Millennium.LineageCompression
open Soma.Holonics.Millennium.Chronology

open Soma.Holonics.Computation.HolonicAdjointNormalization
open Soma.Holonics.Physics

variable {Candidate : Type*} [Fintype Candidate] [Nonempty Candidate]

theorem bitScale_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)

/-- A declared finite description/data objective read as a complete Gibbs receiver. -/
def posterior (objective : Candidate → ℝ) : PositiveProbabilitySection Candidate :=
  NormalizedExponential.face (fun candidate => -(Real.log 2) * objective candidate)

/-- Expected description/data cost minus the entropy of the retained candidate family, in bits. -/
def variational (objective : Candidate → ℝ) (q : PositiveProbabilitySection Candidate) : ℝ :=
  InformationDifference.freeEnergy (Real.log 2)⁻¹ objective q

theorem posterior_log_mass (objective : Candidate → ℝ) (candidate : Candidate) :
    Real.log ((posterior objective).mass candidate) =
      -(Real.log 2) * objective candidate -
        Real.log (NormalizedExponential.partition (fun p => -(Real.log 2) * objective p)) :=
  NormalizedExponential.log_face_mass _ _

/-- MDL/MAP order is the ordering of one declared objective, not a second inference operation. -/
theorem posterior_mass_le_iff (objective : Candidate → ℝ) (left right : Candidate) :
    (posterior objective).mass left ≤ (posterior objective).mass right ↔
      objective right ≤ objective left := by
  rw [posterior, NormalizedExponential.face_mass_le_iff]
  constructor <;> intro h <;> nlinarith [bitScale_pos]

theorem minimizer_iff_posterior_mode (objective : Candidate → ℝ) (candidate : Candidate) :
    (∀ p, objective candidate ≤ objective p) ↔
      ∀ p, (posterior objective).mass p ≤ (posterior objective).mass candidate := by
  simp only [posterior_mass_le_iff]

/-- Exact synthesis uses the admissible solution fibre itself as its candidate population. -/
theorem exact_solver_iff_posterior_mode (feasible : Candidate → Prop)
    [DecidablePred feasible] [Nonempty {p // feasible p}]
    (description : Candidate → ℝ) (solution : {p // feasible p}) :
    (∀ p, feasible p → description solution ≤ description p) ↔
      ∀ p : {p // feasible p},
        (posterior (fun q : {p // feasible p} => description q)).mass p ≤
          (posterior (fun q : {p // feasible p} => description q)).mass solution := by
  rw [← minimizer_iff_posterior_mode]
  constructor
  · intro minimal p
    exact minimal p p.property
  · intro minimal p hp
    exact minimal ⟨p, hp⟩

/-- Finite Bayes is the description-plus-log-loss receiver, including its normalization. -/
theorem posterior_of_log_description_and_likelihood
    (prior likelihood : Candidate → ℝ)
    (prior_pos : ∀ p, 0 < prior p) (likelihood_pos : ∀ p, 0 < likelihood p)
    (candidate : Candidate) :
    (posterior (fun p => -Real.log (prior p) / Real.log 2 -
      Real.log (likelihood p) / Real.log 2)).mass candidate =
      prior candidate * likelihood candidate / ∑ p, prior p * likelihood p := by
  have factor (p : Candidate) :
      Real.exp (-(Real.log 2) * (-Real.log (prior p) / Real.log 2 -
        Real.log (likelihood p) / Real.log 2)) = prior p * likelihood p := by
    rw [show -(Real.log 2) * (-Real.log (prior p) / Real.log 2 -
      Real.log (likelihood p) / Real.log 2) = Real.log (prior p) + Real.log (likelihood p) by
        field_simp [bitScale_pos.ne']; ring]
    rw [Real.exp_add, Real.exp_log (prior_pos p), Real.exp_log (likelihood_pos p)]
  simp only [posterior, NormalizedExponential.face, NormalizedExponential.partition, factor]

/-- The previous Gibbs/free-energy theorem now prices a distribution over executable descriptions. -/
theorem variational_gap_eq_kl_bits (objective : Candidate → ℝ)
    (q : PositiveProbabilitySection Candidate) :
    variational objective q - variational objective (posterior objective) =
      q.klDivergence (posterior objective) / Real.log 2 := by
  have canonical (p : Candidate) :
      (Real.log 2)⁻¹ * Real.log ((posterior objective).mass p) =
        -objective p - (Real.log 2)⁻¹ *
          Real.log (NormalizedExponential.partition (fun z => -(Real.log 2) * objective z)) := by
    rw [posterior_log_mass]
    field_simp [bitScale_pos.ne']
  have result := InformationDifference.freeEnergy_difference_eq_thermalScale_mul_kl
    (Real.log 2)⁻¹ objective
    (Real.log (NormalizedExponential.partition (fun z => -(Real.log 2) * objective z)))
    q (posterior objective) canonical
  simpa only [variational, div_eq_mul_inv, mul_comm] using result

theorem variational_minimum (objective : Candidate → ℝ)
    (q : PositiveProbabilitySection Candidate) :
    variational objective (posterior objective) ≤ variational objective q := by
  have gap := variational_gap_eq_kl_bits objective q
  have positive := div_nonneg (q.klDivergence_nonnegative (posterior objective)) bitScale_pos.le
  linarith

/-- A complete normalized inference face retains exactly the pairwise objective differences. -/
theorem posterior_eq_iff_objective_differences (left right : Candidate → ℝ) :
    (posterior left).mass = (posterior right).mass ↔
      ∀ i j, left i - left j = right i - right j := by
  rw [posterior, posterior, NormalizedExponential.face_eq_iff_pairwise_differences]
  constructor
  · intro h i j
    have difference := h i j
    nlinarith [bitScale_pos]
  · intro h i j
    have difference := h i j
    calc
      -(Real.log 2) * left i - -(Real.log 2) * left j =
          -(Real.log 2) * (left i - left j) := by ring
      _ = -(Real.log 2) * (right i - right j) := congrArg (fun x => -(Real.log 2) * x) difference
      _ = -(Real.log 2) * right i - -(Real.log 2) * right j := by ring

/-- A history-dependent additive offset carries no model discrimination. -/
theorem sufficient_statistic_posterior
    {History Statistic : Type*} (statistic : History → Statistic)
    (objective : History → Candidate → ℝ) (reduced : Statistic → Candidate → ℝ)
    (offset : History → ℝ)
    (factors : ∀ history p, objective history p = reduced (statistic history) p + offset history)
    (history : History) :
    (posterior (objective history)).mass = (posterior (reduced (statistic history))).mass := by
  apply (posterior_eq_iff_objective_differences _ _).2
  intro i j
  rw [factors, factors]
  ring

/-- Recursively sufficient statistics reuse the existing dynamic compression contract. -/
def sufficientHistoryCompression
    {History Statistic Generator : Type*} (statistic : History → Statistic)
    (objective : History → Candidate → ℝ) (reduced : Statistic → Candidate → ℝ)
    (offset : History → ℝ)
    (factors : ∀ history p, objective history p = reduced (statistic history) p + offset history)
    (step : Generator → History → History) (reducedStep : Generator → Statistic → Statistic)
    (closed : ∀ g h, statistic (step g h) = reducedStep g (statistic h)) :
    ReceiverHistoryCompression Generator Unit History Statistic (Candidate → ℝ) where
  present := {
    quotient := statistic
    receiver := fun _ h => (posterior (objective h)).mass
    factor := fun _ s => (posterior (reduced s)).mass
    exact := fun _ h => (sufficient_statistic_posterior statistic objective reduced offset factors h).symm }
  sourceTransport := step
  quotientTransport := reducedStep
  generatorExact := closed

theorem sufficient_statistic_every_future
    {History Statistic Generator : Type*} (statistic : History → Statistic)
    (objective : History → Candidate → ℝ) (reduced : Statistic → Candidate → ℝ)
    (offset : History → ℝ)
    (factors : ∀ history p, objective history p = reduced (statistic history) p + offset history)
    (step : Generator → History → History) (reducedStep : Generator → Statistic → Statistic)
    (closed : ∀ g h, statistic (step g h) = reducedStep g (statistic h))
    (word : List Generator) (history : History) :
    (posterior (reduced (transportWord reducedStep word (statistic history)))).mass =
      (posterior (objective (transportWord step word history))).mass := by
  let compression := sufficientHistoryCompression statistic objective reduced offset factors step reducedStep closed
  have commute := compression.quotientCommutesWithEveryOrderedWord word history
  change statistic (transportWord step word history) =
    transportWord reducedStep word (statistic history) at commute
  rw [← commute]
  exact (sufficient_statistic_posterior statistic objective reduced offset factors _).symm

/-- Code/work boundary terms and residuals contribute to inference unless common to all candidates. -/
theorem code_cost_log_odds
    (description loss cost boundary residual : Candidate → ℝ) (C : ℝ)
    (balance : ∀ p, description p = C * cost p + boundary p + residual p)
    (left right : Candidate) :
    (Real.log ((posterior (fun p => description p + loss p)).mass left) -
      Real.log ((posterior (fun p => description p + loss p)).mass right)) / Real.log 2 =
      -(C * (cost left - cost right) + (boundary left - boundary right) +
        (residual left - residual right) + (loss left - loss right)) := by
  rw [posterior_log_mass, posterior_log_mass, balance, balance]
  field_simp [bitScale_pos.ne']; ring

/-! ## Noninjective representation changes transport candidate mass through the whole fibre -/

section CoarseGraining

variable {Class : Type*} [Fintype Class] [Nonempty Class] [DecidableEq Class]

def fibreWeight (objective : Candidate → ℝ) (project : Candidate → Class) (label : Class) : ℝ :=
  ∑ p, if project p = label then Real.exp (-(Real.log 2) * objective p) else 0

theorem fibreWeight_pos (objective : Candidate → ℝ) (project : Candidate → Class)
    (onto : Function.Surjective project) (label : Class) : 0 < fibreWeight objective project label := by
  classical
  obtain ⟨p, hp⟩ := onto label
  apply Finset.sum_pos'
  · intro p _
    split_ifs <;> positivity
  · exact ⟨p, Finset.mem_univ p, by simp [hp, Real.exp_pos]⟩

theorem sum_fibreWeight (objective : Candidate → ℝ) (project : Candidate → Class) :
    (∑ label, fibreWeight objective project label) =
      NormalizedExponential.partition (fun p => -(Real.log 2) * objective p) := by
  classical
  unfold fibreWeight NormalizedExponential.partition
  rw [Finset.sum_comm]
  simp

/-- The effective description of a class is its fibre log-sum, not an arbitrary representative. -/
def coarseObjective (objective : Candidate → ℝ) (project : Candidate → Class) (label : Class) : ℝ :=
  -Real.log (fibreWeight objective project label) / Real.log 2

theorem coarse_exponential (objective : Candidate → ℝ) (project : Candidate → Class)
    (onto : Function.Surjective project) (label : Class) :
    Real.exp (-(Real.log 2) * coarseObjective objective project label) =
      fibreWeight objective project label := by
  unfold coarseObjective
  rw [show -(Real.log 2) * (-Real.log (fibreWeight objective project label) / Real.log 2) =
      Real.log (fibreWeight objective project label) by field_simp [bitScale_pos.ne']]
  exact Real.exp_log (fibreWeight_pos objective project onto label)

/-- Gibbs inference commutes with coarse graining when the complete candidate mass is pushed forward. -/
theorem posterior_coarse_eq_pushforward (objective : Candidate → ℝ)
    (project : Candidate → Class) (onto : Function.Surjective project) (label : Class) :
    (posterior (coarseObjective objective project)).mass label =
      ∑ p, if project p = label then (posterior objective).mass p else 0 := by
  classical
  change Real.exp (-(Real.log 2) * coarseObjective objective project label) /
      NormalizedExponential.partition (fun k => -(Real.log 2) * coarseObjective objective project k) = _
  have partition : NormalizedExponential.partition
      (fun k => -(Real.log 2) * coarseObjective objective project k) =
        NormalizedExponential.partition (fun p => -(Real.log 2) * objective p) := by
    unfold NormalizedExponential.partition
    simp_rw [coarse_exponential objective project onto]
    exact sum_fibreWeight objective project
  rw [coarse_exponential objective project onto, partition]
  simp only [fibreWeight, Finset.sum_div, posterior, NormalizedExponential.face, ite_div, zero_div]

end CoarseGraining

/-! A concrete recursively sufficient representation: two symbol counts carry a whole
finite candidate likelihood family. The order is discarded only for this additive source law. -/

namespace CountControl

def statistic (history : List Bool) : ℕ × ℕ :=
  (history.count false, history.count true)

def step (event : Bool) (counts : ℕ × ℕ) : ℕ × ℕ :=
  if event then (counts.1, counts.2 + 1) else (counts.1 + 1, counts.2)

theorem closed (event : Bool) (history : List Bool) :
    statistic (event :: history) = step event (statistic history) := by
  cases event <;> simp [statistic, step]

def objective (description falseLoss trueLoss : Candidate → ℝ)
    (history : List Bool) (p : Candidate) : ℝ :=
  description p + (history.map (fun event => if event then trueLoss p else falseLoss p)).sum

def reduced (description falseLoss trueLoss : Candidate → ℝ)
    (counts : ℕ × ℕ) (p : Candidate) : ℝ :=
  description p + counts.1 * falseLoss p + counts.2 * trueLoss p

omit [Fintype Candidate] [Nonempty Candidate] in
theorem factors (description falseLoss trueLoss : Candidate → ℝ)
    (history : List Bool) (p : Candidate) :
    objective description falseLoss trueLoss history p =
      reduced description falseLoss trueLoss (statistic history) p := by
  induction history with
  | nil => simp [objective, reduced, statistic]
  | cons event history ih =>
    cases event <;>
      simp [objective, reduced, statistic, Nat.cast_add] at ih ⊢ <;> linarith

theorem same_counts_preserve_inference (description falseLoss trueLoss : Candidate → ℝ)
    (left right : List Bool) (same : statistic left = statistic right) :
    (posterior (objective description falseLoss trueLoss left)).mass =
      (posterior (objective description falseLoss trueLoss right)).mass := by
  have hleft := funext (factors description falseLoss trueLoss left)
  have hright := funext (factors description falseLoss trueLoss right)
  rw [hleft, hright, same]

end CountControl

#print axioms exact_solver_iff_posterior_mode
#print axioms posterior_of_log_description_and_likelihood
#print axioms variational_gap_eq_kl_bits
#print axioms variational_minimum
#print axioms posterior_eq_iff_objective_differences
#print axioms sufficient_statistic_every_future
#print axioms code_cost_log_odds
#print axioms posterior_coarse_eq_pushforward

end Soma.Holonics.Foundation.GeneratorInference
