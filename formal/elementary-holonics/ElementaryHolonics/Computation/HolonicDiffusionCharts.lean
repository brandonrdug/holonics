import ElementaryHolonics.Computation.HolonicArchitectureCharts

/-!
# Deterministic and stochastic diffusion are distinct transport configurations

Deterministic diffusion is a constituted state transition.  Stochastic diffusion transports a
normalized finite measure through a positive Markov kernel.  Both compose through chronology, but
neither name creates a reasoning organ and a forward stochastic kernel does not manufacture its
own reverse.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicDiffusionCharts

open scoped BigOperators
open Soma.Holonics.Computation.HolonicArchitectureCharts

universe uI uJ uK uState uInput

/-! ## Finite nonnegative measures and Markov transport -/

@[ext] structure FiniteProbabilitySection (Index : Type uI) [Fintype Index] where
  mass : Index → ℝ
  nonnegative : ∀ index, 0 ≤ mass index
  normalized : ∑ index, mass index = 1

structure MarkovKernel (Source : Type uI) (Target : Type uJ)
    [Fintype Source] [Fintype Target] where
  transition : Source → Target → ℝ
  nonnegative : ∀ source target, 0 ≤ transition source target
  normalized : ∀ source, ∑ target, transition source target = 1

namespace MarkovKernel

variable {Source : Type uI} {Middle : Type uJ} {Target : Type uK}
  [Fintype Source] [Fintype Middle] [Fintype Target]

def pushforward (kernel : MarkovKernel Source Target)
    (probability : FiniteProbabilitySection Source) : FiniteProbabilitySection Target where
  mass target := ∑ source, probability.mass source * kernel.transition source target
  nonnegative target := Finset.sum_nonneg fun source hsource =>
    mul_nonneg (probability.nonnegative source) (kernel.nonnegative source target)
  normalized := by
    classical
    calc
      (∑ target, ∑ source,
          probability.mass source * kernel.transition source target) =
        ∑ source, ∑ target,
          probability.mass source * kernel.transition source target :=
            Finset.sum_comm
      _ = ∑ source, probability.mass source := by
        apply Finset.sum_congr rfl
        intro source hsource
        rw [← Finset.mul_sum, kernel.normalized]
        ring
      _ = 1 := probability.normalized

def compose (first : MarkovKernel Source Middle) (second : MarkovKernel Middle Target) :
    MarkovKernel Source Target where
  transition source target :=
    ∑ middle, first.transition source middle * second.transition middle target
  nonnegative source target := Finset.sum_nonneg fun middle hmiddle =>
    mul_nonneg (first.nonnegative source middle) (second.nonnegative middle target)
  normalized source := by
    classical
    calc
      (∑ target, ∑ middle,
          first.transition source middle * second.transition middle target) =
        ∑ middle, ∑ target,
          first.transition source middle * second.transition middle target :=
            Finset.sum_comm
      _ = ∑ middle, first.transition source middle := by
        apply Finset.sum_congr rfl
        intro middle hmiddle
        rw [← Finset.mul_sum, second.normalized]
        ring
      _ = 1 := first.normalized source

/-- Chapman--Kolmogorov composition agrees exactly with sequential measure transport. -/
theorem pushforward_compose
    (first : MarkovKernel Source Middle) (second : MarkovKernel Middle Target)
    (probability : FiniteProbabilitySection Source) :
    (first.compose second).pushforward probability =
      second.pushforward (first.pushforward probability) := by
  apply FiniteProbabilitySection.ext
  funext target
  simp only [pushforward, compose]
  calc
    (∑ source, probability.mass source *
        ∑ middle, first.transition source middle * second.transition middle target) =
      ∑ source, ∑ middle,
        probability.mass source * first.transition source middle *
          second.transition middle target := by
            apply Finset.sum_congr rfl
            intro source hsource
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro middle hmiddle
            ring
    _ = ∑ middle, ∑ source,
        probability.mass source * first.transition source middle *
          second.transition middle target := Finset.sum_comm
    _ = ∑ middle,
        (∑ source, probability.mass source * first.transition source middle) *
          second.transition middle target := by
            apply Finset.sum_congr rfl
            intro middle hmiddle
            rw [Finset.sum_mul]

def expectation (probability : FiniteProbabilitySection Source)
    (receiver : Source → ℝ) : ℝ :=
  ∑ source, probability.mass source * receiver source

theorem expectation_pushforward
    (kernel : MarkovKernel Source Target)
    (probability : FiniteProbabilitySection Source) (receiver : Target → ℝ) :
    expectation (kernel.pushforward probability) receiver =
      ∑ source, probability.mass source *
        (∑ target, kernel.transition source target * receiver target) := by
  classical
  unfold expectation
  change (∑ target, (∑ source,
    probability.mass source * kernel.transition source target) * receiver target) = _
  calc
    (∑ target, (∑ source,
        probability.mass source * kernel.transition source target) * receiver target) =
      ∑ target, ∑ source,
        probability.mass source * kernel.transition source target * receiver target := by
          apply Finset.sum_congr rfl
          intro target htarget
          rw [Finset.sum_mul]
    _ = ∑ source, ∑ target,
        probability.mass source * kernel.transition source target * receiver target :=
          Finset.sum_comm
    _ = ∑ source, probability.mass source *
        (∑ target, kernel.transition source target * receiver target) := by
          apply Finset.sum_congr rfl
          intro source hsource
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro target htarget
          ring

def dirac [DecidableEq Target] (transport : Source → Target) : MarkovKernel Source Target where
  transition source target := if target = transport source then 1 else 0
  nonnegative source target := by split <;> norm_num
  normalized source := by simp

@[simp] theorem dirac_transition [DecidableEq Target]
    (transport : Source → Target) (source : Source) (target : Target) :
    (dirac transport).transition source target =
      if target = transport source then 1 else 0 := rfl

end MarkovKernel

/-! ## A forward kernel alone does not define reverse generation -/

def collapseBool : MarkovKernel Bool Unit := MarkovKernel.dirac (fun _ => ())
def identityBool : MarkovKernel Bool Bool := MarkovKernel.dirac id

theorem collapseBool_has_no_stochastic_inverse :
    ¬ ∃ reverse : MarkovKernel Unit Bool,
      collapseBool.compose reverse = identityBool := by
  rintro ⟨reverse, inverseLaw⟩
  have falseFace := congrFun (congrFun (congrArg MarkovKernel.transition inverseLaw) false) false
  have trueFace := congrFun (congrFun (congrArg MarkovKernel.transition inverseLaw) true) false
  simp [collapseBool, identityBool, MarkovKernel.compose, MarkovKernel.dirac] at falseFace trueFace
  linarith

/-! ## Deterministic implicit diffusion descends to a state-space recurrence -/

structure ImplicitDiffusionChart
    (State : Type uState) (Input : Type uInput)
    [AddCommGroup State] [Module ℝ State] where
  capacity : State →ₗ[ℝ] State
  laplacian : State →ₗ[ℝ] State
  source : Input → State
  timestep : ℝ
  implicitOperator : State ≃ₗ[ℝ] State
  constituted : ∀ state,
    implicitOperator state = capacity state + timestep • laplacian state

namespace ImplicitDiffusionChart

variable {State : Type uState} {Input : Type uInput}
  [AddCommGroup State] [Module ℝ State]
  (D : ImplicitDiffusionChart State Input)

def advance (state : State) (input : Input) : State :=
  D.implicitOperator.symm (D.capacity state + D.source input)

/-- The computed successor satisfies the constituted implicit balance exactly. -/
theorem advance_balance (state : State) (input : Input) :
    D.capacity (D.advance state input) + D.timestep • D.laplacian (D.advance state input) =
      D.capacity state + D.source input := by
  rw [← D.constituted]
  exact D.implicitOperator.apply_symm_apply _

/-- Deterministic diffusion is a state-space recurrence chart once its constituted operator is
invertible; no stochastic kernel is introduced. -/
def asStateSpace : StateSpace.Chart State Input State where
  advance := D.advance
  observe state _ := state

@[simp] theorem asStateSpace_advance (state : State) (input : Input) :
    D.asStateSpace.advance state input = D.advance state input := rfl

end ImplicitDiffusionChart

/-! ## Chronological stochastic refinement -/

namespace MarkovKernel

variable {Index : Type uI} [Fintype Index] [DecidableEq Index]

def iterate (kernel : MarkovKernel Index Index) : Nat → MarkovKernel Index Index
  | 0 => MarkovKernel.dirac id
  | n + 1 => (iterate kernel n).compose kernel

theorem iterate_succ_pushforward (kernel : MarkovKernel Index Index)
    (steps : Nat) (probability : FiniteProbabilitySection Index) :
    (kernel.iterate (steps + 1)).pushforward probability =
      kernel.pushforward ((kernel.iterate steps).pushforward probability) := by
  simp only [iterate]
  exact pushforward_compose (kernel.iterate steps) kernel probability

end MarkovKernel

section Audit

#print axioms MarkovKernel.pushforward_compose
#print axioms MarkovKernel.expectation_pushforward
#print axioms collapseBool_has_no_stochastic_inverse
#print axioms ImplicitDiffusionChart.advance_balance
#print axioms ImplicitDiffusionChart.asStateSpace_advance
#print axioms MarkovKernel.iterate_succ_pushforward

end Audit

end Soma.Holonics.Computation.HolonicDiffusionCharts
