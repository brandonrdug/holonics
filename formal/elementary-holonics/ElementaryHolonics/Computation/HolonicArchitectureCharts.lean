import ElementaryHolonics.Computation.HolonicAdjointNormalization
import ElementaryHolonics.Computation.HolonicNeuralEcology

/-!
# Classical neural architectures as configurations of one local-current ecology

The names in this file are exterior receiver charts.  None is added to the native Eros/Athena
ontology.  Attention is input-conditioned contact, convolution is shared relative current, graph
transport is sparse irregular incidence, and a state-space model is rested recurrence with an
observation boundary.
-/

noncomputable section

namespace Soma.Holonics.Computation.HolonicArchitectureCharts

open scoped BigOperators
open Soma.Holonics.Computation.HolonicNeuralEcology
open Soma.Holonics.Computation.HolonicAdjointNormalization

universe uSite uState uInput uOutput uCache

/-! ## Attention and a complete block -/

structure AttentionChart (Site : Type uSite) [Fintype Site] [DecidableEq Site] where
  admitted : Site → Finset Site
  admitted_nonempty : ∀ target, (admitted target).Nonempty
  score : (Site → ℝ) → Site → Site → ℝ
  value : (Site → ℝ) → Site → ℝ

namespace AttentionChart

variable {Site : Type uSite} [Fintype Site] [DecidableEq Site]
  (A : AttentionChart Site)

def partition (state : Site → ℝ) (target : Site) : ℝ :=
  ∑ source ∈ A.admitted target, Real.exp (A.score state target source)

theorem partition_pos (state : Site → ℝ) (target : Site) :
    0 < A.partition state target := by
  apply Finset.sum_pos'
  · intro source hsource
    exact (Real.exp_pos _).le
  · obtain ⟨source, hsource⟩ := A.admitted_nonempty target
    exact ⟨source, hsource, Real.exp_pos _⟩

theorem partition_ne_zero (state : Site → ℝ) (target : Site) :
    A.partition state target ≠ 0 := (A.partition_pos state target).ne'

def weight (state : Site → ℝ) (target source : Site) : ℝ :=
  Real.exp (A.score state target source) / A.partition state target

theorem weight_positive (state : Site → ℝ) (target source : Site) :
    0 < A.weight state target source :=
  div_pos (Real.exp_pos _) (A.partition_pos state target)

/-- Normalization is over the admitted contact population, not over an authored global width. -/
theorem weight_normalized (state : Site → ℝ) (target : Site) :
    ∑ source ∈ A.admitted target, A.weight state target source = 1 := by
  unfold weight
  rw [← Finset.sum_div]
  exact div_self (A.partition_ne_zero state target)

def output (state : Site → ℝ) (target : Site) : ℝ :=
  ∑ source ∈ A.admitted target,
    A.weight state target source * A.value state source

/-- Attention is exactly one input-conditioned local-current ecology. -/
def ecology : FiniteLocalCurrentEcology Site ℝ Unit Unit Unit (Site → ℝ) where
  localCurrent _ _ state target source :=
    if source ∈ A.admitted target then
      A.weight state target source * A.value state source
    else 0
  reaction _ _ _ current := current
  observe _ state := state

theorem ecology_step_eq_output (state : Site → ℝ) :
    (A.ecology.step () () state) = A.output state := by
  funext target
  simp only [FiniteLocalCurrentEcology.step_apply, ecology, output]
  rw [← Finset.sum_filter]
  simp

def relabelState (reindex : Site ≃ Site) (state : Site → ℝ) (site : Site) : ℝ :=
  state (reindex.symm site)

/-- Complete attention is permutation-equivariant when score and value are transported with the
same receiver relabeling.  Masked attention obeys the corresponding theorem after transporting
its admitted finite sets; the complete case keeps that boundary assumption visible and exact. -/
theorem complete_output_relabel
    (complete : ∀ target, A.admitted target = Finset.univ)
    (reindex : Site ≃ Site) (state : Site → ℝ)
    (scoreCovariant : ∀ target source,
      A.score (relabelState reindex state) (reindex target) (reindex source) =
        A.score state target source)
    (valueCovariant : ∀ source,
      A.value (relabelState reindex state) (reindex source) = A.value state source) :
    A.output (relabelState reindex state) ∘ reindex = A.output state := by
  funext target
  have partitionCovariant :
      A.partition (relabelState reindex state) (reindex target) = A.partition state target := by
    unfold partition
    rw [complete (reindex target), complete target]
    calc
      (∑ source : Site,
          Real.exp (A.score (relabelState reindex state) (reindex target) source)) =
        ∑ source : Site,
          Real.exp (A.score (relabelState reindex state) (reindex target)
            (reindex source)) := by
              exact (reindex.sum_comp (fun source =>
                Real.exp (A.score (relabelState reindex state) (reindex target) source))).symm
      _ = ∑ source : Site, Real.exp (A.score state target source) := by
        apply Finset.sum_congr rfl
        intro source hsource
        rw [scoreCovariant]
  have weightCovariant : ∀ source,
      A.weight (relabelState reindex state) (reindex target) (reindex source) =
        A.weight state target source := by
    intro source
    unfold weight
    rw [scoreCovariant, partitionCovariant]
  change A.output (relabelState reindex state) (reindex target) = A.output state target
  unfold output
  rw [complete (reindex target), complete target]
  calc
    (∑ source : Site,
        A.weight (relabelState reindex state) (reindex target) source *
          A.value (relabelState reindex state) source) =
      ∑ source : Site,
        A.weight (relabelState reindex state) (reindex target) (reindex source) *
          A.value (relabelState reindex state) (reindex source) := by
            exact (reindex.sum_comp (fun source =>
              A.weight (relabelState reindex state) (reindex target) source *
                A.value (relabelState reindex state) source)).symm
    _ = ∑ source : Site,
        A.weight state target source * A.value state source := by
          apply Finset.sum_congr rfl
          intro source hsource
          rw [weightCovariant, valueCovariant]

/-- A block retains standing through a diagonal current, adds attention current, and applies one
local constitutive reaction. -/
structure Block where
  reaction : Site → ℝ → ℝ

def Block.output (block : Block (Site := Site)) (state : Site → ℝ) (target : Site) : ℝ :=
  block.reaction target (state target + A.output state target)

def Block.ecology (block : Block (Site := Site)) :
    FiniteLocalCurrentEcology Site ℝ Unit Unit Unit (Site → ℝ) where
  localCurrent _ _ state target source :=
    (if source = target then state source else 0) +
      if source ∈ A.admitted target then
        A.weight state target source * A.value state source
      else 0
  reaction _ _ target current := block.reaction target current
  observe _ state := state

theorem Block.ecology_step_eq_output (block : Block (Site := Site)) (state : Site → ℝ) :
    (block.ecology A).step () () state = block.output A state := by
  funext target
  simp only [FiniteLocalCurrentEcology.step_apply, Block.ecology, Block.output]
  rw [Finset.sum_add_distrib]
  have diagonal : (∑ source : Site, if source = target then state source else 0) =
      state target := by simp
  rw [diagonal, ← Finset.sum_filter]
  simp
  change block.reaction target (state target + A.output state target) =
    block.reaction target (state target + A.output state target)
  rfl

end AttentionChart

/-! ## Autoregressive recurrence and optional cache testimony -/

namespace Autoregressive

def conduct {State : Type uState} {Output : Type uOutput}
    (emit : State → Output) (remount : State → Output → State) :
    Nat → State → List Output
  | 0, _ => []
  | n + 1, state =>
      let emitted := emit state
      emitted :: conduct emit remount n (remount state emitted)

@[simp] theorem conduct_zero {State : Type uState} {Output : Type uOutput}
    (emit : State → Output) (remount : State → Output → State) (state : State) :
    conduct emit remount 0 state = [] := rfl

theorem conduct_length {State : Type uState} {Output : Type uOutput}
    (emit : State → Output) (remount : State → Output → State)
    (steps : Nat) (state : State) :
    (conduct emit remount steps state).length = steps := by
  induction steps generalizing state with
  | zero => rfl
  | succ steps ih => simp [conduct, ih]

/-- A cache is lawful only when its recovered state equals direct history conduct. -/
structure CacheValidity (Input : Type uInput) (State : Type uState) (Cache : Type uCache) where
  direct : List Input → State
  cache : List Input → Cache
  recover : Cache → State
  valid : ∀ history, recover (cache history) = direct history

theorem valid_cache_eq_direct
    {Input : Type uInput} {State : Type uState} {Cache : Type uCache}
    (C : CacheValidity Input State Cache) (history : List Input) :
    C.recover (C.cache history) = C.direct history := C.valid history

/-- The foreign cache coordinate does not become native state: an invalid witness is exposed by
one unchanged direct-history receiver. -/
theorem invalid_cache_control :
    ¬ ∀ history : List Bool, (false : Bool) = history.foldl xor false := by
  intro alleged
  have := alleged [true]
  simp at this

end Autoregressive

/-! ## Convolution: shared translation-relative current -/

namespace Convolution

variable {Site : Type uSite} [Fintype Site] [AddCommGroup Site]

def translate (shift : Site) (values : Site → ℝ) (site : Site) : ℝ :=
  values (site - shift)

def apply (kernel values : Site → ℝ) (site : Site) : ℝ :=
  ∑ offset : Site, kernel offset * values (site - offset)

def ecology (kernel : Site → ℝ) :
    FiniteLocalCurrentEcology Site ℝ Unit Unit Unit (Site → ℝ) where
  localCurrent _ _ values target offset := kernel offset * values (target - offset)
  reaction _ _ _ current := current
  observe _ values := values

theorem ecology_step_eq_apply (kernel values : Site → ℝ) :
    (ecology kernel).step () () values = apply kernel values := rfl

/-- Translation equivariance follows from the relative incidence law, with no layer ontology. -/
theorem translate_equivariant (kernel values : Site → ℝ) (shift : Site) :
    apply kernel (translate shift values) = translate shift (apply kernel values) := by
  funext site
  unfold apply translate
  apply Finset.sum_congr rfl
  intro offset hoffset
  congr 1
  congr 1
  abel

end Convolution

/-! ## Graph current and relabeling -/

namespace Graph

variable {Vertex : Type uSite} [Fintype Vertex] [DecidableEq Vertex]

def aggregate (incident : Vertex → Vertex → Bool)
    (message : ℝ → ℝ → ℝ) (state : Vertex → ℝ) (target : Vertex) : ℝ :=
  ∑ source : Vertex,
    if incident target source then message (state target) (state source) else 0

def ecology (incident : Vertex → Vertex → Bool) (message : ℝ → ℝ → ℝ)
    (reaction : Vertex → ℝ → ℝ → ℝ) :
    FiniteLocalCurrentEcology Vertex ℝ Unit Unit Unit (Vertex → ℝ) where
  localCurrent _ _ state target source :=
    if incident target source then message (state target) (state source) else 0
  reaction _ _ target current := reaction target 0 current
  observe _ state := state

def relabel (reindex : Vertex ≃ Vertex) (state : Vertex → ℝ) (vertex : Vertex) : ℝ :=
  state (reindex.symm vertex)

/-- Sparse graph transport is equivariant when the complete incidence relation is transported
with the vertex equivalence. -/
theorem aggregate_relabel
    (incident : Vertex → Vertex → Bool) (message : ℝ → ℝ → ℝ)
    (reindex : Vertex ≃ Vertex)
    (incidentCovariant : ∀ target source,
      incident (reindex target) (reindex source) = incident target source)
    (state : Vertex → ℝ) (target : Vertex) :
    aggregate incident message (relabel reindex state) (reindex target) =
      aggregate incident message state target := by
  unfold aggregate
  calc
    (∑ source : Vertex,
      if incident (reindex target) source then
        message ((relabel reindex state) (reindex target))
          ((relabel reindex state) source) else 0) =
      ∑ source : Vertex,
        if incident (reindex target) (reindex source) then
          message ((relabel reindex state) (reindex target))
            ((relabel reindex state) (reindex source)) else 0 := by
              exact (reindex.sum_comp (fun source =>
                if incident (reindex target) source then
                  message ((relabel reindex state) (reindex target))
                    ((relabel reindex state) source) else 0)).symm
    _ = ∑ source : Vertex,
        if incident target source then message (state target) (state source) else 0 := by
          apply Finset.sum_congr rfl
          intro source hsource
          simp [relabel, incidentCovariant]

end Graph

/-! ## State-space recurrence -/

namespace StateSpace

structure Chart (State : Type uState) (Input : Type uInput) (Output : Type uOutput) where
  advance : State → Input → State
  observe : State → Input → Output

namespace Chart

variable {State : Type uState} {Input : Type uInput} {Output : Type uOutput}
  (S : Chart State Input Output)

def fold : List Input → State → State
  | [], state => state
  | input :: rest, state => fold rest (S.advance state input)

@[simp] theorem fold_nil (state : State) : S.fold [] state = state := rfl

@[simp] theorem fold_cons (input : Input) (rest : List Input) (state : State) :
    S.fold (input :: rest) state = S.fold rest (S.advance state input) := rfl

theorem fold_append (left right : List Input) (state : State) :
    S.fold (left ++ right) state = S.fold right (S.fold left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons input left ih => simp [fold, ih]

end Chart

/-- The conventional linear SSM is one chart of the recurrence. -/
structure LinearChart (State : Type uState) (Input : Type uInput) (Output : Type uOutput)
    [AddCommMonoid State] [AddCommMonoid Output] where
  stateTransport : State →+ State
  inputTransport : Input → State
  observation : State →+ Output
  direct : Input → Output

def LinearChart.asChart
    {State : Type uState} {Input : Type uInput} {Output : Type uOutput}
    [AddCommMonoid State] [AddCommMonoid Output]
    (S : LinearChart State Input Output) : Chart State Input Output where
  advance state input := S.stateTransport state + S.inputTransport input
  observe state input := S.observation state + S.direct input

@[simp] theorem LinearChart.advance_eq_A_add_B
    {State : Type uState} {Input : Type uInput} {Output : Type uOutput}
    [AddCommMonoid State] [AddCommMonoid Output]
    (S : LinearChart State Input Output) (state : State) (input : Input) :
    S.asChart.advance state input = S.stateTransport state + S.inputTransport input := rfl

end StateSpace

section Audit

#print axioms AttentionChart.weight_normalized
#print axioms AttentionChart.ecology_step_eq_output
#print axioms AttentionChart.complete_output_relabel
#print axioms AttentionChart.Block.ecology_step_eq_output
#print axioms Autoregressive.conduct_length
#print axioms Autoregressive.valid_cache_eq_direct
#print axioms Autoregressive.invalid_cache_control
#print axioms Convolution.translate_equivariant
#print axioms Graph.aggregate_relabel
#print axioms StateSpace.Chart.fold_append
#print axioms StateSpace.LinearChart.advance_eq_A_add_B

end Audit

end Soma.Holonics.Computation.HolonicArchitectureCharts
