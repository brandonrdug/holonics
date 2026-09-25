import Holonics.Aeon.Clock.Reading
import Holonics.Physics.InformationDifference

/-!
# Joining clock axes: a commuting join or its cycle defect; the two-parameter flow square

[definition] Rebuild step 6, K4 (#75); restructure plan §3.6 at `13f8c734`, "keep distinct addressed
clock lines: source/generator phase, receiving proper time, fluid/world-tube time, thermal
relaxation and observation ticks". The clock axes are the occurrences of a parametric complex
(`Aeon/Clock/Groupoid.ParametricComplex`); each declared unit/chart map between two axes is a
passage carrying its rate in the additive chart of a commutative group `A` (the log chart of the
rate ratios, or `Additive ℚˣ` for the ratios themselves). A **join** of the axes is a potential
`φ` whose exact form is the declared rate cochain: every axis gets one rate against a reference,
and every declared map is the ratio of the two (`Joins`).

[proved-derived; formal-checked]

* **A join is silent on every cycle** (`join_silent_on_cycles`, the owner's
  `Reading.wordReading_exactForm`): around any closed chain of rate maps the product of the rates is
  one.
* **Conversely, on a connected axis graph a silent rate cochain joins**, with the potential read
  along any chosen aeons from a reference axis (`join_of_silent_on_cycles`); so a join exists
  exactly when every cycle reads trivially (`join_iff_silent`). Otherwise the cycle's reading is
  the **defect**: the holonomy of the declared maps. On a triangle of axes with rates `2`, `3`,
  `1/5` the loop reads the product `6/5 ≠ 1` and no join exists (`triangle_defect`).
* **The two-parameter flow square.** Two parametrized evolutions `A` (say fluid) and `B` (say
  thermal) of one state commute exactly when the square closes: then every receiver reads the two
  orders alike (`commuting_square_reads_alike`); in general the two orders differ by the
  commutator applied to the state (`square_defect`).

[counterexample; formal-checked] **A non-commuting square changes the cross-entropy return.** The
column-stochastic steps `A = [[1, 1/2], [0, 1/2]]` and `B = [[1/2, 0], [1/2, 1]]` take
`p = (1/2, 1/2)` to `(3/8, 5/8)` by `A` then `B` and to `(5/8, 3/8)` by `B` then `A`
(`flow_square_orders`), and the two cross-entropies against `(1/3, 2/3)` differ
(`flow_square_crossEntropy_differs`).
-/

noncomputable section

namespace Holonics.Physics.Information.ClockJoin

open Matrix
open Holonics.Aeon.Clock.Groupoid
open Holonics.Aeon.Clock.Reading

/-! ## 1. The join of clock axes -/

section Join

variable {V E F : Type*} {K : ParametricComplex V E F} {A : Type*} [AddCommGroup A]

/-- [definition] **A join** of the axes: a potential whose exact form is the declared rate
cochain. -/
def Joins (K : ParametricComplex V E F) (ω : E → A) (φ : V → A) : Prop := ω = exactForm K φ

/-- [proved-derived; formal-checked] **A join is silent on every cycle.** -/
theorem join_silent_on_cycles {ω : E → A} {φ : V → A} (h : Joins K ω φ) {u : V}
    (γ : Aeon K u u) : wordReading ω γ.steps = 0 := by
  rw [h, wordReading_exactForm φ γ.chained, sub_self]

/-- [definition] The one-step aeon along a passage. -/
def edgeAeon (K : ParametricComplex V E F) (e : E) : Aeon K (K.src e) (K.tgt e) :=
  ⟨[(e, true)], by simp [ParametricComplex.start, ParametricComplex.finish]⟩

/-- [proved-derived; formal-checked] **A silent rate cochain joins** on a connected axis graph: the
potential is the reading along chosen aeons from a reference axis. -/
theorem join_of_silent_on_cycles (ω : E → A) (base : V) (path : ∀ v, Aeon K base v)
    (silent : ∀ (u : V) (γ : Aeon K u u), wordReading ω γ.steps = 0) :
    Joins K ω fun v => wordReading ω (path v).steps := by
  funext e
  have h := silent base (((path (K.src e)).concat (edgeAeon K e)).concat (path (K.tgt e)).reverse)
  simp only [Aeon.concat, Aeon.reverse, edgeAeon, wordReading_append, wordReading_reverseWord,
    wordReading_cons, wordReading_nil, stepReading, if_true, add_zero] at h
  simp only [exactForm]
  rw [← sub_eq_zero]
  rw [← h]
  abel

/-- [proved-derived; formal-checked] **A join exists exactly when every cycle reads trivially.** -/
theorem join_iff_silent (ω : E → A) (base : V) (path : ∀ v, Aeon K base v) :
    (∃ φ, Joins K ω φ) ↔ ∀ (u : V) (γ : Aeon K u u), wordReading ω γ.steps = 0 :=
  ⟨fun ⟨_, h⟩ _ γ => join_silent_on_cycles h γ,
    fun h => ⟨_, join_of_silent_on_cycles ω base path h⟩⟩

end Join

/-- [definition] Three clock axes in a triangle: `0 → 1 → 2 → 0`. -/
def axisTriangle : ParametricComplex (Fin 3) (Fin 3) Empty where
  src := ![0, 1, 2]
  tgt := ![1, 2, 0]
  base := Empty.elim
  boundary := Empty.elim

/-- [definition] The loop around the triangle of axes. -/
def axisLoop : Aeon axisTriangle 0 0 :=
  ⟨[(0, true), (1, true), (2, true)], by
    simp [ParametricComplex.Chained, ParametricComplex.start, ParametricComplex.finish,
      axisTriangle]⟩

/-- [definition] The declared rates `2`, `3`, `1/5` in the multiplicative carrier. -/
def triangleRates : Fin 3 → Additive ℚˣ :=
  ![Additive.ofMul (Units.mk0 2 (by norm_num)), Additive.ofMul (Units.mk0 3 (by norm_num)),
    Additive.ofMul (Units.mk0 (1 / 5) (by norm_num))]

/-- [counterexample; formal-checked] **The triangle's defect**: the loop reads the product of its
rates, `6/5 ≠ 1`, so the declared rates admit no join. -/
theorem triangle_defect :
    ((Additive.toMul (wordReading triangleRates axisLoop.steps) : ℚˣ) : ℚ) = 6 / 5 ∧
      ¬ ∃ φ, Joins axisTriangle triangleRates φ := by
  have hread : ((Additive.toMul (wordReading triangleRates axisLoop.steps) : ℚˣ) : ℚ) = 6 / 5 := by
    simp [axisLoop, wordReading, stepReading, triangleRates]
    norm_num
  refine ⟨hread, fun ⟨φ, h⟩ => ?_⟩
  have h0 := join_silent_on_cycles h axisLoop
  rw [h0] at hread
  norm_num at hread

/-! ## 2. The two-parameter flow square -/

section Flow

variable {ι R : Type*} [Fintype ι] [CommRing R]

/-- [proved-derived; formal-checked] **A commuting square is read alike by every receiver.** -/
theorem commuting_square_reads_alike {X : Type*} (Aflow Bflow : Matrix ι ι R)
    (hcomm : Aflow * Bflow = Bflow * Aflow) (receiver : (ι → R) → X) (p : ι → R) :
    receiver (Bflow *ᵥ (Aflow *ᵥ p)) = receiver (Aflow *ᵥ (Bflow *ᵥ p)) := by
  rw [mulVec_mulVec, mulVec_mulVec, hcomm]

/-- [proved-derived; formal-checked] **The square's defect** is the commutator applied to the
state. -/
theorem square_defect (Aflow Bflow : Matrix ι ι R) (p : ι → R) :
    Bflow *ᵥ (Aflow *ᵥ p) - Aflow *ᵥ (Bflow *ᵥ p) = (Bflow * Aflow - Aflow * Bflow) *ᵥ p := by
  rw [mulVec_mulVec, mulVec_mulVec, sub_mulVec]

end Flow

/-- [definition] The fluid step, column-stochastic. -/
def fluidStep : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1 / 2; 0, 1 / 2]

/-- [definition] The thermal step, column-stochastic. -/
def thermalStep : Matrix (Fin 2) (Fin 2) ℚ := !![1 / 2, 0; 1 / 2, 1]

/-- [counterexample; formal-checked] **The two orders differ.** -/
theorem flow_square_orders :
    thermalStep *ᵥ (fluidStep *ᵥ ![1 / 2, 1 / 2]) = ![3 / 8, 5 / 8] ∧
      fluidStep *ᵥ (thermalStep *ᵥ ![1 / 2, 1 / 2]) = ![5 / 8, 3 / 8] ∧
      fluidStep * thermalStep ≠ thermalStep * fluidStep := by
  refine ⟨?_, ?_, ?_⟩
  · ext i; fin_cases i <;> simp [thermalStep, fluidStep, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> norm_num
  · ext i; fin_cases i <;> simp [thermalStep, fluidStep, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two] <;> norm_num
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [thermalStep, fluidStep, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- [counterexample; formal-checked] **The non-commuting square changes the cross-entropy return**:
against the reference `(1/3, 2/3)`, the two orders' populations read different cross-entropies. -/
theorem flow_square_crossEntropy_differs :
    Holonics.Foundation.HolonicMembraneActionTransport.finiteCrossEntropy
        (![3 / 8, 5 / 8] : Fin 2 → ℝ) ![1 / 3, 2 / 3] ≠
      Holonics.Foundation.HolonicMembraneActionTransport.finiteCrossEntropy
        (![5 / 8, 3 / 8] : Fin 2 → ℝ) ![1 / 3, 2 / 3] := by
  simp only [Holonics.Foundation.HolonicMembraneActionTransport.finiteCrossEntropy,
    Fin.sum_univ_two]
  simp
  intro h
  have hlt : Real.log (1 / 3 : ℝ) < Real.log (2 / 3) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  rw [one_div, Real.log_inv] at hlt
  linarith

section Audit

#print axioms join_silent_on_cycles
#print axioms join_of_silent_on_cycles
#print axioms join_iff_silent
#print axioms triangle_defect
#print axioms commuting_square_reads_alike
#print axioms square_defect
#print axioms flow_square_orders
#print axioms flow_square_crossEntropy_differs

end Audit

end Holonics.Physics.Information.ClockJoin
