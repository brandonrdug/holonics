import Holonics.Aeon.Clock.Groupoid
import Holonics.Objects.Pairing
import Holonics.Geometry.CrossRatio
import Holonics.Transport.CellHolonomy

/-!
# Clocks and their readings: elapsed time is a pairing

[definition] `docs/ELEMENTARY_OBJECTS.md` §12 and the aeon record (A1). A **clock** of a
receiver is a closed 1-form of the parametric complex (`Clock`): a value on each oriented edge
whose reading around every two-cell vanishes. Its **reading** of an aeon is the pairing
`t_R(γ) = ⟨ω_R | γ⟩`, the sum of the clock over the aeon's signed steps (`reading`). A reading is
the parallel transport of a flat time connection; on a cycle it is the holonomy.

[proved-derived; formal-checked] What is proved.

1. **Additivity and reversal.** `reading_concat`: `t(γ · δ) = t(γ) + t(δ)`; `reading_reverse`:
   `t(Rγ) = −t(γ)`; `reading_rest`: rest reads zero. Readings descend to aeon classes and are a
   representation of the aeon groupoid in `(A, +)` (`classReading_comp`, `classReading_id`,
   `classReading_inv`).
2. **Homotopy invariance exactly characterizes closedness.** A closed form reads homotopic words
   alike (`reading_homotopy_invariant`); conversely a form that reads every pair of homotopic words
   alike is closed (`homotopy_invariant_iff_closed`).
3. **Stokes and gauge.** An exact form `dφ` reads `φ(v) − φ(u)` on an aeon from `u` to `v`
   (`reading_exactForm`), so it is a clock on a well-formed complex (`exactClock`) and every cycle
   reads it as zero; regauging a clock by `dφ` leaves every cycle reading unchanged
   (`cycle_reading_gauge_free`).
4. **Cycle readings factor through homology.** Over `ℚ` on a finite complex, the aeon's 1-chain
   is `chainOf`, the incidences are `incidence₁`, `incidence₂` with `∂₁∂₂ = 0`, a cycle's chain is
   in `Pairing.cycles` and a clock is in `Pairing.cocycles`; the reading of a cycle is the owner's
   class pairing `Pairing.classPairing` of the two classes
   (`cycle_reading_factors_through_homology`), so homologous cycles read alike
   (`homologous_cycles_read_alike`).
5. **The rate between two receivers** is the undivided pair of their readings of one aeon
   (`rate`, a `RatioPresentation`, "one per two"). No clock is privileged: exchanging the receivers
   exchanges the pair (`rate_swap`); a rate composed through a third clock is exactly the direct
   rate scaled by the mediating reading (`rate_through`), so through a clock that reads the aeon it
   is projectively the direct rate, admitted exactly when the direct rate is, with its quotient
   (`rate_through_projectivelyEq`); on a cycle the rate is unchanged by regauging either clock
   (`rate_regauge_cycle`) and, for `m ≠ 0`, by repeating the cycle `m` times (`rate_iterate`).
   Projective equality is transitive only through **admitted** ratios (`projectivelyEq_trans`):
   the undetermined pair `(0 : 0)` is projectively equal to every pair
   (`undetermined_breaks_transitivity`), and it is what a zero mediating reading or zero repetitions
   return (`rate_through_zero`, `rate_iterate`).

[counterexample; formal-checked] **Closedness is load-bearing.** On the filled triangle, the form
reading `1` on one edge is not closed; the boundary loop is homotopic to rest by one face move, yet
reads `1` against rest's `0` (`nonclosed_form_is_not_homotopy_invariant`). The boundary loop's chain
is a boundary, so the same form also fails to factor through homology
(`nonclosed_form_does_not_factor_through_homology`). The loop's reading is the owner's cell
holonomy `Transport/CellHolonomy.triangleHolonomy` in the multiplicative chart, and closedness is its
triviality (`triangleLoop_reading_is_cell_holonomy`).

Scope: combinatorial words and finite cochains. Smooth line integrals, de Rham's theorem and the
observer covector `−U_μ dx^μ` on a world tube are outside this module. No `axiom`, no `sorry`, no
`native_decide`.
-/

set_option linter.dupNamespace false

namespace Holonics.Aeon.Clock.Reading

open Holonics.Aeon.Clock.Groupoid
open scoped Matrix

variable {V E F : Type*}

/-! ## 1. The reading of a word -/

section Word

variable {A : Type*} [AddCommGroup A]

/-- [definition] The reading of one signed step by a form: the form's value along the edge,
negated against it. -/
def stepReading (ω : E → A) (s : E × Bool) : A := if s.2 then ω s.1 else -ω s.1

/-- [definition] The reading of a word: the sum of its step readings. -/
def wordReading (ω : E → A) (w : List (E × Bool)) : A := (w.map (stepReading ω)).sum

@[simp] theorem wordReading_nil (ω : E → A) : wordReading ω [] = 0 := rfl

@[simp] theorem wordReading_cons (ω : E → A) (s : E × Bool) (w : List (E × Bool)) :
    wordReading ω (s :: w) = stepReading ω s + wordReading ω w := by
  simp [wordReading]

/-- [proved-derived; formal-checked] The reading of a concatenated word is the sum. -/
theorem wordReading_append (ω : E → A) (p q : List (E × Bool)) :
    wordReading ω (p ++ q) = wordReading ω p + wordReading ω q := by
  simp [wordReading]

theorem stepReading_reverseStep (ω : E → A) (s : E × Bool) :
    stepReading ω (reverseStep s) = -stepReading ω s := by
  rcases s with ⟨e, _ | _⟩ <;> simp [stepReading, reverseStep]

/-- [proved-derived; formal-checked] The reversed word reads the negative. -/
theorem wordReading_reverseWord (ω : E → A) (w : List (E × Bool)) :
    wordReading ω (reverseWord w) = -wordReading ω w := by
  induction w with
  | nil => simp
  | cons s w ih =>
    rw [reverseWord_cons, wordReading_append, ih, wordReading_cons, wordReading_cons,
      wordReading_nil, stepReading_reverseStep]
    abel

theorem wordReading_add (ω η : E → A) (w : List (E × Bool)) :
    wordReading (ω + η) w = wordReading ω w + wordReading η w := by
  induction w with
  | nil => simp
  | cons s w ih =>
    rcases s with ⟨e, _ | _⟩ <;> simp [stepReading, ih] <;> abel

end Word

/-! ## 2. Clocks: the closed forms -/

section Clock

variable {A : Type*} [AddCommGroup A] (K : ParametricComplex V E F)

/-- [definition] A form is **closed** when it reads zero around every two-cell. -/
def IsClosed (ω : E → A) : Prop := ∀ f, wordReading ω (K.boundary f) = 0

/-- [definition] A **clock**: a closed 1-form of the parametric complex, a flat time connection. -/
structure Clock (A : Type*) [AddCommGroup A] where
  form : E → A
  closed : IsClosed K form

variable {K}

/-- [definition] **Elapsed time is a pairing**: the reading `⟨ω_R | γ⟩` of an aeon by a clock. -/
def reading (c : Clock K A) {u v : V} (γ : Aeon K u v) : A := wordReading c.form γ.steps

/-- [proved-derived; formal-checked] **Readings add under concatenation.** -/
theorem reading_concat (c : Clock K A) {u w v : V} (γ : Aeon K u w) (δ : Aeon K w v) :
    reading c (γ.concat δ) = reading c γ + reading c δ :=
  wordReading_append _ _ _

/-- [proved-derived; formal-checked] **Reversal negates the reading.** -/
theorem reading_reverse (c : Clock K A) {u v : V} (γ : Aeon K u v) :
    reading c γ.reverse = -reading c γ :=
  wordReading_reverseWord _ _

/-- [proved-derived; formal-checked] Rest reads zero. -/
theorem reading_rest (c : Clock K A) (u : V) : reading c (Aeon.rest u : Aeon K u u) = 0 := rfl

/-- [proved-derived; formal-checked] A closed form reads the two sides of an elementary move alike. -/
theorem wordReading_move {ω : E → A} (hω : IsClosed K ω) {p q : List (E × Bool)}
    (h : Move K p q) : wordReading ω p = wordReading ω q := by
  cases h with
  | backtrack a b s =>
    simp [wordReading_append, stepReading_reverseStep]
  | face a b f =>
    simp [wordReading_append, hω f]
  | faceReversed a b f =>
    simp [wordReading_append, wordReading_reverseWord, hω f]

/-- [proved-derived; formal-checked] A closed form reads homotopic words alike. -/
theorem wordReading_homotopic {ω : E → A} (hω : IsClosed K ω) {p q : List (E × Bool)}
    (h : WordHomotopic K p q) : wordReading ω p = wordReading ω q := by
  induction h with
  | rel x y hxy => exact wordReading_move hω hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- [proved-derived; formal-checked] **A clock's reading is homotopy-invariant.** -/
theorem reading_homotopy_invariant (c : Clock K A) {u v : V} {γ δ : Aeon K u v}
    (h : Homotopic γ δ) : reading c γ = reading c δ :=
  wordReading_homotopic c.closed h

/-- [proved-derived; formal-checked] **Homotopy invariance is exactly closedness.** A form reads
every pair of homotopic words alike if and only if it reads zero around every two-cell. -/
theorem homotopy_invariant_iff_closed (ω : E → A) :
    (∀ p q, WordHomotopic K p q → wordReading ω p = wordReading ω q) ↔ IsClosed K ω := by
  constructor
  · intro h f
    have hm : WordHomotopic K [] (K.boundary f) :=
      Relation.EqvGen.rel _ _ (by simpa using Move.face (K := K) [] [] f)
    simpa using (h _ _ hm).symm
  · intro hω p q hpq
    exact wordReading_homotopic hω hpq

/-! ### The reading is a representation of the aeon groupoid -/

/-- [definition] The reading of an aeon class. -/
def classReading (c : Clock K A) {u v : V} : AeonClass K u v → A :=
  Quotient.lift (s := homotopySetoid K u v) (fun γ => reading c γ)
    (fun _ _ h => reading_homotopy_invariant c h)

@[simp] theorem classReading_mk (c : Clock K A) {u v : V} (γ : Aeon K u v) :
    classReading c (AeonClass.mk γ) = reading c γ := rfl

open CategoryTheory in
/-- [proved-derived; formal-checked] **The clock is a representation of the aeon groupoid in
`(A, +)`: composition is sent to addition.** -/
theorem classReading_comp (c : Clock K A) {u w v : Occurrence K} (f : u ⟶ w) (g : w ⟶ v) :
    classReading c (f ≫ g) = classReading c f + classReading c g := by
  induction f using Quotient.inductionOn with
  | h γ =>
    induction g using Quotient.inductionOn with
    | h δ => exact reading_concat c γ δ

open CategoryTheory in
/-- [proved-derived; formal-checked] The identity arrow reads zero. -/
theorem classReading_id (c : Clock K A) (u : Occurrence K) : classReading c (𝟙 u) = 0 :=
  reading_rest c u

open CategoryTheory in
/-- [proved-derived; formal-checked] The inverse arrow reads the negative. -/
theorem classReading_inv (c : Clock K A) {u v : Occurrence K} (f : u ⟶ v) :
    classReading c (inv f) = -classReading c f := by
  rw [← Groupoid.inv_eq_inv]
  induction f using Quotient.inductionOn with
  | h γ => exact reading_reverse c γ

/-! ### Stokes: exact forms read the boundary -/

variable (K) in
/-- [definition] The exact form `dφ` of a potential on occurrences. -/
def exactForm (φ : V → A) : E → A := fun e => φ (K.tgt e) - φ (K.src e)

theorem stepReading_exactForm (φ : V → A) (s : E × Bool) :
    stepReading (exactForm K φ) s = φ (K.finish s) - φ (K.start s) := by
  rcases s with ⟨e, _ | _⟩ <;>
    simp [stepReading, exactForm, ParametricComplex.start, ParametricComplex.finish]

/-- [proved-derived; formal-checked] **Stokes.** An exact form reads `φ(v) − φ(u)` on every
chained word from `u` to `v`. -/
theorem wordReading_exactForm (φ : V → A) {u v : V} {w : List (E × Bool)}
    (hw : K.Chained u w v) : wordReading (exactForm K φ) w = φ v - φ u := by
  induction w generalizing u with
  | nil =>
    rw [ParametricComplex.chained_nil] at hw
    subst hw
    simp
  | cons s w ih =>
    obtain ⟨h1, h2⟩ := hw
    rw [wordReading_cons, ih h2, stepReading_exactForm, h1]
    abel

/-- [proved-derived; formal-checked] On a well-formed complex every exact form is closed. -/
theorem exactForm_isClosed (hK : K.WellFormed) (φ : V → A) : IsClosed K (exactForm K φ) := by
  intro f
  rw [wordReading_exactForm φ (hK f), sub_self]

/-- [definition] The exact clock `dφ` of a potential, on a well-formed complex. -/
def exactClock (hK : K.WellFormed) (φ : V → A) : Clock K A := ⟨exactForm K φ, exactForm_isClosed hK φ⟩

/-- [proved-derived; formal-checked] An exact clock reads the potential drop of an aeon. -/
theorem reading_exactClock (hK : K.WellFormed) (φ : V → A) {u v : V} (γ : Aeon K u v) :
    reading (exactClock hK φ) γ = φ v - φ u :=
  wordReading_exactForm φ γ.chained

/-- [proved-derived; formal-checked] **Cycle readings are gauge-free.** Regauging a clock by an
exact form leaves the reading of every cycle unchanged. -/
theorem cycle_reading_gauge_free (c : Clock K A) (φ : V → A) {u : V}
    (γ : Aeon K u u) :
    wordReading (c.form + exactForm K φ) γ.steps = reading c γ := by
  rw [wordReading_add, wordReading_exactForm φ γ.chained, sub_self, add_zero]
  rfl

end Clock

/-! ## 3. Cycle readings factor through homology (the `Objects/Pairing` owner) -/

section Homology

variable [Fintype V] [Fintype E] [Fintype F] [DecidableEq V] [DecidableEq E]
variable (K : ParametricComplex V E F)

/-- [definition] The 1-chain of a word: its coordinate at `e` is the reading of the dual basis
form at `e`, the signed number of traversals of `e`. -/
def chainOf (w : List (E × Bool)) : E → ℚ :=
  fun e => wordReading (fun e' => if e' = e then (1 : ℚ) else 0) w

/-- [proved-derived; formal-checked] **The reading is the pairing of the form with the chain.** -/
theorem wordReading_eq_dotProduct (ω : E → ℚ) (w : List (E × Bool)) :
    wordReading ω w = ω ⬝ᵥ chainOf w := by
  induction w with
  | nil => simp [chainOf, dotProduct]
  | cons s w ih =>
    have hstep : stepReading ω s =
        ω ⬝ᵥ (fun e => stepReading (fun e' => if e' = e then (1 : ℚ) else 0) s) := by
      rcases s with ⟨e, _ | _⟩ <;> simp [stepReading, dotProduct]
    have hsplit : chainOf (s :: w) =
        (fun e => stepReading (fun e' => if e' = e then (1 : ℚ) else 0) s) + chainOf w := by
      funext e
      simp [chainOf]
    rw [wordReading_cons, ih, hstep, hsplit, dotProduct_add]

/-- [definition] The edge–occurrence incidence `∂₁`: `+1` at an edge's target, `−1` at its
source, as the exact form of the occurrence's indicator. -/
def incidence₁ : Matrix V E ℚ :=
  fun x e => exactForm K (fun y => if y = x then (1 : ℚ) else 0) e

/-- [definition] The cell–edge incidence `∂₂`: the column of a two-cell is the chain of its
boundary word. -/
def incidence₂ : Matrix E F ℚ := fun e f => chainOf (K.boundary f) e

omit [Fintype V] [Fintype F] in
/-- [proved-derived; formal-checked] **The boundary of an aeon's chain is its endpoint
difference.** -/
theorem incidence₁_mulVec_chainOf {u v : V} {w : List (E × Bool)} (hw : K.Chained u w v) :
    incidence₁ K *ᵥ chainOf w =
      fun x => (if v = x then (1 : ℚ) else 0) - (if u = x then 1 else 0) := by
  funext x
  have h := wordReading_eq_dotProduct (exactForm K (fun y => if y = x then (1 : ℚ) else 0)) w
  rw [wordReading_exactForm _ hw] at h
  exact h.symm

omit [Fintype V] [Fintype F] in
/-- [proved-derived; formal-checked] **A cycle's chain is a cycle** in the owner's sense. -/
theorem chainOf_mem_cycles {u : V} (γ : Aeon K u u) :
    chainOf γ.steps ∈ Holonics.Objects.Pairing.cycles (incidence₁ K) := by
  change incidence₁ K *ᵥ chainOf γ.steps = 0
  rw [incidence₁_mulVec_chainOf K γ.chained]
  funext x
  simp

omit [Fintype V] [Fintype F] in
/-- [proved-derived; formal-checked] `∂₁∂₂ = 0` on a well-formed complex. -/
theorem incidence₁_mul_incidence₂ (hK : K.WellFormed) : incidence₁ K * incidence₂ K = 0 := by
  ext x f
  have h := congrFun (incidence₁_mulVec_chainOf K (hK f)) x
  simp only [sub_self] at h
  rw [Matrix.mul_apply]
  simpa [Matrix.mulVec, dotProduct, incidence₂] using h

omit [Fintype V] [Fintype F] [DecidableEq V] in
/-- [proved-derived; formal-checked] **A clock is a cocycle** in the owner's sense. -/
theorem clock_mem_cocycles (c : Clock K ℚ) :
    c.form ∈ Holonics.Objects.Pairing.cocycles (incidence₂ K) := by
  change (incidence₂ K)ᵀ *ᵥ c.form = 0
  funext f
  have h := wordReading_eq_dotProduct c.form (K.boundary f)
  rw [c.closed f] at h
  simp only [Pi.zero_apply]
  rw [Matrix.mulVec, dotProduct_comm]
  simpa [dotProduct, incidence₂, Matrix.transpose_apply] using h.symm

/-- [proved-derived; formal-checked] **A cycle's reading factors through homology.** The reading
of a cycle by a clock is the owner's class pairing of the clock's cohomology class with the
cycle's homology class. -/
theorem cycle_reading_factors_through_homology (c : Clock K ℚ) {u : V} (γ : Aeon K u u) :
    reading c γ =
      Holonics.Objects.Pairing.classPairing (incidence₁ K) (incidence₂ K)
        (Submodule.Quotient.mk ⟨c.form, clock_mem_cocycles K c⟩)
        (Submodule.Quotient.mk ⟨chainOf γ.steps, chainOf_mem_cycles K γ⟩) := by
  rw [Holonics.Objects.Pairing.classPairing_mk]
  exact wordReading_eq_dotProduct c.form γ.steps

/-- [proved-derived; formal-checked] **Homologous cycles read alike.** If two cycles' chains differ
by the boundary of a two-chain, every clock reads them alike. -/
theorem homologous_cycles_read_alike (hK : K.WellFormed) (c : Clock K ℚ) {u v : V}
    (γ : Aeon K u u) (δ : Aeon K v v) (x : F → ℚ)
    (h : chainOf δ.steps = chainOf γ.steps + incidence₂ K *ᵥ x) :
    reading c δ = reading c γ := by
  have hc := clock_mem_cocycles K c
  have hz := chainOf_mem_cycles K γ
  have := Holonics.Objects.Pairing.classPairing_representatives (incidence₁ K) (incidence₂ K)
    (incidence₁_mul_incidence₂ K hK) c.form (chainOf γ.steps) hc hz 0 x
  rw [Matrix.mulVec_zero, add_zero, ← h] at this
  rw [reading, reading, wordReading_eq_dotProduct, wordReading_eq_dotProduct]
  exact this

end Homology

/-! ## 4. The rate between two receivers -/

section Rate

variable {K : ParametricComplex V E F}

/-- [definition] **The rate** of receiver `a` against receiver `b` along an aeon: the undivided
pair of their two readings, "one per two". -/
def rate (a b : Clock K ℚ) {u v : V} (γ : Aeon K u v) : RatioPresentation ℚ :=
  ⟨reading a γ, reading b γ⟩

/-- [proved-derived; formal-checked] Exchanging the receivers exchanges the pair: neither is the
reference. -/
theorem rate_swap (a b : Clock K ℚ) {u v : V} (γ : Aeon K u v) :
    rate b a γ = ⟨(rate a b γ).den, (rate a b γ).num⟩ := rfl

/-! ### Admitted ratios: the undetermined pair `(0 : 0)` is excluded -/

variable {Q : Type*} [Field Q]

/-- [definition] **An admitted ratio**: not the undetermined pair `(0 : 0)`. Cross-multiplication
(`RatioPresentation.ProjectivelyEq`) relates `(0 : 0)` to every pair, so projective equality is an
equivalence only on admitted ratios (`projectivelyEq_trans`, `undetermined_breaks_transitivity`). -/
def Admitted (p : RatioPresentation Q) : Prop := p.num ≠ 0 ∨ p.den ≠ 0

theorem admitted_iff (p : RatioPresentation Q) :
    Admitted p ↔ p ≠ ⟨0, 0⟩ := by
  unfold Admitted
  constructor
  · rintro (h | h) rfl <;> exact h rfl
  · intro h
    by_contra hc
    push Not at hc
    exact h (RatioPresentation.ext hc.1 hc.2)

/-- [proved-derived; formal-checked] Scaling an admitted ratio by a unit keeps it admitted. -/
theorem Admitted.scale {p : RatioPresentation Q} (hp : Admitted p) {u : Q} (hu : u ≠ 0) :
    Admitted (p.scale u) := by
  rcases hp with h | h
  · exact Or.inl (mul_ne_zero hu h)
  · exact Or.inr (mul_ne_zero hu h)

/-- [proved-derived; formal-checked] **Projective equality is transitive through an admitted
middle.** -/
theorem projectivelyEq_trans {p q r : RatioPresentation Q} (hq : Admitted q)
    (hpq : p.ProjectivelyEq q) (hqr : q.ProjectivelyEq r) : p.ProjectivelyEq r := by
  unfold RatioPresentation.ProjectivelyEq at *
  rcases hq with h | h
  · have hz : (p.num * r.den - r.num * p.den) * q.num = 0 := by
      linear_combination p.num * hqr + r.num * hpq
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right h)
  · have hz : (p.num * r.den - r.num * p.den) * q.den = 0 := by
      linear_combination r.den * hpq + p.den * hqr
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right h)

/-- [counterexample; formal-checked] **The undetermined pair breaks transitivity.** `(1 : 0)` and
`(0 : 1)` are each projectively equal to `(0 : 0)`, but not to each other. -/
theorem undetermined_breaks_transitivity :
    (⟨1, 0⟩ : RatioPresentation ℚ).ProjectivelyEq ⟨0, 0⟩ ∧
      (⟨0, 0⟩ : RatioPresentation ℚ).ProjectivelyEq ⟨0, 1⟩ ∧
      ¬ (⟨1, 0⟩ : RatioPresentation ℚ).ProjectivelyEq ⟨0, 1⟩ ∧
      ¬ Admitted (⟨0, 0⟩ : RatioPresentation ℚ) := by
  simp [RatioPresentation.ProjectivelyEq, Admitted]

/-- [proved-derived; formal-checked] **Composing rates through a third clock is exact**: the pair
`⟨t_a t_b, t_b t_c⟩` is the direct rate of `a` against `c` scaled by the mediating reading `t_b`,
with no hypothesis. -/
theorem rate_through (a b c : Clock K ℚ) {u v : V} (γ : Aeon K u v) :
    (⟨(rate a b γ).num * (rate b c γ).num, (rate a b γ).den * (rate b c γ).den⟩ :
        RatioPresentation ℚ) = (rate a c γ).scale (reading b γ) := by
  ext <;> simp only [rate, RatioPresentation.scale]
  ring

/-- [proved-derived; formal-checked] **No clock is privileged.** When the mediating clock `b`
actually reads the aeon (`t_b ≠ 0`) the composite is the direct rate scaled by a unit: projectively
equal to it, admitted exactly when the direct rate is, and, when `t_c ≠ 0`, with the direct rate's
quotient. At `t_b = 0` the composite is the undetermined pair `(0 : 0)` (`rate_through_zero`). -/
theorem rate_through_projectivelyEq (a b c : Clock K ℚ) {u v : V} (γ : Aeon K u v)
    (hb : reading b γ ≠ 0) :
    (⟨(rate a b γ).num * (rate b c γ).num, (rate a b γ).den * (rate b c γ).den⟩ :
        RatioPresentation ℚ).ProjectivelyEq (rate a c γ) ∧
      (Admitted (rate a c γ) ↔
        Admitted (⟨(rate a b γ).num * (rate b c γ).num, (rate a b γ).den * (rate b c γ).den⟩ :
          RatioPresentation ℚ)) ∧
      (reading c γ ≠ 0 →
        (rate a b γ).num / (rate a b γ).den * ((rate b c γ).num / (rate b c γ).den) =
          (rate a c γ).num / (rate a c γ).den) := by
  rw [rate_through]
  refine ⟨ratioPresentation_projectivelyEq_scale _ _, ⟨fun h => h.scale hb, fun h => ?_⟩,
    fun hc => ?_⟩
  · rcases h with h | h
    · exact Or.inl (right_ne_zero_of_mul h)
    · exact Or.inr (right_ne_zero_of_mul h)
  · simp only [rate]
    field_simp

/-- [counterexample; formal-checked] Through a clock that reads zero the composite is the
undetermined pair. -/
theorem rate_through_zero (a b c : Clock K ℚ) {u v : V} (γ : Aeon K u v)
    (hb : reading b γ = 0) :
    (⟨(rate a b γ).num * (rate b c γ).num, (rate a b γ).den * (rate b c γ).den⟩ :
        RatioPresentation ℚ) = ⟨0, 0⟩ := by
  rw [rate_through, hb]
  ext <;> simp [RatioPresentation.scale]

/-- [proved-derived; formal-checked] On a cycle, regauging either receiver's clock by an exact
form leaves the rate unchanged. -/
theorem rate_regauge_cycle (a b : Clock K ℚ) (φ ψ : V → ℚ) {u : V}
    (γ : Aeon K u u) :
    (⟨wordReading (a.form + exactForm K φ) γ.steps,
        wordReading (b.form + exactForm K ψ) γ.steps⟩ : RatioPresentation ℚ) = rate a b γ := by
  rw [cycle_reading_gauge_free a φ γ, cycle_reading_gauge_free b ψ γ]
  rfl

/-- [definition] A cycle repeated `m` times. -/
def iterate {u : V} (γ : Aeon K u u) : ℕ → Aeon K u u
  | 0 => Aeon.rest u
  | m + 1 => γ.concat (iterate γ m)

theorem reading_iterate {A : Type*} [AddCommGroup A] (c : Clock K A) {u : V} (γ : Aeon K u u)
    (m : ℕ) : reading c (iterate γ m) = m • reading c γ := by
  induction m with
  | zero => rw [zero_smul]; rfl
  | succ m ih => rw [iterate, reading_concat, ih, succ_nsmul']

/-- [proved-derived; formal-checked] **The rate of a cycle does not depend on how often it is
traversed**: repeating it `m` times scales both readings by `m` exactly; for `m ≠ 0` the pair keeps
its projective class and its admission. At `m = 0` the iterate is rest, whose rate is the
undetermined pair `(0 : 0)`. -/
theorem rate_iterate (a b : Clock K ℚ) {u : V} (γ : Aeon K u u) (m : ℕ) :
    rate a b (iterate γ m) = (rate a b γ).scale (m : ℚ) ∧
      (m ≠ 0 → (rate a b (iterate γ m)).ProjectivelyEq (rate a b γ) ∧
        (Admitted (rate a b γ) → Admitted (rate a b (iterate γ m)))) ∧
      rate a b (iterate γ 0) = ⟨0, 0⟩ := by
  have h : ∀ m, rate a b (iterate γ m) = (rate a b γ).scale (m : ℚ) := fun m => by
    simp [rate, RatioPresentation.scale, reading_iterate, nsmul_eq_mul]
  refine ⟨h m, fun hm => ⟨h m ▸ ratioPresentation_projectivelyEq_scale _ _,
    fun hA => h m ▸ hA.scale (by exact_mod_cast hm)⟩, ?_⟩
  rw [h 0]
  ext <;> simp [RatioPresentation.scale]

end Rate

/-! ## 5. Closedness is load-bearing: the filled triangle -/

section Triangle

/-- [definition] The filled triangle: occurrences `0, 1, 2`, edges `0→1`, `1→2`, `2→0`, and one
two-cell bounded by the loop through all three. -/
def filledTriangle : ParametricComplex (Fin 3) (Fin 3) Unit where
  src := ![0, 1, 2]
  tgt := ![1, 2, 0]
  base _ := 0
  boundary _ := [(0, true), (1, true), (2, true)]

theorem filledTriangle_wellFormed : filledTriangle.WellFormed := by
  intro f
  simp [filledTriangle, ParametricComplex.Chained, ParametricComplex.start,
    ParametricComplex.finish]

/-- [definition] The boundary loop of the filled triangle, as an aeon at occurrence `0`. -/
def triangleLoop : Aeon filledTriangle 0 0 := ⟨filledTriangle.boundary (), filledTriangle_wellFormed ()⟩

/-- [proved-derived; formal-checked] The boundary loop is homotopic to rest: one face move. -/
theorem triangleLoop_homotopic_rest : Homotopic (Aeon.rest 0) triangleLoop :=
  Relation.EqvGen.rel _ _ (Move.face (K := filledTriangle) [] [] ())

/-- [definition] A form reading `1` on the edge `0→1` and `0` elsewhere. -/
def edgeForm : Fin 3 → ℚ := ![1, 0, 0]

/-- [counterexample; formal-checked] **A non-closed "clock" is not homotopy-invariant.** The form
is not closed, and it reads the boundary loop `1` although the loop is homotopic to rest, which
reads `0`. -/
theorem nonclosed_form_is_not_homotopy_invariant :
    ¬ IsClosed filledTriangle edgeForm ∧
      Homotopic (Aeon.rest 0) triangleLoop ∧
      wordReading edgeForm (Aeon.rest 0 : Aeon filledTriangle 0 0).steps = 0 ∧
      wordReading edgeForm triangleLoop.steps = 1 := by
  refine ⟨fun h => ?_, triangleLoop_homotopic_rest, rfl, ?_⟩
  · have := h ()
    simp [filledTriangle, edgeForm, wordReading, stepReading] at this
  · simp [triangleLoop, filledTriangle, edgeForm, wordReading, stepReading]

open Holonics.Transport.CellHolonomy in
/-- [proved-derived; formal-checked] **The boundary reading is the cell holonomy.** In the
multiplicative chart the reading of the filled triangle's boundary loop is the owner's
`triangleHolonomy` of the three edge values, so a form on the filled triangle is closed exactly
when its cell holonomy is trivial, and regauging leaves it unchanged
(`CellHolonomy.abelian_holonomy_is_gauge_free`). -/
theorem triangleLoop_reading_is_cell_holonomy {A : Type*} [AddCommGroup A] (ω : Fin 3 → A) :
    Multiplicative.ofAdd (wordReading ω triangleLoop.steps) =
        triangleHolonomy (Multiplicative.ofAdd (ω 0)) (Multiplicative.ofAdd (ω 1))
          (Multiplicative.ofAdd (ω 2)) ∧
      (IsClosed filledTriangle ω ↔
        triangleHolonomy (Multiplicative.ofAdd (ω 0)) (Multiplicative.ofAdd (ω 1))
          (Multiplicative.ofAdd (ω 2)) = 1) := by
  have hread : Multiplicative.ofAdd (wordReading ω triangleLoop.steps) =
      triangleHolonomy (Multiplicative.ofAdd (ω 0)) (Multiplicative.ofAdd (ω 1))
        (Multiplicative.ofAdd (ω 2)) := by
    simp [triangleLoop, filledTriangle, wordReading, stepReading, triangleHolonomy, ofAdd_add,
      mul_assoc]
  refine ⟨hread, ?_⟩
  rw [← hread]
  constructor
  · intro h
    have := h ()
    change wordReading ω triangleLoop.steps = 0 at this
    rw [this, ofAdd_zero]
  · intro h _
    exact Multiplicative.ofAdd.injective (h.trans ofAdd_zero.symm)

/-- [counterexample; formal-checked] **Nor does it factor through homology.** The boundary loop's
chain is the boundary of the two-cell, homologous to the zero chain of rest, yet the non-closed
form separates them. -/
theorem nonclosed_form_does_not_factor_through_homology :
    chainOf triangleLoop.steps =
        chainOf (Aeon.rest 0 : Aeon filledTriangle 0 0).steps +
          incidence₂ filledTriangle *ᵥ (fun _ => (1 : ℚ)) ∧
      wordReading edgeForm triangleLoop.steps ≠
        wordReading edgeForm (Aeon.rest 0 : Aeon filledTriangle 0 0).steps := by
  refine ⟨?_, ?_⟩
  · funext e
    simp [incidence₂, Matrix.mulVec, dotProduct, triangleLoop, Aeon.rest, chainOf]
  · simp [triangleLoop, filledTriangle, edgeForm, wordReading, stepReading, Aeon.rest]

end Triangle

end Holonics.Aeon.Clock.Reading
