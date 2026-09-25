import Holonics.Objects.Pairing
import Holonics.Aeon.Clock.Reading

/-!
# Hodge-decomposed time on a finite cell complex

[definition] Aeon record A2, Lean obligation 3. The carrier of the aeon is a finite cell complex:
a `Foundation/HodgeReceiver.lean::WeightedComplex p q r` whose middle grade is the edges (the
1-cells the motion runs along), with vertices below it and 2-cells above it. The aeon read here is
the **1-chain** of an aeon of the groupoid (`Aeon/Clock/Reading.chainOf`): on a parametric complex
whose incidences are the weighted complex's (`Matches`), the groupoid aeon's reading by any form is
the pairing with its chain (`wordReading_eq_timeReading`), its chain's boundary `∂γ = d₀ᵀ γ` is its
endpoint difference (`boundary_chainOf`), and a groupoid cycle's chain is a cycle here. A **time
form** is any 1-cochain `ω`; its reading over a 1-chain is `⟨ω | γ⟩ = ω ⬝ᵥ γ` (`reading`). A
**clock** is a closed time form (`Aeon/Clock/Reading.Clock`); a general time form need not be one,
and its failure to be one is exactly its production time.

The existing Hodge owner splits every time form uniquely (`TimeSplit`, from
`HodgeReceiver.hodge_decomposition` and `hodge_decomposition_unique`):

```text
ω = dφ + δβ + h          state (exact) + production (coexact) + winding (harmonic)
```

[proved-derived; formal-checked] What is proved, composing `Objects/Pairing.coordinate_stokes`,
`Transport/EditRigidity.mem_range_iff_annihilators_vanish` and the Hodge owner.

1. **State time is boundary-determined.** The exact part reads `⟨dφ | γ⟩ = ⟨φ | ∂γ⟩`
   (`state_reading_eq_potential_drop`), so two aeons with one boundary read it equally
   (`state_reading_boundary_determined`); an aeon from `u` to `v` reads `φ v − φ u`
   (`state_reading_of_walk`). Conversely a clock whose readings are fixed by boundaries is exact
   (`boundary_determined_iff_exact`, through `exact_iff_silent_on_cycles`).
2. **Winding time is a cycle invariant.** A closed clock reads homologous aeons equally
   (`closed_reading_homology_invariant`), in particular its harmonic part
   (`winding_reading_homology_invariant`). On a cycle the state part is silent and the clock reads
   `production + winding` (`cycle_reading_split`).
3. **Production time is curvature.** On a cell boundary `∂c` only the production part reads, and
   its reading is the flux `⟨d₁ω | c⟩` of the clock's curvature through `c`
   (`cell_boundary_reads_production`, `cell_boundary_reading_is_curvature_flux`). Two homologous
   cycles differ in reading by exactly that flux (`homologous_reading_difference_is_curvature`).
   The production part is nonzero exactly when the time form is not closed
   (`production_ne_zero_iff_not_closed`), and exactly when it reads nonzero on some cycle
   (`production_is_curvature`), which may be taken contractible (a cell boundary).
4. **One aeon, one clock.** On a parametric complex matching the weighted complex, a groupoid
   clock (`Reading.Clock`) is a cocycle here and has no production time (`clock_production_zero`);
   a time form is a groupoid clock exactly when its production part vanishes
   (`isClosed_iff_production_zero`).

[counterexample; formal-checked] Witnesses over `ℚ`.
* **Winding time is not boundary-determined** (`hollowTriangle_winding_not_boundary_determined`):
  on the hollow triangle the harmonic clock `(1,1,1)` reads `3` on the loop and `0` on the empty
  aeon, which has the same (zero) boundary.
* **A non-closed time form has production time** (`filledTriangle_split`,
  `filledTriangle_production_reads_the_loop`): on the filled triangle the single tick `(1,0,0)`
  splits as `(2/3,−1/3,−1/3) + (1/3,1/3,1/3) + 0`, and its production part reads `1` on the loop,
  which bounds the face.

[agent-inferred; not formalized] The record reads an aeon as relatively complete for a clock
exactly when that clock reads exactly on it. That reading is not stated here.

Scope: finite complexes over `ℚ` with declared positive weights. The smooth Hodge theorem and the
continuum clock forms of the record are outside this module. No `axiom`, no `sorry`.
-/

noncomputable section

namespace Holonics.Aeon.Production.HodgeTime

open Matrix
open Holonics.Foundation.HodgeReceiver

variable {p q r : ℕ}

/-! ## 1. Aeons, clocks and readings -/

/-- [definition] The boundary `∂γ = d₀ᵀ γ` of an aeon: its bounding occurrences. -/
def boundary (C : WeightedComplex p q r) (γ : Fin q → ℚ) : Fin p → ℚ := C.d₀ᵀ *ᵥ γ

/-- [definition] A **cycle** is an aeon with no boundary. -/
def IsCycle (C : WeightedComplex p q r) (γ : Fin q → ℚ) : Prop := boundary C γ = 0

/-- [definition] The boundary `∂c = d₁ᵀ c` of a 2-chain: a contractible cycle. -/
def cellBoundary (C : WeightedComplex p q r) (c : Fin r → ℚ) : Fin q → ℚ := C.d₁ᵀ *ᵥ c

/-- [definition] The reading `⟨ω | γ⟩` of a time form on an aeon's 1-chain. -/
def reading (ω γ : Fin q → ℚ) : ℚ := ω ⬝ᵥ γ

theorem reading_add_left (ω ω' γ : Fin q → ℚ) :
    reading (ω + ω') γ = reading ω γ + reading ω' γ := add_dotProduct _ _ _

theorem reading_sub_right (ω γ γ' : Fin q → ℚ) :
    reading ω (γ - γ') = reading ω γ - reading ω γ' := dotProduct_sub _ _ _

/-- [proved-derived; formal-checked] A cell boundary is a cycle: `∂∂ = 0`. -/
theorem cellBoundary_isCycle (C : WeightedComplex p q r) (c : Fin r → ℚ) :
    IsCycle C (cellBoundary C c) := by
  unfold IsCycle boundary cellBoundary
  rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, C.dd, Matrix.transpose_zero,
    Matrix.zero_mulVec]

/-- [definition] **The Hodge split of a time form** into state (exact), production (coexact) and
winding (harmonic) time, in the declared constitution metric. -/
structure TimeSplit (C : WeightedComplex p q r) (ω : Fin q → ℚ) where
  state : Fin q → ℚ
  production : Fin q → ℚ
  winding : Fin q → ℚ
  state_mem : state ∈ C.exactPart
  production_mem : production ∈ C.coexactPart
  winding_mem : winding ∈ C.harmonic
  split : ω = state + production + winding

/-- [proved-derived; formal-checked] Every time form has a split (`hodge_decomposition`). -/
theorem timeSplit_nonempty (C : WeightedComplex p q r) (ω : Fin q → ℚ) :
    Nonempty (TimeSplit C ω) := by
  obtain ⟨a, ha, b, hb, h, hh, hω⟩ := C.hodge_decomposition ω
  exact ⟨⟨a, b, h, ha, hb, hh, hω⟩⟩

/-- [proved-derived; formal-checked] And only one (`hodge_decomposition_unique`). -/
theorem timeSplit_unique {C : WeightedComplex p q r} {ω : Fin q → ℚ} (s t : TimeSplit C ω) :
    s.state = t.state ∧ s.production = t.production ∧ s.winding = t.winding :=
  C.hodge_decomposition_unique s.state_mem s.production_mem s.winding_mem t.state_mem
    t.production_mem t.winding_mem (s.split.symm.trans t.split)

/-! ## 2. State time is boundary-determined -/

section State

variable (C : WeightedComplex p q r)

/-- [proved-derived; formal-checked] **Stokes for state time.** `⟨dφ | γ⟩ = ⟨φ | ∂γ⟩`. -/
theorem state_reading_eq_potential_drop (φ : Fin p → ℚ) (γ : Fin q → ℚ) :
    reading (C.d₀ *ᵥ φ) γ = φ ⬝ᵥ boundary C γ := by
  unfold reading boundary
  rw [dotProduct_comm φ, Holonics.Objects.Pairing.coordinate_stokes, dotProduct_comm]

/-- [proved-derived; formal-checked] **State time depends only on the bounding occurrences.** -/
theorem state_reading_boundary_determined {a : Fin q → ℚ} (ha : a ∈ C.exactPart)
    {γ γ' : Fin q → ℚ} (hγ : boundary C γ = boundary C γ') : reading a γ = reading a γ' := by
  obtain ⟨φ, rfl⟩ := (C.mem_exactPart_iff a).mp ha
  rw [state_reading_eq_potential_drop, state_reading_eq_potential_drop, hγ]

/-- [proved-derived; formal-checked] An aeon from `u` to `v` (`∂γ = [v] − [u]`) reads the
potential drop `φ v − φ u`. -/
theorem state_reading_of_walk (φ : Fin p → ℚ) {γ : Fin q → ℚ} {u v : Fin p}
    (hγ : boundary C γ = Pi.single v 1 - Pi.single u 1) :
    reading (C.d₀ *ᵥ φ) γ = φ v - φ u := by
  rw [state_reading_eq_potential_drop, hγ, dotProduct_sub, dotProduct_single, dotProduct_single,
    mul_one, mul_one]

/-- [proved-derived; formal-checked] **A time form is exact exactly when every cycle reads it zero**
(Fredholm alternative, `EditRigidity.mem_range_iff_annihilators_vanish`). -/
theorem exact_iff_silent_on_cycles (x : Fin q → ℚ) :
    x ∈ C.exactPart ↔ ∀ z, IsCycle C z → reading x z = 0 := by
  rw [C.mem_exactPart_iff, Holonics.Transport.EditRigidity.mem_range_iff_annihilators_vanish]
  refine forall_congr' fun z => ?_
  unfold IsCycle boundary reading
  rw [dotProduct_comm]

/-- [proved-derived; formal-checked] **State time is exactly the boundary-determined time.** A
time form reads every pair of aeons with one boundary equally exactly when it is exact. -/
theorem boundary_determined_iff_exact (x : Fin q → ℚ) :
    (∀ γ γ', boundary C γ = boundary C γ' → reading x γ = reading x γ') ↔ x ∈ C.exactPart := by
  constructor
  · intro h
    rw [exact_iff_silent_on_cycles]
    intro z hz
    have := h z 0 (by rw [hz]; simp [boundary])
    simpa [reading] using this
  · intro hx γ γ' hγ
    exact state_reading_boundary_determined C hx hγ

end State

/-! ## 3. Winding time is a cycle invariant -/

section Winding

variable (C : WeightedComplex p q r)

/-- [proved-derived; formal-checked] A cell boundary reads a time form as the flux of its curvature:
`⟨ω | ∂c⟩ = ⟨d₁ω | c⟩`. -/
theorem cell_boundary_reading_is_curvature_flux (ω : Fin q → ℚ) (c : Fin r → ℚ) :
    reading ω (cellBoundary C c) = (C.d₁ *ᵥ ω) ⬝ᵥ c := by
  unfold reading cellBoundary
  rw [dotProduct_comm, Holonics.Objects.Pairing.coordinate_stokes, dotProduct_comm]

/-- [proved-derived; formal-checked] **Homologous aeons differ in reading by the curvature
flux** through the 2-chain between them. -/
theorem homologous_reading_difference_is_curvature (ω : Fin q → ℚ) {z z' : Fin q → ℚ}
    (c : Fin r → ℚ) (hc : z - z' = cellBoundary C c) :
    reading ω z - reading ω z' = (C.d₁ *ᵥ ω) ⬝ᵥ c := by
  rw [← reading_sub_right, hc, cell_boundary_reading_is_curvature_flux]

/-- [proved-derived; formal-checked] **A closed time form (a clock) reads homologous aeons
equally.** -/
theorem closed_reading_homology_invariant {ω : Fin q → ℚ} (hω : ω ∈ C.cocycles)
    {z z' : Fin q → ℚ} (c : Fin r → ℚ) (hc : z - z' = cellBoundary C c) :
    reading ω z = reading ω z' := by
  have h := homologous_reading_difference_is_curvature C ω c hc
  rw [(C.mem_cocycles_iff ω).mp hω, zero_dotProduct] at h
  exact sub_eq_zero.mp h

/-- [proved-derived; formal-checked] **Winding time is a cycle invariant:** the harmonic part of
a time form reads homologous aeons equally. -/
theorem winding_reading_homology_invariant {ω : Fin q → ℚ} (s : TimeSplit C ω)
    {z z' : Fin q → ℚ} (c : Fin r → ℚ) (hc : z - z' = cellBoundary C c) :
    reading s.winding z = reading s.winding z' :=
  closed_reading_homology_invariant C (C.harmonic_le_cocycles s.winding_mem) c hc

/-- [proved-derived; formal-checked] **On a cycle the state part is silent.** A cycle reads a
time form as production plus winding. -/
theorem cycle_reading_split {ω : Fin q → ℚ} (s : TimeSplit C ω) {z : Fin q → ℚ}
    (hz : IsCycle C z) : reading ω z = reading s.production z + reading s.winding z := by
  have hstate : reading s.state z = 0 := (exact_iff_silent_on_cycles C s.state).mp s.state_mem z hz
  rw [congrArg (reading · z) s.split, reading_add_left, reading_add_left, hstate, zero_add]

end Winding

/-! ## 4. Production time is curvature -/

section ProductionTime

variable (C : WeightedComplex p q r)

/-- [proved-derived; formal-checked] **A time form is closed exactly when every cell boundary reads
it zero.** -/
theorem closed_iff_silent_on_cell_boundaries (ω : Fin q → ℚ) :
    ω ∈ C.cocycles ↔ ∀ c, reading ω (cellBoundary C c) = 0 := by
  rw [C.mem_cocycles_iff]
  constructor
  · intro h c
    rw [cell_boundary_reading_is_curvature_flux, h, zero_dotProduct]
  · intro h
    have hself := h (C.d₁ *ᵥ ω)
    rw [cell_boundary_reading_is_curvature_flux] at hself
    exact dotProduct_self_eq_zero.mp hself

/-- [proved-derived; formal-checked] **On a cell boundary only production time reads.** -/
theorem cell_boundary_reads_production {ω : Fin q → ℚ} (s : TimeSplit C ω) (c : Fin r → ℚ) :
    reading ω (cellBoundary C c) = reading s.production (cellBoundary C c) := by
  have hstate : reading s.state (cellBoundary C c) = 0 :=
    (exact_iff_silent_on_cycles C s.state).mp s.state_mem _ (cellBoundary_isCycle C c)
  have hwinding : reading s.winding (cellBoundary C c) = 0 :=
    (closed_iff_silent_on_cell_boundaries C s.winding).mp
      (C.harmonic_le_cocycles s.winding_mem) c
  rw [congrArg (reading · (cellBoundary C c)) s.split, reading_add_left, reading_add_left, hstate,
    hwinding, zero_add, add_zero]

/-- [proved-derived; formal-checked] The time form and its production part have one curvature. -/
theorem production_curvature_eq {ω : Fin q → ℚ} (s : TimeSplit C ω) :
    C.d₁ *ᵥ s.production = C.d₁ *ᵥ ω := by
  have ha : C.d₁ *ᵥ s.state = 0 := C.exactPart_le_cocycles s.state_mem
  have hh : C.d₁ *ᵥ s.winding = 0 := C.harmonic_le_cocycles s.winding_mem
  rw [congrArg (C.d₁ *ᵥ ·) s.split, Matrix.mulVec_add, Matrix.mulVec_add, ha, hh, zero_add,
    add_zero]

/-- [proved-derived; formal-checked] **The production part is nonzero exactly when the time form
is not closed.** A coexact cocycle is zero (`coexact_cocycle_eq_zero`). -/
theorem production_ne_zero_iff_not_closed {ω : Fin q → ℚ} (s : TimeSplit C ω) :
    s.production ≠ 0 ↔ ω ∉ C.cocycles := by
  rw [not_iff_not, C.mem_cocycles_iff, ← production_curvature_eq C s]
  constructor
  · intro h
    rw [h, Matrix.mulVec_zero]
  · intro h
    exact C.coexact_cocycle_eq_zero s.production_mem h

/-- [proved-derived; formal-checked] **Production time is curvature.** The production part reads
nonzero on some cycle exactly when the time form is not closed, and that cycle may be taken
contractible: a cell boundary. -/
theorem production_is_curvature {ω : Fin q → ℚ} (s : TimeSplit C ω) :
    ((∃ z, IsCycle C z ∧ reading s.production z ≠ 0) ↔ ω ∉ C.cocycles) ∧
      ((∃ c, reading s.production (cellBoundary C c) ≠ 0) ↔ ω ∉ C.cocycles) := by
  have hcell : (∃ c, reading s.production (cellBoundary C c) ≠ 0) ↔ ω ∉ C.cocycles := by
    rw [closed_iff_silent_on_cell_boundaries C ω]
    push Not
    refine exists_congr fun c => ?_
    rw [cell_boundary_reads_production C s]
  refine ⟨⟨?_, ?_⟩, hcell⟩
  · rintro ⟨z, -, hz⟩
    rw [← production_ne_zero_iff_not_closed C s]
    rintro h
    rw [h] at hz
    exact hz (by simp [reading])
  · intro h
    obtain ⟨c, hc⟩ := hcell.mpr h
    exact ⟨cellBoundary C c, cellBoundary_isCycle C c, hc⟩

end ProductionTime

/-! ## 5. One aeon: the groupoid's aeons and clocks on the weighted complex -/

section Bridge

open Holonics.Aeon.Clock.Groupoid Holonics.Aeon.Clock.Reading

variable {F : Type*}

/-- [definition] A parametric complex on the weighted complex's cells **matches** it when its
incidences are the weighted complex's: `d₀ = ∂₁ᵀ` and `d₁ = ∂₂ᵀ` (up to the indexing of the
2-cells by `e`). -/
structure Matches (K : ParametricComplex (Fin p) (Fin q) F) (C : WeightedComplex p q r)
    (e : Fin r ≃ F) : Prop where
  d₀_eq : C.d₀ = (incidence₁ K)ᵀ
  d₁_eq : ∀ c j, C.d₁ c j = incidence₂ K j (e c)

/-- [proved-derived; formal-checked] **The groupoid's reading is the pairing with the aeon's
chain**: `wordReading ω γ = reading ω (chainOf γ)` (`Reading.wordReading_eq_dotProduct`). -/
theorem wordReading_eq_timeReading (ω : Fin q → ℚ) (w : List (Fin q × Bool)) :
    wordReading ω w = reading ω (chainOf w) :=
  wordReading_eq_dotProduct ω w

/-- [proved-derived; formal-checked] **The chain of a groupoid aeon from `u` to `v` has boundary
`[v] − [u]`**, and a groupoid cycle's chain is a cycle here. -/
theorem boundary_chainOf {K : ParametricComplex (Fin p) (Fin q) F} {C : WeightedComplex p q r}
    {e : Fin r ≃ F} (hK : Matches K C e) {u v : Fin p} (γ : Aeon K u v) :
    boundary C (chainOf γ.steps) = Pi.single v 1 - Pi.single u 1 ∧
      (u = v → IsCycle C (chainOf γ.steps)) := by
  have hb : boundary C (chainOf γ.steps) = Pi.single v 1 - Pi.single u 1 := by
    unfold boundary
    rw [hK.d₀_eq, Matrix.transpose_transpose, incidence₁_mulVec_chainOf K γ.chained]
    funext x
    simp [Pi.single_apply, eq_comm]
  refine ⟨hb, fun huv => ?_⟩
  subst huv
  unfold IsCycle
  rw [hb, sub_self]

/-- [proved-derived; formal-checked] **A groupoid clock is a cocycle of the weighted complex.** -/
theorem clock_mem_cocycles' {K : ParametricComplex (Fin p) (Fin q) F} {C : WeightedComplex p q r}
    {e : Fin r ≃ F} (hK : Matches K C e) (c : Clock K ℚ) : c.form ∈ C.cocycles := by
  rw [C.mem_cocycles_iff]
  funext i
  have h := congrFun (clock_mem_cocycles K c) (e i)
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct, Pi.zero_apply] at h ⊢
  rw [← h]
  exact Finset.sum_congr rfl fun j _ => by rw [hK.d₁_eq]; rfl

/-- [proved-derived; formal-checked] **A clock has no production time.** For a groupoid clock read
on a matching weighted complex, the production part of its Hodge split is zero
(`production_ne_zero_iff_not_closed`). -/
theorem clock_production_zero {K : ParametricComplex (Fin p) (Fin q) F}
    {C : WeightedComplex p q r} {e : Fin r ≃ F} (hK : Matches K C e) (c : Clock K ℚ)
    (s : TimeSplit C c.form) : s.production = 0 := by
  by_contra h
  exact (production_ne_zero_iff_not_closed C s).mp h (clock_mem_cocycles' hK c)

/-- [proved-derived; formal-checked] **A time form is a groupoid clock exactly when its production
part vanishes.** -/
theorem isClosed_iff_production_zero {K : ParametricComplex (Fin p) (Fin q) F}
    {C : WeightedComplex p q r} {e : Fin r ≃ F} (hK : Matches K C e) (ω : Fin q → ℚ)
    (s : TimeSplit C ω) : IsClosed K ω ↔ s.production = 0 := by
  constructor
  · intro hω
    exact clock_production_zero hK ⟨ω, hω⟩ s
  · intro h0 f
    have hcoc : ω ∈ C.cocycles := by
      by_contra hn
      exact (production_ne_zero_iff_not_closed C s).mpr hn h0
    rw [C.mem_cocycles_iff] at hcoc
    have := congrFun hcoc (e.symm f)
    rw [wordReading_eq_dotProduct]
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this ⊢
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hK.d₁_eq, e.apply_symm_apply, mul_comm]
    rfl

end Bridge

/-! ## 6. Witnesses -/

/-- [definition] The oriented triangle `0 → 1 → 2 → 0`: rows are edges, `−1` at the source and
`+1` at the target. -/
def triangleIncidence : Matrix (Fin 3) (Fin 3) ℚ := !![-1, 1, 0; 0, -1, 1; 1, 0, -1]

/-- [definition] The loop around the triangle, as an aeon. -/
def loop : Fin 3 → ℚ := ![1, 1, 1]

namespace HollowTriangle

/-- [definition] The hollow triangle: no 2-cell, unit metric. -/
def complex : WeightedComplex 3 3 0 := unitMetric triangleIncidence 0 (by simp)

/-- [counterexample; formal-checked] **Winding time is not boundary-determined.** The harmonic
clock `(1,1,1)` reads `3` on the loop and `0` on the empty aeon, which has the same boundary. -/
theorem hollowTriangle_winding_not_boundary_determined :
    loop ∈ complex.harmonic ∧ IsCycle complex loop ∧ boundary complex loop = boundary complex 0 ∧
      reading loop loop = 3 ∧ reading loop 0 = 0 := by
  have hcod : complex.codiff₀ = triangleIncidenceᵀ := unitMetric_codiff₀ _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [WeightedComplex.mem_harmonic_iff, hcod]
    refine ⟨?_, ?_⟩
    · ext i; fin_cases i <;> simp [triangleIncidence, loop, Matrix.mulVec, dotProduct,
        Fin.sum_univ_three]
    · ext i; exact Fin.elim0 i
  · unfold IsCycle boundary
    ext i; fin_cases i <;> simp [complex, unitMetric, triangleIncidence, loop, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  · unfold boundary
    ext i; fin_cases i <;> simp [complex, unitMetric, triangleIncidence, loop, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three]
  · simp [reading, loop, dotProduct, Fin.sum_univ_three]; norm_num
  · simp [reading]

end HollowTriangle

namespace FilledTriangle

/-- [definition] The face boundary: the one 2-cell's boundary is the loop. -/
def faceBoundary : Matrix (Fin 1) (Fin 3) ℚ := !![1, 1, 1]

theorem faceBoundary_dd : faceBoundary * triangleIncidence = 0 := by
  ext i j; fin_cases i; fin_cases j <;>
    simp [faceBoundary, triangleIncidence, Matrix.mul_apply, Fin.sum_univ_three]

/-- [definition] The filled triangle, unit metric. -/
def complex : WeightedComplex 3 3 1 := unitMetric triangleIncidence faceBoundary faceBoundary_dd

/-- [definition] A single tick on the first edge. -/
def tick : Fin 3 → ℚ := ![1, 0, 0]

/-- [counterexample; formal-checked] **The split of a non-closed time form.** On the filled triangle
the tick `(1,0,0)` is `(2/3,−1/3,−1/3)` of state time plus `(1/3,1/3,1/3)` of production time,
with no winding time. -/
def filledTriangle_split : TimeSplit complex tick where
  state := ![2 / 3, -1 / 3, -1 / 3]
  production := ![1 / 3, 1 / 3, 1 / 3]
  winding := 0
  state_mem := by
    refine (complex.mem_exactPart_iff _).mpr ⟨![0, 2 / 3, 1 / 3], ?_⟩
    ext i; fin_cases i <;> simp [complex, unitMetric, triangleIncidence, Matrix.mulVec,
      dotProduct, Fin.sum_univ_three] <;> norm_num
  production_mem := by
    refine (complex.mem_coexactPart_iff _).mpr ⟨![1 / 3], ?_⟩
    ext i; fin_cases i <;> simp [complex, unitMetric, WeightedComplex.codiff₁, faceBoundary,
      Matrix.mulVec, dotProduct]
  winding_mem := complex.harmonic.zero_mem
  split := by
    ext i; fin_cases i <;> simp [tick] <;> norm_num

/-- [counterexample; formal-checked] **Its production time reads the loop.** The tick is not
closed, and its production part reads `1` on the loop, which bounds the face. -/
theorem filledTriangle_production_reads_the_loop :
    tick ∉ complex.cocycles ∧ cellBoundary complex ![1] = loop ∧
      reading filledTriangle_split.production loop = 1 ∧ reading tick loop = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [complex.mem_cocycles_iff]
    intro h
    have := congrFun h 0
    simp [complex, unitMetric, faceBoundary, tick, Matrix.mulVec, dotProduct,
      Fin.sum_univ_three] at this
  · ext i; fin_cases i <;> simp [cellBoundary, complex, unitMetric, faceBoundary, loop,
      Matrix.mulVec, dotProduct]
  · simp [reading, filledTriangle_split, loop, dotProduct, Fin.sum_univ_three]; norm_num
  · simp [reading, tick, loop, dotProduct, Fin.sum_univ_three]

end FilledTriangle

section Audit

#print axioms timeSplit_unique
#print axioms state_reading_boundary_determined
#print axioms boundary_determined_iff_exact
#print axioms winding_reading_homology_invariant
#print axioms cycle_reading_split
#print axioms homologous_reading_difference_is_curvature
#print axioms production_ne_zero_iff_not_closed
#print axioms production_is_curvature
#print axioms boundary_chainOf
#print axioms clock_production_zero
#print axioms isClosed_iff_production_zero
#print axioms HollowTriangle.hollowTriangle_winding_not_boundary_determined
#print axioms FilledTriangle.filledTriangle_production_reads_the_loop

end Audit

end Holonics.Aeon.Production.HodgeTime
