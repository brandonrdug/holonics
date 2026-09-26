import Holonics.HNN.LandmarkTree
import Holonics.Foundation.Standing
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Complex.Order

/-!
# HNN.BornFace: the wave read by the Born rule on the receiving ring's register

[definition; agent-inferred] Decision 33 of the step 4 design (`docs/plans/THE_REBUILD.md`,
"The wave reads by the Born rule"), rebuild step 4 (#73). The computational object is the helical
pair interaction; this owner is its **receiving parametron read quantum-mechanically**: a finitely
correlated (quantum hidden Markov) receiver on the register `ℂ^χ`. Of the winding guide's six
general objects it touches three: the **helix** (the register's phase: amplitudes add with their
phases before they are squared), the **pair** (the reception operators `A_(π,b)` compare the state
with each side of a digit) and **faces and placement** (the Born face on the dyadic partition of
the unit cell, the landmark tree's partition). The tube (one cell per tick), the tower thread (the
digit prefix restricts the cell) and cell holonomy (none claimed: the register is one site) stay
attached through the tree's owners.

```text
state      ρ ⪰ 0 ,  Tr ρ = 1                                  a density on the register ℂ^χ
mass       T_b = re Tr(A_(π,b) ρ A_(π,b)ᴴ)                     digit b at prefix π (its dyadic cell or position)
face       p(b | ρ) = T_b / (T_0 + T_1) ,  refused at T_0 + T_1 = 0
reception  ρ ← A_(π,b) ρ A_(π,b)ᴴ / T_b                         the collapse is the receipt
cell       q(c) = ∏_i p(c_i | ρ after c_0 … c_(i−1))           a dyadic partition of the unit cell
tick       ρ ← U ρ Uᴴ between cells;  here U = 1 (absorbed:  A ρ' Aᴴ = (AU) ρ (AU)ᴴ)
covector   ∂_E log p(b) at operator c = re Tr(Gᴴ E) ,  G = 2 (δ_(bc)/T_b − 1/Z) · A_c ρ
```

[proved-derived; formal-checked] What is proved.

1. **The face is normalized** (`born_face_normalized`): at a positive semidefinite state with a
   positive denominator both digit splits are nonnegative and sum to one; for operators indexed by
   the digit prefix (which covers both declared emissions, per digit position and per dyadic cell)
   the cell faces over the `2^B` classes, each digit read at the state its prefix left, are
   nonnegative and sum to one whenever every denominator a positive-mass prefix reaches is positive
   (`BornAdmits`). A digit of zero mass contributes zero and its subtree is never read. The
   executed face (the Rust owner's) is the landmark tree's executed split `executedSplit M` of the
   exact Born ratio at each prefix, so `HNN/LandmarkTree.cell_faces_partition` applies verbatim:
   every executed cell face is positive and they sum to one (`born_executed_partition`).
2. **The reception keeps a density** (`born_update_trace_one`): `A ρ Aᴴ / T` is positive
   semidefinite with trace one when `T > 0`. A pure state stays pure (`born_pure_stays_pure`:
   `A (ψψᴴ) Aᴴ = (Aψ)(Aψ)ᴴ`), which is why the Rust owner carries the ray `ψ`.
3. **The density is the retained quotient** (`born_state_future_sufficient`): the histories (an
   initial density and the steps received) with `retain` the density fold form a
   `Foundation/Standing.StandingLaw`: every future face factors through the density, so two
   histories with one density have one causal signature; two distinct histories leave one density
   (`two_histories_one_density`). No tape is kept.
4. **The tick is power-neutral and absorbed** (`born_unitary_invariant`, `born_tick_absorbed`): a
   unitary `U` keeps positivity and the trace, and `A (UρUᴴ) Aᴴ = (AU) ρ (AU)ᴴ`, so every face and
   every received state after a fixed tick equal those of the operators `A U` without it.
5. **The shadows** (`born_interference_zero`): at the pure state `ρ = ½[[1,1],[1,1]]` (both
   diagonal entries `½`) the nonzero operators `A₁ = [[1,0],[0,0]]` and `A₂ = [[0,−1],[0,0]]` each
   carry mass `½`, and their sum carries mass `0`: the amplitudes cancel. A nonnegative (hidden
   Markov) receiver of the same width cannot: its masses add (`hmm_mass_add`), and a nonzero
   nonnegative operator carries positive mass at every state with positive entries
   (`hmm_mass_pos`).
6. **The covector** (`born_covector_eq`): the mass is quadratic in the operator,
   `T(A + tE) = T(A) + 2t re Tr(EρAᴴ) + t² T(E)` for Hermitian `ρ` (`bornMass_add_smul`), so the
   log face's derivative along `E` at the observed operator is `2 re Tr(EρA_bᴴ)(1/T_b − 1/Z)` and
   at the other `−2 re Tr(EρA_cᴴ)/Z`, and `re Tr(EρAᴴ) = re Tr((Aρ)ᴴ E)` names the covector
   `G = 2(δ_(bc)/T_b − 1/Z) A_c ρ` in the Frobenius pairing.
7. **The step is Fisher scoring** (`born_fisher_bound`): along the unit direction of its own
   amplitude the split's Fisher information is `(4/Z)(1 − p_c) ≤ 4/Z`, so the prox step `γ = Z/4`
   never exceeds the inverse curvature of the face in any direction.

[open] Owed in #62:
- the general separation of Glasser, Sweke, Pancotti, Eisert and Cirac (2019): a width-`χ` Born
  receiver expresses laws that no nonnegative receiver of polynomial width expresses; only the
  single-zero witness of item 5 is proved here;
- the executed lattice's per-digit residual (the state's rebase and the chart-based covector)
  composed over the passage into a per-cell bound, as for the landmark tree and the word;
- the convergence of the Fisher-scored prox step on the Born face.

| Lean | Rust (`hnn::born`) |
|---|---|
| `bornMass`, `bornSplit`, `born_face_normalized`, `born_executed_partition` | the digit read and the executed dyadic split |
| `bornUpdate`, `born_update_trace_one`, `born_pure_stays_pure` | the reception on the carried ray `ψ` |
| `bornStanding`, `born_state_future_sufficient`, `two_histories_one_density` | the retained state (no tape) |
| `born_unitary_invariant`, `born_tick_absorbed` | the identity tick between cells |
| `born_interference_zero`, `hmm_mass_add`, `hmm_mass_pos` | the tests' interference fixture |
| `bornMass_add_smul`, `born_covector_eq` | the covector deposited by the prox step |
| `born_fisher_bound` | the step `γ = Z/4` |

No `sorry`, no `axiom`, no `native_decide`.
-/

noncomputable section

namespace Holonics.HNN.BornFace

open Matrix
open scoped ComplexOrder
open Holonics.Compression.Core.Cost (toBits)
open Holonics.Foundation.Chronology (transportWord)
open Holonics.Foundation.Standing (StandingLaw causalSignature)

variable {n : Type*} [Fintype n]

/-! ## 1. The mass, the split and the reception -/

/-- [definition] **The Born mass** of an operator at a state: `re Tr(A ρ Aᴴ)`. -/
def bornMass (A ρ : Matrix n n ℂ) : ℝ := (A * ρ * Aᴴ).trace.re

/-- [definition] **A digit's denominator**: the two sides' masses. -/
def bornDen (A : Bool → Matrix n n ℂ) (ρ : Matrix n n ℂ) : ℝ :=
  bornMass (A false) ρ + bornMass (A true) ρ

/-- [definition] **The digit split** `p(b | ρ) = T_b / (T_0 + T_1)`. -/
def bornSplit (A : Bool → Matrix n n ℂ) (ρ : Matrix n n ℂ) (b : Bool) : ℝ :=
  bornMass (A b) ρ / bornDen A ρ

/-- [definition] **The reception** of the side whose operator is `A`: `A ρ Aᴴ / T`. -/
def bornUpdate (A ρ : Matrix n n ℂ) : Matrix n n ℂ :=
  ((bornMass A ρ : ℂ))⁻¹ • (A * ρ * Aᴴ)

/-- A positive semidefinite complex matrix has a real trace. -/
theorem trace_eq_ofReal_re {M : Matrix n n ℂ} (hM : M.PosSemidef) :
    M.trace = ((M.trace.re : ℝ) : ℂ) := by
  have h := Complex.nonneg_iff.mp hM.trace_nonneg
  exact Complex.ext (by simp) (by simp [← h.2])

/-- [proved-derived; formal-checked] Every mass at a positive semidefinite state is nonnegative. -/
theorem bornMass_nonneg {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (A : Matrix n n ℂ) :
    0 ≤ bornMass A ρ :=
  (Complex.nonneg_iff.mp (hρ.mul_mul_conjTranspose_same A).trace_nonneg).1

/-- The reception keeps positivity for every mass (a zero mass gives the zero matrix). -/
theorem bornUpdate_posSemidef {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (A : Matrix n n ℂ) :
    (bornUpdate A ρ).PosSemidef := by
  unfold bornUpdate
  refine (hρ.mul_mul_conjTranspose_same A).smul ?_
  rw [← Complex.ofReal_inv]
  exact Complex.zero_le_real.mpr (inv_nonneg.mpr (bornMass_nonneg hρ A))

/-- [proved-derived; formal-checked] **`born_update_trace_one`.** At a positive semidefinite state
and a positive mass, the received state `A ρ Aᴴ / T` is positive semidefinite with trace one. -/
theorem born_update_trace_one {A ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hT : 0 < bornMass A ρ) :
    (bornUpdate A ρ).PosSemidef ∧ (bornUpdate A ρ).trace = 1 := by
  refine ⟨bornUpdate_posSemidef hρ A, ?_⟩
  unfold bornUpdate
  rw [trace_smul, trace_eq_ofReal_re (hρ.mul_mul_conjTranspose_same A), smul_eq_mul]
  have hne : ((bornMass A ρ : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hT.ne'
  exact inv_mul_cancel₀ hne

/-- [proved-derived; formal-checked] The two splits of a digit, nonnegative and normalized, at a
positive semidefinite state with a positive denominator. -/
theorem born_split_laws {A : Bool → Matrix n n ℂ} {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (hZ : 0 < bornDen A ρ) :
    (∀ b, 0 ≤ bornSplit A ρ b) ∧ bornSplit A ρ false + bornSplit A ρ true = 1 := by
  refine ⟨fun b => div_nonneg (bornMass_nonneg hρ _) hZ.le, ?_⟩
  unfold bornSplit
  rw [← add_div]
  exact div_self hZ.ne'

/-- Every split at a positive semidefinite state is nonnegative (a zero denominator reads zero). -/
theorem bornSplit_nonneg {A : Bool → Matrix n n ℂ} {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)
    (b : Bool) : 0 ≤ bornSplit A ρ b :=
  div_nonneg (bornMass_nonneg hρ _)
    (add_nonneg (bornMass_nonneg hρ _) (bornMass_nonneg hρ _))

/-! ## 2. The cell face on the dyadic partition -/

/-- [definition] **The cell face** after the prefix `pre` at the state `ρ`: the product of the
digit splits along the digits, each read at the state its prefix left. The operators are indexed
by the digit prefix (the dyadic cell; a per-position emission reads only its length). -/
def bornEmit (A : List Bool → Bool → Matrix n n ℂ) :
    List Bool → Matrix n n ℂ → List Bool → ℝ
  | _, _, [] => 1
  | pre, ρ, b :: rest =>
      bornSplit (A pre) ρ b * bornEmit A (pre ++ [b]) (bornUpdate (A pre b) ρ) rest

/-- [definition] **The refusal's hypothesis over a cell**: every denominator that a prefix of
positive mass reaches, within `w` digits, is positive. -/
def BornAdmits (A : List Bool → Bool → Matrix n n ℂ) : ℕ → List Bool → Matrix n n ℂ → Prop
  | 0, _, _ => True
  | w + 1, pre, ρ =>
      0 < bornDen (A pre) ρ ∧
        ∀ b, 0 < bornMass (A pre b) ρ → BornAdmits A w (pre ++ [b]) (bornUpdate (A pre b) ρ)

theorem bornEmit_nonneg (A : List Bool → Bool → Matrix n n ℂ) :
    ∀ (l pre : List Bool) (ρ : Matrix n n ℂ), ρ.PosSemidef → 0 ≤ bornEmit A pre ρ l
  | [], _, _, _ => zero_le_one
  | b :: rest, pre, _, hρ =>
      mul_nonneg (bornSplit_nonneg hρ b)
        (bornEmit_nonneg A rest (pre ++ [b]) _ (bornUpdate_posSemidef hρ _))

/-- One side of a digit's subtree: its split times the subtree's sum is the split, when the
subtree is admitted or the side carries no mass. -/
theorem side_sum {A : List Bool → Bool → Matrix n n ℂ} {w : ℕ} {pre : List Bool}
    {ρ : Matrix n n ℂ} (b : Bool)
    (ih : 0 < bornMass (A pre b) ρ →
      ∑ c ∈ Finset.range (2 ^ w), bornEmit A (pre ++ [b]) (bornUpdate (A pre b) ρ)
        (toBits w c) = 1)
    (hρ : ρ.PosSemidef) :
    bornSplit (A pre) ρ b *
        ∑ c ∈ Finset.range (2 ^ w), bornEmit A (pre ++ [b]) (bornUpdate (A pre b) ρ)
          (toBits w c) = bornSplit (A pre) ρ b := by
  rcases (bornMass_nonneg hρ (A pre b)).lt_or_eq with h | h
  · rw [ih h, mul_one]
  · simp [bornSplit, ← h]

/-- [proved-derived; formal-checked] **`born_face_normalized`.**
* At a positive semidefinite state with a positive denominator, both digit splits are nonnegative
  and they sum to one.
* For operators indexed by the digit prefix, at a positive semidefinite state, every cell face (the
  emission of the cell's `w` odometer digits `toBits w c`) is nonnegative, and when every
  denominator a prefix of positive mass reaches is positive (`BornAdmits`), the faces of the cells
  `c < 2^w` sum to one. -/
theorem born_face_normalized :
    (∀ (A : Bool → Matrix n n ℂ) (ρ : Matrix n n ℂ), ρ.PosSemidef → 0 < bornDen A ρ →
        (∀ b, 0 ≤ bornSplit A ρ b) ∧ bornSplit A ρ false + bornSplit A ρ true = 1) ∧
      ∀ (A : List Bool → Bool → Matrix n n ℂ) (w : ℕ) (pre : List Bool) (ρ : Matrix n n ℂ),
        ρ.PosSemidef →
          (∀ c, 0 ≤ bornEmit A pre ρ (toBits w c)) ∧
            (BornAdmits A w pre ρ → ∑ c ∈ Finset.range (2 ^ w), bornEmit A pre ρ (toBits w c) = 1)
          := by
  refine ⟨fun A ρ hρ hZ => born_split_laws hρ hZ, fun A w => ?_⟩
  induction w with
  | zero =>
    intro pre ρ _
    exact ⟨fun _ => by simp [toBits, bornEmit], fun _ => by simp [toBits, bornEmit]⟩
  | succ w ih =>
    intro pre ρ hρ
    refine ⟨fun c => bornEmit_nonneg A _ pre ρ hρ, fun ⟨hZ, hadm⟩ => ?_⟩
    rw [show 2 ^ (w + 1) = 2 ^ w + 2 ^ w by ring, Finset.sum_range_add]
    have hside : ∀ b : Bool,
        ∑ c ∈ Finset.range (2 ^ w),
            bornEmit A pre ρ (toBits (w + 1) (if b then 2 ^ w + c else c)) =
          bornSplit (A pre) ρ b := by
      intro b
      rw [← side_sum b (fun hb => (ih (pre ++ [b]) _ (bornUpdate_posSemidef hρ _)).2
        (hadm b hb)) hρ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c hc => ?_
      have hc' := Finset.mem_range.mp hc
      cases b
      · simp only [Bool.false_eq_true, if_false]
        rw [LandmarkTree.toBits_succ_low hc', bornEmit]
      · simp only [if_true]
        rw [LandmarkTree.toBits_succ_high hc', bornEmit]
    have h0 := hside false
    have h1 := hside true
    simp only [Bool.false_eq_true, if_false, if_true] at h0 h1
    rw [h0, h1]
    exact (born_split_laws hρ hZ).2

/-- [proved-derived; formal-checked] **`born_executed_partition`.** The executed Born face rounds
each digit's exact ratio `q0 π` (the Born split of side `0` at the prefix `π`, rational in the
Rust carrier) by the landmark tree's executed split at `M ≥ 1`
(`HNN/LandmarkTree.executed_split_laws`): every executed cell face is positive and the faces sum to
one over the cells, a dyadic partition of the unit cell (`HNN/LandmarkTree.cell_faces_partition`,
verbatim). -/
theorem born_executed_partition {M : ℕ} (hM : 1 ≤ M) (q0 : List Bool → ℚ) (w : ℕ) :
    (∀ c, 0 < LandmarkTree.emit (fun π b => LandmarkTree.executedSplit M (q0 π) b) []
        (toBits w c)) ∧
      ∑ c ∈ Finset.range (2 ^ w),
        LandmarkTree.emit (fun π b => LandmarkTree.executedSplit M (q0 π) b) [] (toBits w c) = 1 :=
  (LandmarkTree.cell_faces_partition (fun π b => LandmarkTree.executedSplit M (q0 π) b)
    (fun π => (LandmarkTree.executed_split_laws hM (q0 π)).2.2.1) w).2.2 hM q0

/-! ## 3. Pure states, the tick and its absorption -/

/-- [proved-derived; formal-checked] **`born_pure_stays_pure`.** The reception of a pure state is
pure: `A (ψψᴴ) Aᴴ = (Aψ)(Aψ)ᴴ`. So from a pure start every received state (and every tick's
image, `A = U`) is the ray of `Aψ`, which the Rust owner carries. -/
theorem born_pure_stays_pure (A : Matrix n n ℂ) (ψ : n → ℂ) :
    A * vecMulVec ψ (star ψ) * Aᴴ = vecMulVec (A *ᵥ ψ) (star (A *ᵥ ψ)) := by
  rw [mul_vecMulVec, vecMulVec_mul, star_mulVec]

/-- [proved-derived; formal-checked] **`born_unitary_invariant`.** A unitary tick keeps a density:
`U ρ Uᴴ` is positive semidefinite with the trace of `ρ`. -/
theorem born_unitary_invariant [DecidableEq n] {U : Matrix n n ℂ} (hU : U ∈ Matrix.unitaryGroup n ℂ)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) :
    (U * ρ * Uᴴ).PosSemidef ∧ (U * ρ * Uᴴ).trace = ρ.trace := by
  refine ⟨hρ.mul_mul_conjTranspose_same U, ?_⟩
  have hUU : Uᴴ * U = 1 := by
    rw [← star_eq_conjTranspose]
    exact Matrix.mem_unitaryGroup_iff'.mp hU
  rw [trace_mul_comm, ← Matrix.mul_assoc, hUU, Matrix.one_mul]

/-- [proved-derived; formal-checked] **`born_tick_absorbed`.** A fixed tick `U` before a digit is
absorbed by the digit's operators: the masses, the splits and the received states at `U ρ Uᴴ`
under `A` are those at `ρ` under `A U`. -/
theorem born_tick_absorbed (A U ρ : Matrix n n ℂ) (B : Bool → Matrix n n ℂ) (b : Bool) :
    bornMass A (U * ρ * Uᴴ) = bornMass (A * U) ρ ∧
      bornUpdate A (U * ρ * Uᴴ) = bornUpdate (A * U) ρ ∧
      bornSplit B (U * ρ * Uᴴ) b = bornSplit (fun c => B c * U) ρ b := by
  have key : ∀ A : Matrix n n ℂ, A * (U * ρ * Uᴴ) * Aᴴ = A * U * ρ * (A * U)ᴴ := by
    intro A
    rw [conjTranspose_mul]
    simp only [Matrix.mul_assoc]
  have hmass : ∀ A : Matrix n n ℂ, bornMass A (U * ρ * Uᴴ) = bornMass (A * U) ρ := by
    intro A
    unfold bornMass
    rw [key]
  refine ⟨hmass A, ?_, ?_⟩
  · unfold bornUpdate
    rw [hmass, key]
  · unfold bornSplit bornDen
    rw [hmass, hmass, hmass]

/-! ## 4. The density is the retained quotient -/

/-- [definition] **A received step**: the digit's operator pair and the side observed. -/
abbrev BornStep (n : Type*) := (Bool → Matrix n n ℂ) × Bool

/-- [definition] **A history**: the initial density and the steps received, oldest first. -/
abbrev BornHistory (n : Type*) := Matrix n n ℂ × List (BornStep n)

/-- [definition] The density's step: receive side `g.2` through `g.1 g.2`. -/
def densityStep (g : BornStep n) (ρ : Matrix n n ℂ) : Matrix n n ℂ := bornUpdate (g.1 g.2) ρ

/-- [definition] **The retained density**: the fold of the receptions over the history. -/
def retainDensity (h : BornHistory n) : Matrix n n ℂ :=
  h.2.foldl (fun ρ g => densityStep g ρ) h.1

/-- [definition] A history grows by appending the step received. -/
def extendHistory (g : BornStep n) (h : BornHistory n) : BornHistory n := (h.1, h.2 ++ [g])

theorem retainDensity_extend (g : BornStep n) (h : BornHistory n) :
    retainDensity (extendHistory g h) = densityStep g (retainDensity h) := by
  simp [retainDensity, extendHistory, List.foldl_append]

/-- [definition] **The Born receiver as a standing law**: sources are histories, a receiver is a
digit's operator pair with the side it reads, the face is that side's split at the retained
density, and a future word is reopened from the density alone. -/
def bornStanding :
    StandingLaw (BornStep n) (BornStep n) (BornHistory n) (Matrix n n ℂ) ℝ where
  transport := extendHistory
  observe := fun r h => bornSplit r.1 (retainDensity h) r.2
  retain := retainDensity
  reopen := fun r word ρ => bornSplit r.1 (transportWord densityStep word ρ) r.2
  sufficient := by
    intro r word h
    have := Holonics.Foundation.Chronology.generatorEquivarianceExtendsToEveryTransportWord
      extendHistory densityStep retainDensity (fun g h => retainDensity_extend g h) word h
    simp only [this]

/-- [proved-derived; formal-checked] **`born_state_future_sufficient`.** Every admitted future face
of the Born receiver factors through the retained density (`bornStanding.sufficient`), so two
histories that leave one density have one causal signature: every future word of receptions reads
the same face at every receiver. -/
theorem born_state_future_sufficient (r : BornStep n) (word : List (BornStep n))
    (h : BornHistory n) :
    bornStanding.reopen r word (retainDensity h) =
        bornSplit r.1 (retainDensity (transportWord extendHistory word h)) r.2 ∧
      ∀ h' : BornHistory n, retainDensity h = retainDensity h' →
        causalSignature bornStanding.observe bornStanding.transport h =
          causalSignature bornStanding.observe bornStanding.transport h' :=
  ⟨bornStanding.sufficient r word h, fun _ he => bornStanding.causalSignature_eq_of_retain_eq he⟩

/-- [proved-derived; formal-checked] **Retention is a quotient, not a tape.** At a density of trace
one, receiving through the identity leaves the density: the empty history and the history of one
such step are distinct and leave one density. -/
theorem two_histories_one_density [DecidableEq n] {ρ : Matrix n n ℂ} (hρ : ρ.trace = 1) :
    ((ρ, []) : BornHistory n) ≠ (ρ, [((fun _ => 1), false)]) ∧
      retainDensity ((ρ, []) : BornHistory n) = retainDensity (ρ, [((fun _ => 1), false)]) := by
  refine ⟨by simp, ?_⟩
  simp [retainDensity, densityStep, bornUpdate, bornMass, hρ]

/-! ## 5. The shadows: destructive interference -/

/-- [definition] The pure state `½[[1, 1], [1, 1]]`, the ray of `(1, 1)`. -/
def plusState : Matrix (Fin 2) (Fin 2) ℂ := !![1 / 2, 1 / 2; 1 / 2, 1 / 2]

/-- [definition] The two operators whose amplitudes cancel at `plusState`. -/
def shadowLeft : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]

/-- See `shadowLeft`. -/
def shadowRight : Matrix (Fin 2) (Fin 2) ℂ := !![0, -1; 0, 0]

/-- [definition] **The mass of a nonnegative (hidden Markov) receiver** at a probability state
`π`: `Σ_i (M π)_i`. -/
def hmmMass {m : Type*} [Fintype m] (M : Matrix m m ℝ) (π : m → ℝ) : ℝ := ∑ i, (M *ᵥ π) i

/-- [proved-derived; formal-checked] A nonnegative receiver's masses add: no cancellation. -/
theorem hmm_mass_add {m : Type*} [Fintype m] (M₁ M₂ : Matrix m m ℝ) (π : m → ℝ) :
    hmmMass (M₁ + M₂) π = hmmMass M₁ π + hmmMass M₂ π := by
  simp [hmmMass, add_mulVec, Finset.sum_add_distrib]

/-- [proved-derived; formal-checked] A nonzero nonnegative operator carries positive mass at every
state with positive entries. -/
theorem hmm_mass_pos {m : Type*} [Fintype m] {M : Matrix m m ℝ} (hM : ∀ i j, 0 ≤ M i j)
    (hne : M ≠ 0) {π : m → ℝ} (hπ : ∀ j, 0 < π j) : 0 < hmmMass M π := by
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    by_contra h
    exact hne (Matrix.ext fun i j => by
      by_contra hij
      exact h ⟨i, j, hij⟩)
  unfold hmmMass
  refine Finset.sum_pos' (fun k _ => ?_) ⟨i, Finset.mem_univ _, ?_⟩
  · exact Finset.sum_nonneg fun l _ => mul_nonneg (hM k l) (hπ l).le
  · refine Finset.sum_pos' (fun l _ => mul_nonneg (hM i l) (hπ l).le)
      ⟨j, Finset.mem_univ _, mul_pos ((hM i j).lt_of_ne (Ne.symm hij)) (hπ j)⟩

theorem plusState_eq : plusStateᴴ * plusState = plusState := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [plusState, Matrix.mul_apply, Fin.sum_univ_two, conjTranspose_apply, map_ofNat] <;>
    norm_num

/-- [proved-derived; formal-checked] **`born_interference_zero`.** The pure state `ρ = ½[[1,1],[1,1]]`
is a density whose diagonal entries are positive; the operators `A₁ = [[1,0],[0,0]]` and
`A₂ = [[0,−1],[0,0]]` are nonzero, each carries mass `½`, and their sum carries mass `0`. A
nonnegative receiver of the same width never produces that zero: for nonzero nonnegative `M₁`,
`M₂` and any state with positive entries (such as `ρ`'s diagonal), the sum's mass is positive. -/
theorem born_interference_zero :
    (plusState.PosSemidef ∧ plusState.trace = 1 ∧ ∀ i, 0 < (plusState i i).re) ∧
      shadowLeft ≠ 0 ∧ shadowRight ≠ 0 ∧
      bornMass shadowLeft plusState = 1 / 2 ∧ bornMass shadowRight plusState = 1 / 2 ∧
      bornMass (shadowLeft + shadowRight) plusState = 0 ∧
      ∀ (M₁ M₂ : Matrix (Fin 2) (Fin 2) ℝ), (∀ i j, 0 ≤ M₁ i j) → (∀ i j, 0 ≤ M₂ i j) →
        M₁ ≠ 0 → M₂ ≠ 0 → ∀ π : Fin 2 → ℝ, (∀ j, 0 < π j) → 0 < hmmMass (M₁ + M₂) π := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← plusState_eq]
    exact posSemidef_conjTranspose_mul_self _
  · simp [plusState, Matrix.trace, Fin.sum_univ_two]; norm_num
  · intro i; fin_cases i <;> simp [plusState]
  · intro h
    have := congrFun (congrFun h 0) 0
    simp [shadowLeft] at this
  · intro h
    have := congrFun (congrFun h 0) 1
    simp [shadowRight] at this
  · simp [bornMass, shadowLeft, plusState, Matrix.trace, Fin.sum_univ_two, vecMul, dotProduct,
      conjTranspose_apply]
  · simp [bornMass, shadowRight, plusState, Matrix.trace, Fin.sum_univ_two, vecMul, dotProduct,
      conjTranspose_apply]
  · simp [bornMass, shadowLeft, shadowRight, plusState, Matrix.trace, Fin.sum_univ_two, vecMul,
      dotProduct, conjTranspose_apply]
  · intro M₁ M₂ h₁ h₂ hne₁ hne₂ π hπ
    rw [hmm_mass_add]
    exact add_pos (hmm_mass_pos h₁ hne₁ hπ) (hmm_mass_pos h₂ hne₂ hπ)

/-! ## 6. The covector -/

/-- The cross term's two halves have one real part, for Hermitian `ρ`. -/
theorem cross_re {A E ρ : Matrix n n ℂ} (hρ : ρᴴ = ρ) :
    (A * ρ * Eᴴ).trace.re = (E * ρ * Aᴴ).trace.re := by
  have : A * ρ * Eᴴ = (E * ρ * Aᴴ)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hρ, Matrix.mul_assoc]
  rw [this, trace_conjTranspose]
  simp

/-- [proved-derived; formal-checked] **The mass is quadratic in the operator**:
`T(A + tE) = T(A) + 2t re Tr(EρAᴴ) + t² T(E)` for Hermitian `ρ` and real `t`. -/
theorem bornMass_add_smul {A E ρ : Matrix n n ℂ} (hρ : ρᴴ = ρ) (t : ℝ) :
    bornMass (A + t • E) ρ =
      bornMass A ρ + 2 * t * (E * ρ * Aᴴ).trace.re + t ^ 2 * bornMass E ρ := by
  unfold bornMass
  have hE : (t • E)ᴴ = t • Eᴴ := by
    rw [conjTranspose_smul]; simp
  rw [conjTranspose_add, hE]
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul, trace_add,
    trace_smul, Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [cross_re (A := A) (E := E) hρ]
  ring

/-- The Riesz form: `re Tr(EρAᴴ) = re Tr((Aρ)ᴴ E)` for Hermitian `ρ` (the traces agree). -/
theorem riesz_trace {A E ρ : Matrix n n ℂ} (hρ : ρᴴ = ρ) :
    (E * ρ * Aᴴ).trace = ((A * ρ)ᴴ * E).trace := by
  rw [conjTranspose_mul, hρ, Matrix.mul_assoc E, trace_mul_comm E]

/-- The derivative at `0` of the mass along `E`. -/
theorem hasDerivAt_bornMass {A E ρ : Matrix n n ℂ} (hρ : ρᴴ = ρ) :
    HasDerivAt (fun t : ℝ => bornMass (A + t • E) ρ) (2 * (E * ρ * Aᴴ).trace.re) 0 := by
  have hfun : (fun t : ℝ => bornMass (A + t • E) ρ) =
      fun t => bornMass A ρ + 2 * t * (E * ρ * Aᴴ).trace.re + t ^ 2 * bornMass E ρ :=
    funext fun t => bornMass_add_smul hρ t
  rw [hfun]
  have h1 : HasDerivAt (fun t : ℝ => 2 * t * (E * ρ * Aᴴ).trace.re)
      (2 * 1 * (E * ρ * Aᴴ).trace.re) 0 :=
    ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const _
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2 * bornMass E ρ)
      ((2 : ℕ) * (0 : ℝ) ^ (2 - 1) * 1 * bornMass E ρ) 0 :=
    ((hasDerivAt_id (0 : ℝ)).pow 2).mul_const _
  refine (((hasDerivAt_const (0 : ℝ) (bornMass A ρ)).add h1).add h2).congr_deriv ?_
  simp

/-- [proved-derived; formal-checked] **`born_covector_eq`.** With `T_b = bornMass P ρ > 0` the
observed side's mass, `T_c = bornMass Q ρ ≥ 0` the other's and `Z = T_b + T_c`, for Hermitian `ρ`:
* along `E` at the observed operator, `d/dt log p_b = 2 re Tr(EρPᴴ)(1/T_b − 1/Z)`;
* along `E` at the other operator, `d/dt log p_b = −2 re Tr(EρQᴴ)/Z`;
* `re Tr(EρAᴴ) = re Tr((Aρ)ᴴ E)`, so the covector in the Frobenius pairing is
  `G = 2(δ_(bc)/T_b − 1/Z) · A_c ρ`, the formula the Rust owner deposits. -/
theorem born_covector_eq {P Q E ρ : Matrix n n ℂ} (hρ : ρᴴ = ρ) (hP : 0 < bornMass P ρ)
    (hQ : 0 ≤ bornMass Q ρ) :
    HasDerivAt
        (fun t : ℝ => Real.log (bornMass (P + t • E) ρ /
          (bornMass (P + t • E) ρ + bornMass Q ρ)))
        (2 * (E * ρ * Pᴴ).trace.re * (1 / bornMass P ρ - 1 / (bornMass P ρ + bornMass Q ρ))) 0 ∧
      HasDerivAt
        (fun t : ℝ => Real.log (bornMass P ρ / (bornMass P ρ + bornMass (Q + t • E) ρ)))
        (-2 * (E * ρ * Qᴴ).trace.re / (bornMass P ρ + bornMass Q ρ)) 0 ∧
      ∀ A : Matrix n n ℂ, (E * ρ * Aᴴ).trace.re = ((A * ρ)ᴴ * E).trace.re := by
  set a := bornMass P ρ
  set s := bornMass Q ρ
  have hZ : 0 < a + s := by linarith
  refine ⟨?_, ?_, fun A => by rw [riesz_trace hρ]⟩
  · have hT := hasDerivAt_bornMass (A := P) (E := E) hρ
    have hval : bornMass (P + (0 : ℝ) • E) ρ = a := by simp [a]
    have hden : HasDerivAt (fun t : ℝ => bornMass (P + t • E) ρ + s)
        (2 * (E * ρ * Pᴴ).trace.re) 0 := hT.add_const s
    have hq := hT.div hden (by show bornMass (P + (0 : ℝ) • E) ρ + s ≠ 0; rw [hval]; exact hZ.ne')
    have hlog := hq.log (by
      show bornMass (P + (0 : ℝ) • E) ρ / (bornMass (P + (0 : ℝ) • E) ρ + s) ≠ 0
      rw [hval]; exact (div_pos hP hZ).ne')
    refine hlog.congr_deriv ?_
    simp only [Pi.div_apply, hval]
    field_simp
  · have hT := hasDerivAt_bornMass (A := Q) (E := E) hρ
    have hval : bornMass (Q + (0 : ℝ) • E) ρ = s := by simp [s]
    have hden : HasDerivAt (fun t : ℝ => a + bornMass (Q + t • E) ρ)
        (2 * (E * ρ * Qᴴ).trace.re) 0 := hT.const_add a
    have hq := (hasDerivAt_const (0 : ℝ) a).div hden
      (by show a + bornMass (Q + (0 : ℝ) • E) ρ ≠ 0; rw [hval]; exact hZ.ne')
    have hlog := hq.log (by
      show a / (a + bornMass (Q + (0 : ℝ) • E) ρ) ≠ 0
      rw [hval]; exact (div_pos hP hZ).ne')
    refine hlog.congr_deriv ?_
    simp only [Pi.div_apply, hval]
    field_simp
    ring

/-! ## 7. The step: Fisher scoring -/

/-- [proved-derived; formal-checked] **`born_fisher_bound`.** Along the unit direction of side
`c`'s own amplitude (`E = A_c/s`, `s² = T_c`, so `re Tr(EρA_cᴴ) = s`), `born_covector_eq` gives
the scores `2s(1/T_c − 1/Z)` for side `c` and `−2s/Z` for the other; their Fisher information
`p_c score_c² + p_o score_o²` is `(4/Z)(1 − p_c) ≤ 4/Z`. The prox step `γ = Z/4` is therefore at
most the inverse curvature of the face along every such direction (Fisher scoring). -/
theorem born_fisher_bound {Tc To s : ℝ} (hc : 0 < Tc) (ho : 0 ≤ To) (hs : 0 < s)
    (hsq : s ^ 2 = Tc) :
    Tc / (Tc + To) * (2 * s * (1 / Tc - 1 / (Tc + To))) ^ 2 +
        To / (Tc + To) * (-2 * s / (Tc + To)) ^ 2 =
      4 / (Tc + To) * (1 - Tc / (Tc + To)) ∧
      4 / (Tc + To) * (1 - Tc / (Tc + To)) ≤ 4 / (Tc + To) := by
  have hZ : 0 < Tc + To := by linarith
  refine ⟨?_, ?_⟩
  · rw [← hsq]
    field_simp
    ring
  · have h4 : 0 ≤ 4 / (Tc + To) := by positivity
    have hp : 0 ≤ Tc / (Tc + To) := by positivity
    nlinarith

end Holonics.HNN.BornFace
