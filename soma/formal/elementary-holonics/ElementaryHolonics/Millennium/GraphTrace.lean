import ElementaryHolonics.Millennium.TraceSequence
import Mathlib.Tactic

/-!
# GraphTrace: the geodesics of the tetrahedron ride the trace sequence

The proved spectral-placement instance of the Riemann route — spectrum against closed orbits as
an exact ledger — has a finite home: the non-backtracking walk structure of a regular graph,
where the Ihara zeta is `det(1 − uB)⁻¹` for the dart-transition matrix `B` and graph-RH is the
Ramanujan condition.  **The determinant face already has an exact owner in this repository** —
`crates/relational-geometry/src/receiver_topology.rs` computes the Ihara signature with an Euler-
product cross-check and `crates/holonic-engine/examples/the_graph_is_asked_the_ramanujan_question.rs`
drives the Ramanujan question with a negative control — so this file does **not** rebuild it.
What had no owner anywhere is the **trace formula proper**: the spectral identity equating the
enumerated closed-geodesic population to a sum of trace sequences.  This file proves it on the
tetrahedron `K₄`, joining the dynamical side to `TraceSequence.lean` — the same sequence whose
level-one bound carries the Weil exponent.

What is proved, all kernel-computed, no `native_decide`:

* **the dynamical side is enumerated, not declared**: `closedDartWalks k` counts the closed
  non-backtracking dart walks of length `k` on the twelve darts of `K₄`, by executing the
  successor relation — the walk population is derived from the incidence condition, never from
  an authored table of counts;
* **the trace formula**: for `k ≤ 6`,
  `closedDartWalks k = trace 3 2 k + 3·trace (−1) 2 k + (4 if k even else 0)` — the geodesic
  population **is** the trace-sequence sum, with the trivial term `2(m−n)` carried by the even
  indicator.  The seven values `12, 0, 0, 24, 24, 0, 96` were confirmed by three independent
  derivations before this file was written: hand enumeration, the spectral factoring of the
  Ihara determinant, and exact powers of the explicit `12×12` dart matrix;
* **the spectrum arrives by exhibited realizers, not by declaration**: the Perron vector and
  three independent winding vectors are exhibited with their eigenvalue equations
  (`A·v = 3v`, `A·w = −w`), and their independence is a computed nonzero determinant — the
  multiplicity three is *paid for*, never authored;
* **placement rides, by instantiation**: `normSq (alpha (−1) 2) = 2` — the winding root sits on
  the circle of radius `√q`, which is graph-RH for `K₄` — obtained by instantiating
  `theRootHasSquaredModulusQ` at the graph's parameters; and the **aperture is exhibited**:
  `theOvershootProducesARealRootBeyondTheCircle 3 2` shows the Perron eigenvalue — exactly the
  one the Ramanujan condition excludes — is exactly the one whose root escapes the circle.

**What this may not be reported as** (the investigating agent's own scope, adopted): not a
result about the Riemann Hypothesis; not a result about the Selberg trace formula; not evidence
for the Ihara–Bass theorem, whose truth makes the identity a corollary — it is evidence about
the **model**: the trivial term, the dart-reversal convention, the marked-start convention, and
the successor relation are exactly where modelling errors live, and this identity is the
instrument that catches them.  The Selberg import survey's own strongest self-refutation is
adopted with it: the hyperbolic-surface instance hands the operator to the analyst and is *not*
an instance of realization-pays; what transports exactly is only the quadratic dichotomy, which
is why this deed lives at the quadratic.

**Measured 2026-08-21** over `Mathlib` at `v4.27.0`: `grep -rli "ihara"` → 0 files;
`grep -rli "ramanujan"` → 2 files, both unrelated (Chudnovsky's `π` series; a partial-fractions
comment).  A name search over a stated scope, not a content-absence proof.

Every `theorem` is discharged and none depends on `sorryAx`.
-/

namespace Soma.Holonics.Millennium.GraphTrace

open Soma.Holonics.Millennium

/-- The twelve darts of the tetrahedron: ordered pairs of distinct vertices, derived from the
range rather than listed by hand. -/
def dartList : List (ℕ × ℕ) :=
  (List.range 4).flatMap fun u => (List.range 4).filterMap fun v =>
    if u ≠ v then some (u, v) else none

/-- The non-backtracking successor relation: `e` follows `d` when it departs where `d` lands
and does not reverse it.  This is the incidence condition; the successor lists are derived from
it by filtering, never authored. -/
def succs (d : ℕ × ℕ) : List (ℕ × ℕ) :=
  dartList.filter fun e => e.1 == d.2 && e.2 != d.1

/-- The endpoint population of length-`k` non-backtracking walks from `d`, with multiplicity. -/
def walks : ℕ → ℕ × ℕ → List (ℕ × ℕ)
  | 0, d => [d]
  | k + 1, d => (walks k d).flatMap succs

/-- The closed non-backtracking dart-walk population of length `k` — the trace of the `k`-th
power of the dart-transition matrix, computed by executing the walk relation. -/
def closedDartWalks (k : ℕ) : ℕ :=
  (dartList.map fun d => ((walks k d).filter fun e => e == d).length).sum

/-- The trivial term of the graph trace formula: `2(m − n) = 4` on `K₄`, present at even
lengths. -/
def trivialTerm (k : ℕ) : ℤ := if k % 2 = 0 then 4 else 0

/-- **The trace formula holds on the tetrahedron**: the enumerated closed-geodesic population
equals the Perron trace sequence plus three winding trace sequences plus the trivial term, at
every length up to six.  The left side executes the walk relation; the right side executes the
recurrence `TraceSequence.trace`; the kernel checks that they meet. -/
theorem theTraceFormulaHoldsOnTheTetrahedron :
    ∀ k : ℕ, k ≤ 6 →
      (closedDartWalks k : ℤ)
        = TraceSequence.trace 3 2 k + 3 * TraceSequence.trace (-1) 2 k + trivialTerm k := by
  intro k hk
  interval_cases k <;> rfl

/-- The adjacency of the tetrahedron. -/
def A : Matrix (Fin 4) (Fin 4) ℚ := !![0,1,1,1; 1,0,1,1; 1,1,0,1; 1,1,1,0]

/-- **The Perron realizer is exhibited**: the all-ones vector carries eigenvalue three. -/
theorem thePerronRealizerIsExhibited : A.mulVec ![1,1,1,1] = (3 : ℚ) • ![1,1,1,1] := by
  funext i
  fin_cases i <;> norm_num [A, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ]

/-- **The three winding realizers are exhibited**: three difference vectors, each carrying
eigenvalue `−1`. -/
theorem theWindingRealizersAreExhibited :
    A.mulVec ![1,-1,0,0] = (-1 : ℚ) • ![1,-1,0,0] ∧
    A.mulVec ![1,0,-1,0] = (-1 : ℚ) • ![1,0,-1,0] ∧
    A.mulVec ![1,0,0,-1] = (-1 : ℚ) • ![1,0,0,-1] := by
  refine ⟨?_, ?_, ?_⟩ <;>
    (funext i; fin_cases i <;> norm_num [A, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ])

/-- **The four realizers are independent** — no nontrivial combination of them vanishes, so the
multiplicity three of the winding eigenvalue is paid by exhibited realizers, never declared.
Stated as a statement about combinations rather than a determinant magnitude: the components
force every coefficient to zero. -/
theorem theRealizersAreIndependent (a b c d : ℚ)
    (h : a • ![1,1,1,1] + b • ![1,-1,0,0] + c • ![1,0,-1,0] + d • ![1,0,0,-1]
        = (0 : Fin 4 → ℚ)) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  have h3 := congrFun h 3
  simp at h0 h1 h2 h3
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- **Placement rides on the winding root**: the characteristic root at the graph's winding
parameters `(a, q) = (−1, 2)` has squared modulus exactly `q` — graph-RH for the tetrahedron,
by instantiating the standing level-one theorem. -/
theorem thePlacementRidesOnTheWindingRoot :
    Complex.normSq (TraceSequence.alpha (-1) 2) = 2 := by
  have h := TraceSequence.theRootHasSquaredModulusQ (-1) 2 (by norm_num)
  simpa using h

/-- **The aperture is exhibited**: at the Perron parameters `(3, 2)` the level-one bound fails
(`9 > 8`) and the characteristic polynomial acquires a real root whose square exceeds `q` — the
eigenvalue the Ramanujan condition excludes is exactly the eigenvalue that violates the bound. -/
theorem thePerronRootEscapesTheCircle :
    ∃ x : ℝ, x ^ 2 - 3 * x + 2 = 0 ∧ 2 < x ^ 2 := by
  have h := TraceSequence.theOvershootProducesARealRootBeyondTheCircle 3 2
    (by norm_num) (by norm_num)
  simpa using h

end Soma.Holonics.Millennium.GraphTrace
