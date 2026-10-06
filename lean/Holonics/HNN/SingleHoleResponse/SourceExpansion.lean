import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Module.LinearMap.Basic
import Mathlib.Tactic.Abel

noncomputable section

namespace Holonics.HNN.SingleHoleResponse

open scoped BigOperators

section Source

variable {K Station Label X W : Type*} [Field K]
  [Fintype Station] [DecidableEq Station]
  [Fintype Label] [DecidableEq Label]
  [AddCommGroup X] [Module K X]
  [AddCommGroup W] [Module K W]

/-- The completed station chart: every intact station keeps its declared class, and the one hole
is filled by the same admitted label `c`. -/
def completedCell (hole : Station) (known : Station → Label) (basis : Label → X)
    (c : Label) (s : Station) : X :=
  if s = hole then basis c else basis (known s)

/-- A first-port term after the source's carried phase/lift transport. `weight` includes the
normalization at the full first population, which is independent of `c`. -/
def firstCompleteTerm (hole : Station) (known : Station → Label) (basis : Label → X)
    (c : Label) (weight : K) (P : Station → X →ₗ[K] W) (s : Station) : W :=
  weight • P s (completedCell hole known basis c s)

/-- Known first-port contribution. The missing station contributes zero here. -/
def firstFixedTerm (hole : Station) (known : Station → Label) (basis : Label → X)
    (weight : K) (P : Station → X →ₗ[K] W) (s : Station) : W :=
  if s = hole then 0 else weight • P s (basis (known s))

/-- First-port response column. It is zero off the missing station. -/
def firstResponseTerm (hole : Station) (basis : Label → X) (c : Label)
    (weight : K) (P : Station → X →ₗ[K] W) (s : Station) : W :=
  if s = hole then weight • P s (basis c) else 0

/-- One complete first-source population, using its full class-independent normalization. -/
def firstComplete (hole : Station) (known : Station → Label) (basis : Label → X)
    (c : Label) (weight : K) (P : Station → X →ₗ[K] W) : W :=
  ∑ s, firstCompleteTerm hole known basis c weight P s

/-- The fixed first-source population. -/
def firstFixed (hole : Station) (known : Station → Label) (basis : Label → X)
    (weight : K) (P : Station → X →ₗ[K] W) : W :=
  ∑ s, firstFixedTerm hole known basis weight P s

/-- The first-source response at the shared label. -/
def firstResponse (hole : Station) (basis : Label → X) (c : Label)
    (weight : K) (P : Station → X →ₗ[K] W) : W :=
  ∑ s, firstResponseTerm hole basis c weight P s

/-- The pair-port term for one ordered offset edge. `F e` is that edge's existing bilinear pair
relation (which may differ at every ring/offset); `Q e` carries its output through the edge's
phase/lift placement. The edge is ordered as current endpoint, earlier endpoint. -/
def pairCompleteTerm (hole : Station) (known : Station → Label) (basis : Label → X)
    (c : Label) (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) (e : Station × Station) : W :=
  weight e • Q e (F e (completedCell hole known basis c e.1)
    (completedCell hole known basis c e.2))

/-- Pair-port terms with both endpoints intact. -/
def pairFixedTerm (hole : Station) (known : Station → Label) (basis : Label → X)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) (e : Station × Station) : W :=
  if e.1 = hole ∨ e.2 = hole then 0 else
    weight e • Q e (F e (basis (known e.1)) (basis (known e.2)))

/-- The correlated pair response: the same label supplies the unique missing endpoint, while the
other endpoint retains its known class. -/
def pairResponseTerm (hole : Station) (known : Station → Label) (basis : Label → X)
    (c : Label) (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) (e : Station × Station) : W :=
  if e.1 = hole then
    weight e • Q e (F e (basis c) (basis (known e.2)) )
  else if e.2 = hole then
    weight e • Q e (F e (basis (known e.1)) (basis c))
  else 0

/-- All normalized pair-port terms for a completed source. -/
def pairComplete (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X) (c : Label)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) : W :=
  ∑ e ∈ edges, pairCompleteTerm hole known basis c F Q weight e

/-- The normalized pair-port contribution whose endpoints are both intact. -/
def pairFixed (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) : W :=
  ∑ e ∈ edges, pairFixedTerm hole known basis F Q weight e

/-- The sum of the pair-port columns at the same missing label used by the first population. -/
def pairResponse (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X) (c : Label)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K) : W :=
  ∑ e ∈ edges, pairResponseTerm hole known basis c F Q weight e

/-- The complete source vector, with the class-independent first and offset normalizations
already included in `weight` and `weight e`. -/
def completeSource (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X) (c : Label) (firstWeight : K)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W) (pairWeight : Station × Station → K) : W :=
  firstComplete hole known basis c firstWeight P +
    pairComplete edges hole known basis c F Q pairWeight

/-- The fixed source vector, including the intact first and offset populations. -/
def fixedSource (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X) (firstWeight : K)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W) (pairWeight : Station × Station → K) : W :=
  firstFixed hole known basis firstWeight P +
    pairFixed edges hole known basis F Q pairWeight

/-- The full signed response column of one shared source label across first and pair ports. -/
def responseSource (edges : Finset (Station × Station)) (hole : Station)
    (known : Station → Label) (basis : Label → X) (c : Label) (firstWeight : K)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W) (pairWeight : Station × Station → K) : W :=
  firstResponse hole basis c firstWeight P +
    pairResponse edges hole known basis c F Q pairWeight

/-- The full first population is exactly its intact population plus the one missing class term.
This is a termwise source identity, not a hypothesis that the desired completed-source equality
already holds. -/
theorem firstComplete_eq_fixed_add_response (hole : Station) (known : Station → Label)
    (basis : Label → X) (c : Label) (weight : K) (P : Station → X →ₗ[K] W) :
    firstComplete hole known basis c weight P =
      firstFixed hole known basis weight P + firstResponse hole basis c weight P := by
  change (∑ s, firstCompleteTerm hole known basis c weight P s) =
    (∑ s, firstFixedTerm hole known basis weight P s) +
      ∑ s, firstResponseTerm hole basis c weight P s
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s hs
  by_cases h : s = hole <;>
    simp [firstCompleteTerm, firstFixedTerm, firstResponseTerm, completedCell, h]

/-- A pair edge with distinct endpoints has exactly one of three cases: both known, hole at its
current endpoint, or hole at its earlier endpoint. The two one-hole cases use the same label `c`.
The existing bilinear pair port is consumed before any receiver projection. -/
theorem pairComplete_eq_fixed_add_response (edges : Finset (Station × Station))
    (hole : Station) (known : Station → Label) (basis : Label → X) (c : Label)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (weight : Station × Station → K)
    (hedges : ∀ e ∈ edges, e.1 ≠ e.2) :
    pairComplete edges hole known basis c F Q weight =
      pairFixed edges hole known basis F Q weight +
        pairResponse edges hole known basis c F Q weight := by
  change (∑ e ∈ edges, pairCompleteTerm hole known basis c F Q weight e) =
    (∑ e ∈ edges, pairFixedTerm hole known basis F Q weight e) +
      ∑ e ∈ edges, pairResponseTerm hole known basis c F Q weight e
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e he
  have hd := hedges e he
  by_cases hs : e.1 = hole
  · have ht : e.2 ≠ hole := by
      intro ht
      exact hd (hs.trans ht.symm)
    simp [pairCompleteTerm, pairFixedTerm, pairResponseTerm, completedCell, hs, ht]
  · by_cases ht : e.2 = hole
    · simp [pairCompleteTerm, pairFixedTerm, pairResponseTerm, completedCell, hs, ht]
    · simp [pairCompleteTerm, pairFixedTerm, pairResponseTerm, completedCell, hs, ht]

/-- **Constructive one-hole source expansion** consumed by the physical consumer. The known
first/offset populations and the shared signed response are separated by expansion of the actual
first terms and bilinear pair-port terms. -/
theorem oneHoleSourceExpansion (edges : Finset (Station × Station))
    (hole : Station) (known : Station → Label) (basis : Label → X) (c : Label)
    (firstWeight : K) (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (pairWeight : Station × Station → K)
    (hedges : ∀ e ∈ edges, e.1 ≠ e.2) :
    completeSource edges hole known basis c firstWeight P F Q pairWeight =
      fixedSource edges hole known basis firstWeight P F Q pairWeight +
        responseSource edges hole known basis c firstWeight P F Q pairWeight := by
  unfold completeSource fixedSource responseSource
  rw [firstComplete_eq_fixed_add_response hole known basis c firstWeight P,
    pairComplete_eq_fixed_add_response edges hole known basis c F Q pairWeight hedges]
  abel

/-- Population-normalized single-hole form. The first population keeps `ν(N)` for every completion,
and an ordered edge at offset `δ` keeps `ν(max(N−δ,0))`; natural subtraction is saturating, exactly
as in the accepted source law. Neither normalization is recomputed from the observed sparse counts. -/
theorem populationNormalizedOneHoleSourceExpansion
    (edges : Finset (Station × Station)) (hole : Station) (known : Station → Label)
    (basis : Label → X) (c : Label) (N : ℕ)
    (offset : Station × Station → ℕ) (ν : ℕ → K)
    (hN : N = Fintype.card Station)
    (P : Station → X →ₗ[K] W)
    (F : Station × Station → X →ₗ[K] X →ₗ[K] W)
    (Q : Station × Station → W →ₗ[K] W)
    (hedges : ∀ e ∈ edges, e.1 ≠ e.2) :
    completeSource edges hole known basis c (ν (Fintype.card Station)) P F Q
        (fun e => ν (Fintype.card Station - offset e)) =
      fixedSource edges hole known basis (ν (Fintype.card Station)) P F Q
          (fun e => ν (Fintype.card Station - offset e)) +
        responseSource edges hole known basis c (ν (Fintype.card Station)) P F Q
          (fun e => ν (Fintype.card Station - offset e)) := by
  simpa [hN] using
    (oneHoleSourceExpansion edges hole known basis c (ν N) P F Q
      (fun e => ν (N - offset e)) hedges)

end Source

end Holonics.HNN.SingleHoleResponse

#print axioms Holonics.HNN.SingleHoleResponse.firstComplete_eq_fixed_add_response
#print axioms Holonics.HNN.SingleHoleResponse.pairComplete_eq_fixed_add_response
#print axioms Holonics.HNN.SingleHoleResponse.oneHoleSourceExpansion
#print axioms Holonics.HNN.SingleHoleResponse.populationNormalizedOneHoleSourceExpansion
