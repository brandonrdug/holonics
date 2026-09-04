# FT4 (iii)–(v): the flow never creates a pair, the seam times are a closed up-set, and RH is the threshold given one seam time

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** FT4 (iii)–(v) under
[`THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md`](../../blueprint/THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md).  
**Owners:** `RH/KernelFlow.lean`, `RH/HurwitzLine.lean`, `RH/PolyaLine.lean`,
`RH/LineApproximation.lean`, `RH/EulerIterates.lean`, `RH/RealZeroTimes.lean`,
`RH/LinePreservation.lean`, all under `soma/formal/elementary-holonics/ElementaryHolonics/` and
registered in the root umbrella.  
**Scope:** FT4 (iii) forward preservation, (iv) the seam times as a closed up-set, and (v) `Λ_DN`
with `RH ⟺ Λ_DN ≤ 0` given one seam time are returned. The nonemptiness of the seam times, de
Bruijn's bound, is FT4's remaining item and is named below with its obstruction. Schedules nothing
beyond the directed order; the engine frontier is unchanged.

## The coordinate

[definition] Standard time is `τ = −t`: `H_τ := heatE (−τ) ξ = ∫ e^{τ u²} e^{(z − ½) u} Φ(u) du`
(`HeatKernelPhi`). Forward is `τ` increasing. The *seam times* are
`seamTimes := {τ | ∀ z, H_τ(z) = 0 → Re z = ½}`; **`Λ_DN := sInf seamTimes`**.

## (a) Admissible kernels and the semigroup (`KernelFlow`)

[proved-derived; formal-checked] `Kernel`: a continuous `K` with
`e^{a u² + b|u|} |K(u)| ≤ C e^{−u²}` for all `a, b ≥ 0`; its transform `T_K` is entire with the
moment transforms as derivative ladder (`hasDerivAt_TM`, `iteratedDeriv_T`), and
**`heatE_T : heatE t (T_K) = T_{e^{−t u²} K}`**. `Φ` is admissible (`ΦK`, `ΦK_T : T_Φ = ξ`),
`heatE t ξ = T_{e^{−t u²} Φ}`, and **`heatE_heatE_riemannXi : heatE s (heatE t ξ) = heatE (s + t) ξ`**,
the semigroup at the entire face.

## (b) Hurwitz on a rectangle (`HurwitzLine`)

[proved-derived; formal-checked] For entire `F n → G` locally uniformly along a countably
generated filter: the log-derivative winding integrals converge (`tendsto_rectIntegral`, by
dominated convergence on the four edges with `G` bounded away from zero on the boundary and the
derivatives uniformly bounded); each is `2πi` times the interior divisor sum
(`RectangleCountStable.exists_count`); so **`no_zero_of_eventually`**: if `F n` has eventually no
zero in the open rectangle, neither has `G`; and **`zeros_on_seam`**: if `G ≢ 0` and eventually
every zero of `F n` lies on the seam, every zero of `G` does, by an isolated-zero rectangle
avoiding the seam.

## (c) The seam polynomials (`PolyaLine`)

[proved-derived; formal-checked] `seamPoly q (z) := q(−i(z − ½))` for `q ∈ ℝ[X]`;
`iteratedDeriv_two_mul_seamPoly`; the Euler iterate
`eulerIter λ N f := Σ_{k ≤ N} C(N,k)(λ/N)^k f^{(2k)}` satisfies
**`eulerIter_seamPoly : eulerIter λ N (seamPoly q) = seamPoly ((heatStep (λ/N))^[N] q)`**;
`heatStep_iterate_ne_zero`; `nonreal_heatStep_iterate` (from
`ForwardPreservation.nonreal_heatStep_iterate_le`); hence **`eulerIter_seamPoly_re`**: the zeros of
the Euler iterates of a real-rooted seam polynomial lie on the seam.

## (d) Seam-zeroed members are limits of seam polynomials (`LineApproximation`)

[proved-derived; formal-checked] For a member `f` of the Foster class with `OnSeam f`: the mirror
`u ↦ 1 − u` is an involution of the repeated index (`mirror_mirror`), fixes every factor
(`a_mirror`), and exchanges the upper and lower halves (`mirror_mem_upper_iff`), so
**`P_eq_Qplus_sq : P f = (Qplus f)²`** with `Qplus` the product over the zeros of positive
imaginary part; by `IsPreconnected.eq_of_sq_eq` on the connected nonzero set and density,
**`eq_centre_mul_Qplus : f = f(½) · Qplus f`**; the finite subproducts `approx s` converge to `f`
locally uniformly (`tendsto_approx`) and are the seam polynomials `f(½) · seamPoly (qpoly s)` with
`qpoly s = ∏ (1 − X²/γ_i²)` real-rooted (`nonreal_qpoly`, `qpoly_ne_zero`).

## (e) The Euler iterates converge to the flow (`EulerIterates`)

[proved-derived; formal-checked] For `f` entire of growth `A exp(B‖w‖^ρ)`, `ρ < 2`, and `λ ≥ 0`:
**`tendsto_eulerIter : eulerIter λ N f → heatE (−λ) f` locally uniformly**, by Tannery's argument
with the majorant of `HeatFlowEntire`, `C(N,k)(λ/N)^k ≤ λ^k/k!`, and
`ForwardPreservation.tendsto_choose_mul_pow`.

## (f) The seam times (`RealZeroTimes`, `LinePreservation`)

[proved-derived; formal-checked]

- **`zero_mem_iff : 0 ∈ seamTimes ↔ RiemannHypothesis`** (`TrivialZeros.riemannHypothesis_iff_xi`).
- `tendstoLocallyUniformly_heatE`: the flow converges locally uniformly along every convergent
  sequence of times (joint continuity, `HeatFlowContinuity.continuous_heatE`); hence
  **`isClosed_seamTimes`** by Hurwitz.
- `onSeam_heatE_neg`: for a member `f` with seam zeros and `λ ≥ 0`, `heatE (−λ) f` has seam zeros
  unless it vanishes: the Euler iterates of the approximants have seam zeros (c, d), converge to
  the Euler iterates of `f` (derivatives of locally uniform limits,
  `tendstoLocallyUniformly_eulerIter`), which have seam zeros by Hurwitz, and converge to
  `heatE (−λ) f` (e), which has seam zeros by Hurwitz.
- **`seamTimes_upset : τ ∈ seamTimes → τ ≤ τ' → τ' ∈ seamTimes`**, the flow never creates a pair,
  through the semigroup and the class membership of every `heatE (−τ) ξ` with its centre value.
- **`riemannHypothesis_iff_Λ_DN_le : seamTimes.Nonempty → (RiemannHypothesis ↔ Λ_DN ≤ 0)`**, with
  `Λ_DN = sInf seamTimes` from the actual `Φ`: if the seam times are bounded below the infimum is a
  seam time (closed, nonempty, bounded below), and the up-set law places `0`; if not bounded below,
  the up-set is all of `ℝ`.

`#print axioms` on `seamTimes_upset`, `riemannHypothesis_iff_Λ_DN_le`, `onSeam_heatE_neg`,
`isClosed_seamTimes`, `zero_mem_iff`, `zeros_on_seam`, `tendsto_eulerIter`, `tendsto_approx`, and
`heatE_heatE_riemannXi` returns `propext`, `Classical.choice`, `Quot.sound`. The owners build alone
and inside the root umbrella (9,810 jobs).

## The remaining item, named

[open; source-inspected] FT4's pass asks for de Bruijn's `Λ_DN ≤ ½` "from `PairDescent`
transported to the entire face". `PairDescent.highest_pair_descent` needs a *highest* nonreal
pair; at the entire face the zeros are infinitely many and the supremum of their heights need not
be attained, so the polynomial argument does not transport as written. The seam times are
nonempty by de Bruijn's theorem (every `H_τ` with `τ ≥ ½` has only seam zeros), whose proof is
analytic in the kernel `e^{τ u²} Φ(u)` rather than by pair descent. Under this contract the
equivalence stands with the hypothesis `seamTimes.Nonempty` carried explicitly, and the
nonemptiness is the first exact missing item of the RH line. Falsifier for the returned law: a
seam time `τ` and `τ' > τ` at which `H_{τ'}` has a zero off the seam.

## Boundaries

- No claim of movement on the Riemann Hypothesis. `0 ∈ seamTimes ↔ RH` is a restatement; the
  up-set and closedness hold wherever the zeros are.
- Nothing here bounds `Λ_DN` above or below.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.LinePreservation
timeout 180s lake build ElementaryHolonics
```
