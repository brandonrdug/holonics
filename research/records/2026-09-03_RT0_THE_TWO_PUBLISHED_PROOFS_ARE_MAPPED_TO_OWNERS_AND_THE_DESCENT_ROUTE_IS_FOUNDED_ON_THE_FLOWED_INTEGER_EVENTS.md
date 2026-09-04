# RT0: the two published proofs are mapped to owners, and the descent route is founded on the flowed integer events

**Date:** 2026-09-03  
**Truth status:** `established-bounded`  
**Evidence:** `source-inspected` (the two papers read in full structure; the tree and Mathlib
grepped for owners)  
**Campaign:** RT0 under
[`THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md`](../../blueprint/THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md).  
**Owner:** none in Lean; this deed returns a manifest and a route.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## The occasion

Brandon asked whether Rodgers--Tao's `0 ≤ Λ_DN` is available online and directed a critical
scoping and a formal deposit of the RT plans. Available: the paper
(arXiv 1801.05914; Forum of Mathematics, Pi 8 (2020)) and Dobner's shorter proof
(arXiv 2005.05142). Not available: any formal artifact. Mathlib's tree at the pinned commit
(2026-08-10, Lean 4.33) contains no de Bruijn--Newman material; `Mathlib/NumberTheory/FLT/`
holds `n = 3`, `n = 4`, and the statement `FermatLastTheorem`; `Mathlib/FieldTheory/AbelRuffini.lean`
holds `IsSolvableByRad` and the insolvability theorem. Neither is consumed by the RH line.

## The manifest

[established-bounded; source-inspected] **Rodgers--Tao, by result, against the tree:**

| Published result | Content | Tree / Mathlib | Status |
|---|---|---|---|
| Notation, §1.2 | `Λ < 0 ⇒ RH`, so RH-conditional theorems are available | `RealZeroTimes`, `LinePreservation.riemannHypothesis_iff_Λ_DN_le` | theorem (given a seam time) |
| Lemma 4 | saddle-point asymptotics of `H_t(x − iκ log x)`, `H_t′/H_t` | none; needs complex Stirling with remainder | missing |
| Theorem 9, Cor. 10 | `N_t([0,T]) = Ψ(T) + O(log² T)`; `x_j(t) = ξ_j + O(log ξ_j)` | `RH/Jensen.lean`, `RectangleArgumentPrinciple`, Foster-class count `K₁ + K₂ R^{3/2}` | partial; needs Lemma 4 |
| Theorem 11 (CSV 1994) | `∂_t x_k = 2 Σ′ 1/(x_k − x_j)`, `C¹`, simple zeros for `t > Λ` | `FosterClassHeatFlow.rodgersTaoZeroDynamics_heatE`, `SimpleZeroCurve.exists_zero_curve_riemannXi` | theorem at the local scope; global ordering and simplicity missing |
| Lemma 12, 14, Prop. 13 | gap dynamics, cross-energy inequality, `log(1/gap) ≪ log² j log log j` | none | missing |
| Prop. 15, 17, 22, Lemmas 16--21, 24, Cor. 25 | cutoff Hamiltonian, renormalized energy, `∂_t H̃_T = −4Ẽ_T + negl.`, `∫ Ẽ_T = o(T log³ T)` | none | missing |
| Prop. 26--28 | energy at time zero by Bourgain's pigeonholing | none | missing |
| §9 | `Ẽ(0)` small ⇒ almost all gaps `(4π + o(1))/log T`; contradicts CGGGH-B 1985 | `ExplicitFormulaLimit`, `WeilPositivity` are the explicit formula only; Montgomery's method and CGGGH-B absent everywhere | missing; a second programme |

[established-bounded; source-inspected] **Dobner, by result, against the tree:**

| Published result | Content | Tree / Mathlib | Status |
|---|---|---|---|
| Eq. (9) | `ξ_t` as the Gaussian convolution of `ξ` on a vertical line, `t < 0` standard | `HeatKernelPhi.heatE_riemannXi`, `KernelFlow`, `HeatFlowStackedSeam` (kernel length `√(4πt)`) | theorem in the kernel form; the line form is a Fourier identity |
| termwise structure | each Dirichlet term convolves to a Gaussian-weighted term | `FlowedExplicitFormula.hasSum_flowedTerm` (repository `t ≥ 0`, `Re z > 1`) | **theorem** (FT5) |
| Lemma 1 | Stirling with remainder | Mathlib: real `n!` only; tree: `GammaBound`, `GammaGrowth`, `GammaDecay` magnitudes | missing → RT2 |
| Lemma 2 | inverse-Mellin decay | `ThetaMellin`, `MellinHorizon` | partial |
| Lemma 4, 5 | per-term steepest descent; Taylor of `γ` | none | missing → RT3 |
| Theorem 4 | `ξ_t(J_t s) = γ_t(s)(F_t(s) + O(y^{−1/5} e^{(10/|t|) min(x,−2)²}))`, `|x| ≤ C y^{1/4}` | none | missing → RT4 |
| Lemma 3, Theorem 5 | `F_t` has a zero; Bohr almost periodicity | Mathlib: `Real.exists_int_int_abs_mul_sub_le` (one-dimensional) | missing → RT5 |
| Rouché transfer; `Re J_t → ∞` | zeros of `ξ_t` right of the seam at every `t < 0` | `HurwitzLine`, `RectangleArgumentPrinciple`, `Complex.norm_le_of_forall_mem_frontier_norm_le` | partial → RT6 |

## The route

[definition] Repository `t > 0` is standard `τ < 0`, the descent side, and it is exactly where
FT5's flowed integer events converge; FT5's divergence for repository `t < 0` is the forward
side. The flowed integer events are Dobner's per-term Gaussian convolutions. The RT programme is
therefore founded on the descent route with the phases RT1--RT6 of the contract; the fleet
document's Rodgers--Tao labels are preserved as `RTa1`--`RTa6` and not scheduled. The one owner
both routes need is Stirling with a remainder (RT2).

[counterexample; source-inspected] The fleet's `RT6` ("time-zero energy control and the
pair-correlation contradiction") is not one phase: its input CGGGH-B 1985 rests on Montgomery's
pair-correlation method, which rests on the Montgomery--Vaughan mean-value theorem; none is
formalized anywhere. Scheduling it as a phase would have made the campaign's last deed a hidden
second campaign.

## Pass RT0

The manifest is deposited and the route founded. **RT0 passes.** Falsifier: a result of either
paper omitted from the manifest, or an owner listed as present that does not carry the stated
content.

## Boundaries

- No claim of movement on `0 ≤ Λ_DN`; the port `RodgersTaoNonneg` stands until RT6.
- No claim on de Bruijn's bound or the conjecture.
- FLT and the quintic are not dependencies of any RH deed; they enter holonics, if at all, as
  world content under the jurisdiction rule, never as interior law.

## Reproduction

```bash
cd soma/formal/elementary-holonics
grep -n "theorem hasSum_flowedTerm" ElementaryHolonics/RH/FlowedExplicitFormula.lean
grep -rln "Bruijn" .lake/packages/mathlib/Mathlib | grep -vi index   # empty
```
