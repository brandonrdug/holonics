# RT2: Stirling holds on the sector with the remainder exhibited, and no logarithm of Gamma is taken

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** RT2 under
[`THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md`](../../archive/plans/THE_DESCENT_SIDE_HAS_OFF_SEAM_ZEROS_AT_EVERY_NEGATIVE_TIME_AND_THE_THRESHOLD_IS_NONNEGATIVE.md).  
**Owner:** `RH/GammaStirling.lean` under `soma/formal/elementary-holonics/ElementaryHolonics/`,
registered in the root umbrella.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## The return

[definition] `Sector := {w ≠ 0 : 0 ≤ Re w ∨ |Re w| ≤ |Im w|}` (the right half-plane together with
the double cone `|arg w| ≤ 3π/4`); `g₂(u) = (u² − u)/2`; `P₂(x) = g₂({x})`; the remainder
`μ(w) = ∫_0^∞ P₂(x)/(w + x)² dx` and its truncation `μ_n(w) = ∫_0^n`; `ρ(w) = e^{−μ(w)} − 1`.

[proved-derived; formal-checked]

- `sector_shift`: for `w` in the sector and `x ≥ 0`, `w + x` is off the slit and
  `‖w + x‖² ≥ (x² + ‖w‖²)/4`.
- `norm_μ_le`: **`‖μ(w)‖ ≤ π/(4‖w‖)`** on the sector, from `|P₂| ≤ 1/8` and
  `∫_0^∞ dx/(x² + c²) = π/(2c)`; `tendsto_μN`: `μ_n(w) → μ(w)`.
- `trapezoid`: on each unit interval,
  `½(Log(w+k) + Log(w+k+1)) − ∫_k^{k+1} Log(w+x) dx = ∫_k^{k+1} g₂(x−k)/(w+x)² dx`, by the
  fundamental theorem for `A(x) = (x−k−½) Log(w+x) − g₂(x−k)/(w+x)`.
- `euler_maclaurin`: `Σ_{j≤n} Log(w+j) = ∫_0^n Log(w+x) dx + ½Log w + ½Log(w+n) + μ_n(w)`, by
  induction on `n`; `integral_log_add`: `∫_0^n Log(w+x) dx = (w+n)Log(w+n) − (w+n) − (wLog w − w)`.
- `gammaSeq_eq_exp`: Euler's sequence is `exp(E_n(w))`,
  `E_n(w) = w log n + log n! − Σ_{j≤n} Log(w+j)`, with every factor exponentiated through
  `exp ∘ Log`, so no branch of `log Γ` is ever chosen.
- `δ_eq`, `tendsto_δ`: the real Stirling defect is `log(stirlingSeq n) − ½ log π → 0`
  (Mathlib's `Stirling.tendsto_stirlingSeq_sqrt_pi`); `tendsto_log_one_add_div`:
  `(w + n + ½) Log(1 + w/n) → w`; `E_eq`, `tendsto_E`.
- **`gamma_eq`, `gamma_eq_sqrt`: `Γ(w) = √(2π) · exp((w − ½) Log w − w − μ(w))` on the sector**,
  by uniqueness of the limit of `GammaSeq` (`Complex.GammaSeq_tendsto_Gamma`).
- **`gamma_eq_mul`, `norm_ρ_le`: `Γ(w) = √(2π) exp((w − ½) Log w − w)(1 + ρ(w))` with
  `‖ρ(w)‖ ≤ π/(2‖w‖)` for `‖w‖ ≥ 1`.**

`#print axioms` on `gamma_eq`, `gamma_eq_sqrt`, `gamma_eq_mul`, `norm_μ_le`, `norm_ρ_le`, and
`euler_maclaurin` returns `propext`, `Classical.choice`, `Quot.sound`. The owner builds alone and
inside the root umbrella (9,814 jobs).

## The scope, stated

[definition] The contract's RT2 text asked for the remainder on `Re s ≥ 1`; the return holds on
the larger sector, which is what RT3 needs: the contour shift of Dobner's Lemma 4 passes through
points `z` with `Re z` as negative as `−C y^{1/4}` at height `y`, all inside `|arg z| ≤ 3π/4`. The
consequences for `Γ_ℝ(s) = π^{−s/2}Γ(s/2)` and for the ratio `Γ(w)/Γ(w₀)` (Dobner's (43)) are
algebra over `gamma_eq_sqrt` and are RT3's to state where they are used.

## Pass RT2

The remainder bound formal-checked with the constant exhibited. **RT2 passes.** Falsifier: a
point of the sector at which `‖μ(w)‖ > π/(4‖w‖)`, or at which `Γ(w)` differs from
`√(2π) exp((w−½)Log w − w − μ(w))`.

## Boundaries

- No claim of movement on `0 ≤ Λ_DN`; the port `RodgersTaoNonneg` stands until RT6.
- Mathlib's own `Stirling` is the real `n!` result; this owner is the complex sector form and
  imports nothing beyond Mathlib.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.GammaStirling
timeout 180s lake build ElementaryHolonics
```
