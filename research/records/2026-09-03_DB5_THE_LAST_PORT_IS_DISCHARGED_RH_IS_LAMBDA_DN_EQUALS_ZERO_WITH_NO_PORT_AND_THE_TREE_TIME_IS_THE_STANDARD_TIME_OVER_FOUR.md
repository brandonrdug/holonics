# DB5: the last port is discharged, RH is Λ_DN = 0 with no port, and the tree's time is the standard time over four

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** DB5 under
[`THE_SEAM_HAS_A_FIRST_TIME_BY_DE_BRUIJN_AND_THE_THRESHOLD_IS_RH_WITH_NO_PORT.md`](../../blueprint/THE_SEAM_HAS_A_FIRST_TIME_BY_DE_BRUIJN_AND_THE_THRESHOLD_IS_RH_WITH_NO_PORT.md).  
**Owners:** `RH/DeBruijnSeal.lean`, `RH/CriticalChart.lean`, and `RH/ThresholdReturn.lean` (docstring
amended) under `soma/formal/elementary-holonics/ElementaryHolonics/`, registered in the root
umbrella.  
**Scope:** the campaign closes with this record; the engine frontier is unchanged.

## The return

[definition] `criticalChart z = ½ + iz/2`; `Φ_std(v) = ½ Φ(2v)` (Rodgers–Tao's kernel);
`Hstd t z = ½ ∫ e^{tv²} Φ_std(v) e^{izv} dv` (their `H_t`); `seamTimesStd = {t | every zero of
Hstd t is real}`; `Λstd = sInf seamTimesStd`.

[proved-derived; formal-checked]

- `DeBruijnSeal.half_mem_seamTimes`: `½ ∈ seamTimes` by the up-set law from DB4's `1/8`;
  **`deBruijnBound : DeBruijnBound`** — the port of `ThresholdReturn` is a theorem.
- `bddBelow_seamTimes`, **`Λ_DN_le_eighth : Λ_DN ≤ 1/8`**, **`Λ_DN_mem_Icc_eighth : Λ_DN ∈ [0, 1/8]`**.
- **`riemannHypothesis_iff_Λ_DN_eq : RiemannHypothesis ↔ Λ_DN = 0`** and
  `riemannHypothesis_iff_Λ_DN_le : RiemannHypothesis ↔ Λ_DN ≤ 0`, with no hypothesis.
- `seamTimes_eq_Ici : seamTimes = Ici Λ_DN`: the seam times are exactly the closed ray from the
  threshold.
- `CriticalChart.Hstd_eq`: **`Hstd t z = ⅛ · heatE (−t/4) ξ (criticalChart z)`**, by the kernel
  representation and the substitution `u = 2v` (`Measure.integral_comp_mul_left`); this is the
  bridge of the 2026-09-02 record, now in Lean, and the RH0/RH1 retraction is closed.
- `criticalChart_on_seam_iff`, `criticalChart_surjective`, `mem_seamTimesStd_iff`:
  `t ∈ seamTimesStd ↔ t/4 ∈ seamTimes`; `seamTimesStd_eq`: the standard seam times are the image
  of the tree's under `τ ↦ 4τ`.
- **`Λstd_eq : Λstd = 4 Λ_DN`**, **`Λstd_mem_Icc : Λstd ∈ [0, ½]`** (de Bruijn's and
  Rodgers–Tao's bounds in the standard coordinate), and
  **`riemannHypothesis_iff_Λstd_eq : RiemannHypothesis ↔ Λstd = 0`**.

`#print axioms` on `deBruijnBound`, `riemannHypothesis_iff_Λ_DN_eq`, `Λ_DN_mem_Icc_eighth`,
`Hstd_eq`, `Λstd_eq`, and `riemannHypothesis_iff_Λstd_eq` returns `propext`, `Classical.choice`,
`Quot.sound`. `CriticalChart` builds alone (8,835 jobs) and the root umbrella at 9,843 jobs in 4 s
incremental, each under the 180 s limit.

## The position of the RH line after this record

[definition] Every theorem of the RH line is now unconditional: `RiemannHypothesis ↔ Λ_DN = 0`
with `Λ_DN ∈ [0, 1/8]` in the tree's coordinate, equivalently `Λstd ∈ [0, ½]` in the standard
one. The first exact missing inequality is `Λ_DN ≤ 0`, which is RH; its falsifier is a zero of
`ξ` off the seam. No route to it is known, and no later RH deed is scheduled by this record.

## Pass DB5

`#print axioms` deposited on the three axioms, root umbrella green under 180 s per owner, the
port discharged, the bridge in Lean. **DB5 passes. The campaign is complete.** Falsifier: a
standard time `t < ½` with `t/4 ∉ seamTimes` would contradict `Λstd_mem_Icc` only through
`Λ_DN_le_eighth`, whose falsifier is a zero of `heatE (−1/8) ξ` off the seam.

## Boundaries

- No claim on the Riemann Hypothesis.
- Ki–Kim–Lee's strict `Λ < ½` and Polymath's `0.22` are not claimed; the tree's bound is de
  Bruijn's.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.DeBruijnSeal
timeout 180s lake build ElementaryHolonics.RH.CriticalChart
timeout 180s lake build ElementaryHolonics
```
