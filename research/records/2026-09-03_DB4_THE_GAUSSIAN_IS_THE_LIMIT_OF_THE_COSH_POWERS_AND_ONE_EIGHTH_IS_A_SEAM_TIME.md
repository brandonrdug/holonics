# DB4: the Gaussian is the limit of the cosh powers, and one eighth is a seam time

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** DB4 under
[`THE_SEAM_HAS_A_FIRST_TIME_BY_DE_BRUIJN_AND_THE_THRESHOLD_IS_RH_WITH_NO_PORT.md`](../../blueprint/THE_SEAM_HAS_A_FIRST_TIME_BY_DE_BRUIJN_AND_THE_THRESHOLD_IS_RH_WITH_NO_PORT.md).  
**Owner:** `RH/DeBruijnLimit.lean` under `soma/formal/elementary-holonics/ElementaryHolonics/`,
registered in the root umbrella.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## The return

[definition] `KN N = coshPow ΦK (1/(2N)) N²`, the kernel `cosh(u/(2N))^{N²} Φ(u)` of the `N²`-fold
average; `ΦK.flow (−1/8)` the kernel `e^{u²/8} Φ(u)` of `heatE (−1/8) ξ`.

[proved-derived; formal-checked]

- `one_add_sq_div_two_le_cosh`: `1 + y²/2 ≤ cosh y`, from `cosh y = 1 + 2 sinh²(y/2)` and
  `|y/2| ≤ |sinh(y/2)|`.
- **`tendsto_coshPow`: `cosh(u/(2N))^{N²} → e^{u²/8}`**, squeezed between
  `(1 + (u²/8)/N²)^{N²}` (Mathlib's `Real.tendsto_one_add_div_pow_exp` along `N ↦ N²`) and the
  constant `e^{u²/8}` from `Real.cosh_le_exp_half_sq`; this is de Bruijn's (3.9).
- **`tendstoLocallyUniformly_T`**: transforms of kernels converging pointwise under a common
  admissible domination converge locally uniformly, by dominated convergence of
  `∫ e^{b|u|} |K_N − L|` on each disc (`b = ‖x‖ + 2`).
- `tendsto_xiIter`: `xiIter (1/(2N)) N² → heatE (−1/8) ξ` locally uniformly, the domination
  being `cosh(u/(2N))^{N²} ≤ e^{u²/8}`.
- **`eighth_mem_seamTimes : (1/8 : ℝ) ∈ seamTimes`**, by `HurwitzLine.zeros_on_seam` applied to
  the iterates (seam zeros for `N ≥ 1` by DB3) and their limit, which is nonzero at `½`.

`#print axioms` on `eighth_mem_seamTimes` and `tendstoLocallyUniformly_T` returns `propext`,
`Classical.choice`, `Quot.sound`. The owner builds alone (8,804 jobs) and inside the root
umbrella (9,841 jobs).

## Pass DB4

`eighth_mem_seamTimes` formal-checked. **DB4 passes.** Falsifier: a zero of `heatE (−1/8) ξ`
off the seam.

## Boundaries

- The seal, the port, and the bridge are DB5's.
- In the standard coordinate this is de Bruijn's `t = ½`; the tree's `1/8` is exact in its own
  coordinate and becomes `½` only through the bridge deposited in DB5.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.DeBruijnLimit
timeout 180s lake build ElementaryHolonics
```
