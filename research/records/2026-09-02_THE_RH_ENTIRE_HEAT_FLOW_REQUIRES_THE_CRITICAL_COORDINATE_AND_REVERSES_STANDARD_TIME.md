# The RH entire heat flow requires the critical coordinate and reverses standard time

**Date:** 2026-09-02
**Scope:** interpretation correction for the current `ElementaryHolonics/RH/` entire heat-flow
line; no Lean theorem is retracted.
**Truth status:** per claim under [`../../canon/EPISTEMIC_GRADES.md`](../../docs/canon/EPISTEMIC_GRADES.md).

## 1. Correction

[proved-derived; source-inspected] The repository defines

```text
heatE(u, f, s) = sum_k (-u)^k / k! * f^(2k)(s)
               = exp(-u D_s^2) f(s)
```

and proves `partial_u heatE = -partial_s^2 heatE`. For `f = xi`, this is a correct entire
`s`-plane flow.

[proved-standard; source-inspected] The standard de Bruijn--Newman coordinate used by
Rodgers--Tao is

```text
H_0(z) = (1/8) xi(1/2 + i z/2)
partial_t H_t = -partial_z^2 H_t.
```

Let `criticalChart(z) = 1/2 + i z/2`. Since its derivative is `i/2`,

```text
partial_z^2 (f o criticalChart) = -(1/4) (partial_s^2 f) o criticalChart.
```

Therefore the exact time/coordinate bridge is

```text
H_t(z) = (1/8) heatE(-t/4, xi, criticalChart(z)),
```

or equivalently

```text
(1/8) heatE(u, xi, criticalChart(z)) = H_(-4u)(z).
```

[counterexample; source-inspected] Positive repository `heatE` time is negative standard
de Bruijn--Newman time. Consequently the direct identification of `heatE(t, xi, s)` with standard
`H_t`, and any interpretation in which its own increasing positive time necessarily carries the
standard forward collision of off-line pairs, is retracted.

## 2. Finite control

[proved-derived] For

```text
f(s) = (s - 1/2)^2 - a^2,
```

the derivative series terminates and returns

```text
heatE(u, f, s) = (s - 1/2)^2 - a^2 - 2u.
```

[counterexample] For positive `u`, the two roots have larger displacement from `1/2`. This is the
opposite orientation from a claim that positive `u` is standard forward de Bruijn--Newman time.
It does not refute the polynomial or entire heat-flow theorems at their actual definitions.

## 3. What stands

[proved-derived; formal-checked] The following remain valid at their stated scope:

- absolute convergence and entire dependence of `heatE`;
- `partial_u heatE = -partial_s^2 heatE`;
- reflection and conjugation symmetry in the `s`-plane;
- joint continuity;
- rectangle zero-count stability;
- persistence of a unique simple zero;
- the continuous local selected-zero curve; and
- its existing conditional differentiable-curve velocity law.

[definition] These results may be transported to the standard `H_t` only after the critical chart,
time reversal/rescaling, and every derivative factor are formalized.

## 4. Required next RH passage

[definition] The exterior Gemini fleet instruction
[`../GEMINI_3_8_FLASH_SWARM_INSTRUCTIONS.md`](../GEMINI_3_8_FLASH_SWARM_INSTRUCTIONS.md) makes RH0
and RH1 mandatory before further threshold interpretation:

1. derive the coordinate/sign receipt and finite control;
2. define `criticalChart` and its inverse;
3. define the coordinate-corrected `dnH`;
4. prove the exact `heatE` bridge and zero correspondence; and
5. only then transport symmetry, zero motion, real-zero times, and `Λ_DN`.

[definition] `c_CD`, the Copson--de Bruijn inequality coefficient, remains mathematically separate
from the coordinate-corrected de Bruijn--Newman threshold `Λ_DN`.

## 5. Source

[proved-standard; source-inspected] The normalization and heat equation are given in
Rodgers and Tao, *The de Bruijn--Newman constant is non-negative*, equations (1) and (4):
<https://arxiv.org/html/1801.05914v5#S1>.
