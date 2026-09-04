# FT3: Hadamard holds, the Foster form is the log-derivative, and the comb flux is the velocity at a simple zero

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** FT3 under
[`THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md`](../../blueprint/THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md).  
**Owners:** `RH/FosterSplit.lean`, `RH/FosterHadamard.lean`, `RH/CombFlux.lean`, the amended port in
`RH/PhaseFlowLedger.lean`, and the population and fixed-constant additions to `RH/FosterTanks.lean`,
all under `soma/formal/elementary-holonics/ElementaryHolonics/` and registered in the root umbrella.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## (i) The split on a disc (`FosterSplit`)

[definition] `Zfac hR` is the symmetric factorization of FT0 at radius `R`, chosen once at the fixed
envelope constant `pointC`; `landau R` is its remainder bound; `T hR` is the finite population of
the closed half disc as a finset of the repeated index; `tail hR z := ∏'_{i ∉ T} (1 + a i z)`;
`tailInvSq R := Σ_{|u − ½| > R/2} |u − ½|^{−2}`; `cst hR := ∏_ρ (−1/(ρ − ½)²)^{m_ρ}`;
`F hR := 2 g′/g − tail′/tail` with `g` the factorization's unit.

[proved-derived; formal-checked]

- `mem_zeros_iff`, `Zfac_mult_eq`: the factorization's comb is exactly the zeros of `ξ` in the
  closed half disc with their global multiplicities; `prod_T`, `sum_T` reindex products and sums
  over the repeated population as multiplicity-weighted ones over the comb.
- `P_split`: `P = (∏_{i ∈ T} (1 + a i z)) · tail`, by Mathlib's `HasProd.mul_compl`.
- `finitePart_eq`: the finite part is `cst · Q²`, `Q` the factorization's polynomial, by reindexing
  the reflected product with `refl_mem`/`refl_mult`; `cst ≠ 0`.
- `tail_ne_zero`, `tail_differentiableOn`, `logDeriv_tail`: the tail is analytic and nonvanishing on
  the open half disc with the tail tank series as log-derivative; `norm_logDeriv_tail_le`:
  `‖tail′/tail(z)‖ ≤ 4 |z − ½| tailInvSq R` on the disc of radius `R/8`.
- **`tailInvSq_tendsto`: the tail of the inverse squares vanishes at infinity**, from FT1's
  summability by `summable_iff_vanishing_norm`.
- `F_differentiableOn`, `F_eq`: `F_R` is analytic on the open half disc and equals `2 ξ′/ξ − P′/P`
  off the zeros; `norm_F_le`: `‖F_R‖ ≤ bound R := 2 landau R + (R/2) tailInvSq R` on the open disc
  of radius `R/8`, extended to the zeros by continuity through the isolated-zero dichotomy and the
  identity theorem.
- `tsum_tank_split`, `sum_tank_T`: the tank series is the half-disc comb plus the tail.

## (ii) Hadamard (`FosterHadamard`)

[proved-derived; formal-checked]

- `landau_le`: for `R ≥ 1`, `landau R ≤ landauA + landauB · log R` with both constants exhibited
  from `pointC`, `L₀`, and `cq = log 2 / log (3/2)`: the budget is `O(R log R)` and Landau divides by
  `R`.
- `norm_deriv_G_le`: Cauchy's estimate for the global defect `G = 2 ξ′/ξ − P′/P` at scale `r`, with
  `R = 8(|w − ½| + r) + 8`; `tendsto_bound_div`: the estimate vanishes as `r → ∞`
  (`Real.tendsto_pow_log_div_mul_add_atTop` and `tailInvSq_tendsto`); `deriv_G_eq_zero`.
- `zeroSet_countable`, `isPreconnected_U`: the nonzero set of `ξ` is the complement of a countable
  set, connected by `Set.Countable.isPathConnected_compl_of_one_lt_rank`; `G_const`.
- `logDeriv_one_sub`, `G_one_sub`, `G_half`: the reflection makes `G` odd, so the constant is zero.
- **`G_eq_zero`: `2 ξ′/ξ = P′/P` off the zeros.**
- **`foster_form`: `ξ′/ξ(z) = Σ_u m_u (z − ½)/((z − ½)² − (u − ½)²)`** as a convergent series over
  the zeros of `ξ`, off the zeros.
- **`sq_eq_centre_mul_P`: `ξ(z)² = ξ(½)² · P(z)` for every `z`**, by the constancy of `ξ²/P` on the
  nonzero set (`P(½) = 1`) and the common vanishing on the zeros.

## (iii) The comb flux (`CombFlux`)

[proved-derived; formal-checked]

- `comb hR z := Σ_{ρ ∈ half disc} m_ρ/(z − ρ)`; `comb_eq_tankSum` (FT0's paired flux identity) and
  **`norm_logDeriv_sub_comb_le`: `‖ξ′/ξ(z) − comb_R(z)‖ ≤ 2 |z − ½| tailInvSq R`** on the disc of
  radius `R/8`: the comb of the half disc converges to `ξ′/ξ` locally uniformly off the zeros.
- `simple_zero_local`: at a simple zero, `mult z₀ = 1` and `ξ = (z − z₀) g` near `z₀` with `g`
  analytic and `g(z₀) = ξ′(z₀)`, by `AnalyticAt.analyticOrderAt_eq_natCast` and the derivative of
  the local form; `deriv_deriv_eq`: `ξ″(z₀) = 2 g′(z₀)`; `logDeriv_eq_local`:
  `ξ′/ξ = 1/(z − z₀) + g′/g` near `z₀`.
- `comb'_sub_le`: the comb without its `z₀` term is within `2(|z₀ − ½| + δ/2) tailInvSq R` of
  `g′/g(z₀)`, by the maximum principle (`Complex.norm_le_of_forall_mem_frontier_norm_le`) on a small
  disc about `z₀` whose circle avoids the zeros.
- `finsum_eq_comb'`: the port's divisor comb on `D(½, R)` is the comb of the half disc at radius
  `2R` without its `z₀` term.
- **`flux_riemannXi`: at every simple zero `z₀` of `ξ`,
  `2 Σ_{u ∈ D(½,R), u ≠ z₀} m_u/(z₀ − u) → ξ″(z₀)/ξ′(z₀)` as `R → ∞`.**
- **`flux_time_zero`: the RT3 port's field for `H t = heatE t ξ` at `t = 0`**, composing
  `ZeroDynamicsEntire.zero_curve_velocity_riemannXi` with `flux_riemannXi` through `heatE_zero`.

`#print axioms` on `P_split`, `finitePart_eq`, `F_eq`, `norm_F_le`, `tailInvSq_tendsto`, `landau_le`,
`deriv_G_eq_zero`, `isPreconnected_U`, `G_eq_zero`, `foster_form`, `sq_eq_centre_mul_P`,
`norm_logDeriv_sub_comb_le`, `simple_zero_local`, and `flux_riemannXi` returns `propext`,
`Classical.choice`, `Quot.sound`. The owners build alone and inside the root umbrella (9,794 jobs).

## The port, amended

[definition] `PhaseFlowLedger.RodgersTaoZeroDynamics` now centres its discs at `½`, the centre of
the reflection that pairs the comb, and takes a `C¹` curve (`z′` continuous), the hypothesis the
tree's velocity theorem carries. Discs centred at `0` are not symmetric under `z ↦ 1 − z`, and the
boundary population of `D(0, R) \ (1 − D(0, R))` is bounded only by `N(R + 1)/R = O(log R)`, which
does not vanish; the centre `½` removes the boundary. The port's field at `t = 0` is the theorem
`flux_time_zero`.

## The correction in place, and the obstruction named

[definition] The contract's FT3 text asked for the port discharged for `heatE t ξ` at every `t`,
"the same argument running on `heatE t ξ` once its Landau bound and count are returned". The
argument needs three inputs for `H_t = heatE t ξ`: an entire growth envelope (available from the
majorant of `HeatFlowEntire`), the count (Jensen from the envelope), and **the centre value
`H_t(½) ≠ 0` at every `t`**, which Jensen's count and the paired product both require. The centre
value at every time is a property of the kernel: `H_t(½) = ∫ e^{tu²} Φ(u) du` with a positive
integrand, and `Φ` is FT4's artifact. So the discharge for the family cannot run before FT4 returns
`Φ`, and the contract is corrected in place: FT3 passes on `ξ`'s Hadamard identity, the Foster
form, the comb flux at every simple zero of `ξ`, and the amended port with its time-zero field; the
discharge for `heatE t ξ` moves to FT4 (i) as the Foster class, FT0--FT3 generalized over symmetric
entire functions of finite order below two with a centre value, instantiated at `heatE t ξ` from
`Φ`'s centre value and the majorant's envelope. This is the actual point of dependence, not an
estimate of difficulty.

## Pass FT3

`ξ² = ξ(½)² · P`, the full Foster form, and the principal-value comb flux at every simple zero of
`ξ` are theorems; the port states the law at centre `½` and its time-zero field is a theorem.
**FT3 passes** at the corrected scope. Falsifier: a simple zero of `ξ` at which the finite comb flux
on a declared truncation disagrees with `ξ″/ξ′`, or a point at which `ξ² − ξ(½)² P` is nonzero.

## Boundaries

- No claim of movement on the Riemann Hypothesis. Nothing here places a zero; the Foster form and the
  flux hold wherever the zeros are.
- The port remains a port for `t ≠ 0`; its discharge is FT4 (i).
- `landauA`, `landauB` are exhibited from `pointC`, itself fixed by choice from an existence
  theorem; no numerical value is computed.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.FosterSplit ElementaryHolonics.RH.FosterHadamard ElementaryHolonics.RH.CombFlux
timeout 180s lake build ElementaryHolonics
```
