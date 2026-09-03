# FT2: the paired canonical product is entire, and its log-derivative is the Foster series

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** FT2 under
[`THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md`](../../blueprint/THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md).  
**Owner:** `RH/FosterProduct.lean` under `soma/formal/elementary-holonics/ElementaryHolonics/`,
registered in the root umbrella.  
**Scope:** schedules nothing beyond the directed order; the engine frontier is unchanged.

## The return

[definition] `Idx := Σ u : Zero, Fin m_u`, the zeros of `ξ` repeated by multiplicity;
`ctr i := u_i − ½`; the paired term `a i z := −((z − ½)/ctr i)²`; the product
`P z := ∏'_{i : Idx} (1 + a i z)`; the tank `tank i z := 2(z − ½)/((z − ½)² − ctr i²)`.

[proved-derived; formal-checked]

- `one_add_a_eq`, `one_add_a_eq_zero_iff`: the factor is
  `(ctr − (z − ½))(ctr + (z − ½))/ctr²` and vanishes exactly at `z = u_i` or `z = 1 − u_i`.
- `summable_idx_of_summable`: a nonnegative function of the zero, summed over the repeated index,
  is its multiplicity-weighted sum over the zeros; `summable_norm_a` and `summable_majorant_disc`
  transport FT1's `Σ m_u |u − ½|^{−2} < ∞` to the norms of the terms, pointwise and uniformly on
  every centred disc.
- `hasProdLocallyUniformlyOn`, `multipliableLocallyUniformlyOn`: the product converges locally
  uniformly on every centred disc, by Mathlib's `Summable.hasProdLocallyUniformlyOn_one_add`.
- **`differentiable_P`: `P` is entire**, as a locally uniform limit of finite products.
- **`P_symm`: `P(1 − z) = P(z)`.**
- **`P_eq_zero`, `P_ne_zero`: `P` vanishes at every zero of `ξ` and nowhere else**, the first by
  the eventually-zero finite products, the second by `tprod_one_add_ne_zero_of_summable` with
  `mult_one_sub` carrying the reflection.
- `finite_zero_ball`, `finite_idx_ball`: finitely many indices lie in any disc.
- `logDeriv_factor`: the log-derivative of one factor is its tank; `norm_tank_le` and
  `summable_tank`: the tanks are summable at every point, bounded eventually by
  `4|z − ½| / |u − ½|²`.
- **`logDeriv_P`: off the zeros, `P′/P(z) = Σ_i tank i z`**, by Mathlib's
  `logDeriv_tprod_eq_tsum`; **`tsum_tank_eq`** collapses it to
  `Σ_u m_u · 2(z − ½)/((z − ½)² − (u − ½)²)`, the sum over all zeros of the tank of each pair
  counted from both members, the same population FT0's finite form carries.

`#print axioms` on `differentiable_P`, `P_symm`, `P_eq_zero`, `P_ne_zero`, `logDeriv_P`, and
`tsum_tank_eq` returns `propext`, `Classical.choice`, `Quot.sound`. The owner builds alone and
inside the root umbrella.

## The scope, corrected in place

[definition] Each pair contributes twice to `P`, once from each member, so `P` is the paired
product squared and its order at a zero is `2 m_u`. FT3 compares `P` with `ξ²`, whose order at a
zero is also `2 m_u`, so the doubled form is the natural one and nothing is lost. The contract's
FT2 text asked for an order-one envelope of `P`; the route FT3 takes needs no envelope of `P`,
only Landau's bound on `ξ` and the tail of the Foster series, so the envelope is withdrawn from the
contract in place. The order `2 m_u` at every zero is established in FT3 through the finite/tail
split of the product on a disc, where it is used, and the contract's FT2 and FT3 texts are
corrected to say so.

## Pass FT2

`P` entire, `P` reflection symmetric, the zero set of `P` equal to the zero set of `ξ`, and the
log-derivative series proved. **FT2 passes** at the corrected scope. Falsifier: a disc on which the
zero set of `P` and the zero set of `ξ` differ.

## Boundaries

- No claim of movement on the Riemann Hypothesis. `P` is built from the zeros wherever they are.
- The identity `P = ξ²/ξ(½)²` is FT3's, not this record's.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.FosterProduct
timeout 180s lake build ElementaryHolonics
```
