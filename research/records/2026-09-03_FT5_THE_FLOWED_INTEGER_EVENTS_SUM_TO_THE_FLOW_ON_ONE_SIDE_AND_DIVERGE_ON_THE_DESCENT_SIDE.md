# FT5: the flowed integer events sum to the flow on one side, and diverge on the descent side

**Date:** 2026-09-03  
**Truth status:** `proved-derived`  
**Evidence:** `formal-checked`, `source-inspected`  
**Campaign:** FT5 under
[`THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md`](../../blueprint/THE_FLOW_CARRIES_THE_ZEROS_AS_FOSTER_TANKS_AND_THE_THRESHOLD_IS_THE_TARGET.md).  
**Owner:** `RH/FlowedExplicitFormula.lean` under `soma/formal/elementary-holonics/ElementaryHolonics/`,
registered in the root umbrella.  
**Scope:** the flowed explicit formula at the kernel: the integer side as the flowed events of the
kernel `Φ`, the zero side as the Foster form of `heatE t ξ`, their identity on the convergent
side, and the exact divergence on the other side. Schedules nothing beyond the directed order.

## The integer events

[definition] `φ(v) := e^{v/2} (2π² e^{4v} − 3π e^{2v}) e^{−π e^{2v}}` is the one Gamma-type profile.
**`event_eq`**: the `n`-th term of the kernel is the profile translated to the integer event,
`e^{u/2} Ψterm_n(e^{2u}) = |n|^{−1/2} φ(u + log |n|)`, so `Φ(u) = Σ_{n ∈ ℤ} |n|^{−1/2} φ(u + log |n|)`,
the half-density comb of `HeatFlowBinding`. **`flow_weight_split`**: in the event's own coordinate
`v = u + log n`, `e^{−t(v − log n)²} = e^{−t v²} · n^{2tv} · flowWeight (−t) n`, the free Gaussian,
the running power, and the flow weight whose binding defect on composites `HeatFlowBinding`
exhibits.

## The identity on the convergent side

[proved-derived; formal-checked] **`hasSum_flowedTerm`**: for repository time `t ≥ 0` (standard
`τ = −t ≤ 0`) and `Re z > 1`, the flowed events sum to the flow,
`Σ_{n ∈ ℤ} ∫ e^{−t u²} e^{(z − ½)u} · |n|^{−1/2} φ(u + log |n|) du = heatE t ξ (z)`, by
`HeatKernelPhi.heatE_riemannXi` and the exchange of sum and integral under the Gamma majorant of
FT4 (ii) (`e^{−t u²} ≤ 1`). **`foster_form_heatE`**: at every time and off its zeros,
`(heatE t ξ)′/(heatE t ξ)(z) = Σ_u m_u(t) (z − ½)/((z − ½)² − (u − ½)²)` over the zeros of
`heatE t ξ`, from the Foster class instance of FT4. At `t = 0` the integer side is `ξ`'s own
series of events, `Φ` unflowed, and the two sides are those of FT3.

## The exact divergence on the descent side

[proved-derived; formal-checked] **`not_integrable_flowedTerm`**: for `t < 0` (standard
`τ = −t > 0`, the side on which pairs descend) and every `n ≠ 0`, the `n`-th flowed event
`e^{−t u²} e^{(z − ½)u} |n|^{−1/2} φ(u + log |n|)` is **not integrable**: as `u → −∞` the profile
decays only like `e^{2u}` while the Gaussian `e^{|t| u²}` grows, so the norm integral over
`(−∞, −M]` is infinite (`abs_Ψterm_ge`, `Real.volume_Iic`). The kernel integral itself converges at
every time (`Φ` decays double-exponentially at both ends by the theta functional equation), so on
the descent side **the integer events do not separate**: the flowed explicit formula exists only
as the kernel integral, not termwise.

`#print axioms` on `hasSum_flowedTerm`, `not_integrable_flowedTerm`, `event_eq`, and
`foster_form_heatE` returns `propext`, `Classical.choice`, `Quot.sound`. The owner builds alone
and inside the root umbrella (9,812 jobs).

## The correction in place

[definition] The contract's FT5 asked for the flowed explicit formula "for every `t`" with the
integer side carrying the weights `n^{−1/2} e^{t(log n)²} n^{−2tv}`. The weights are exactly
`event_eq` and `flow_weight_split`. The formula holds termwise on the repository-forward side
`t ≥ 0` and is formally impossible termwise on the descent side `t < 0`: the contract's FT6 route,
"along `[0, τ]` FT5 gives the flowed explicit formula with the binding defect active", runs on the
side where the events diverge. The contract is corrected in place: FT5 passes at the kernel
scope with the divergence deposited, and FT6's inequality must be sought on the kernel side or
returned as the first exact missing inequality.

## Pass FT5

The flowed explicit formula is a theorem for the flowed events on `t ≥ 0`, `Re z > 1`, with the
`t = 0` specialization the kernel form of the standing explicit formula, and the divergence at
`t < 0` is a theorem. **FT5 passes** at the corrected scope. Falsifier: a `t ≥ 0`, `Re z > 1` at
which the partial sums of the flowed events on a declared truncation depart from `heatE t ξ (z)`
by more than the Gamma tail.

## Boundaries

- No claim of movement on the Riemann Hypothesis.
- The rectangle-and-contour form of `ExplicitFormulaLimit` is not transported to the flow; the
  kernel form is the flowed formula this record returns.

## Reproduction

```bash
cd soma/formal/elementary-holonics
timeout 180s lake build ElementaryHolonics.RH.FlowedExplicitFormula
timeout 180s lake build ElementaryHolonics
```
