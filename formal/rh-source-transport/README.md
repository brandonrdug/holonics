# RH source transport — Lean boundary

This project is the formal companion to
`PAPERS/mathematics/theorems/divisor-source-transport-boundary.typ`.

It formalizes the finite, reusable implication:

1. old cells supply nonnegative demand;
2. new cells supply nonnegative capacity;
3. a declared incidence relation determines lawful transport;
4. proportional descendant transport has exact row sums;
5. its column load is exactly `capacity × congestion`; and
6. congestion at most one implies total demand at most total capacity.

It also begins the divisor-to-quotient re-indexing used by the analytic
continuation.  The companion
[`PROPORTIONAL_OBSTRUCTION.md`](PROPORTIONAL_OBSTRUCTION.md) uses that
re-indexing to show that square-free primorial receivers force the
proportional candidate above unit congestion.  The analytic estimates in
that note are explicit but are not yet checked by Lean.

This project does **not** encode the Riemann Hypothesis as a renamed integer
proposition, and it does not treat the historical
`src/labyrinth/mathematics/lean/App_RH.lean` as an authority.

The analytic objects remain explicit outside this first formal boundary:
Suzuki's incomplete-Beta kernel, the unique sign seam, the kernel asymptotic,
and the prime harmonic divergence used by the obstruction.  Because the
proportional candidate is now rejected, there is no longer a proposed
“uniform quotient-family congestion inequality” to assume.

Inside this laboratory checkout, use:

```sh
./check.sh
```

The checker reuses the already pinned Lean 4.27/Mathlib 4.27 environment when
it is present.  In a standalone checkout it falls back to `lake update`,
Mathlib's binary cache, and `lake build`.
