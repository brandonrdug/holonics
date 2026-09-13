# Public C5 torus transport

`run_public_session.py` supplies exact integer matrices to the public
`holonics hna mathematical-session` JSONL boundary and checks the returned native actions.
The `phase_clock_smith` example independently infers the monic annihilator coefficients through
the shared `ExactRatMatrix::minimal_polynomial` owner and its exact preimage reduction.
The public exact `power` request takes only
a retained operator and exponent; the native session infers the minimal polynomial itself and
uses the existing rank-factorized linear construction path.  The matching receipt is a separate
verification witness.
The default receipt is `.local/artifacts/2026-09-12-geometry/phase_clock_smith.json`; a missing
receipt returns explicit producer guidance and never falls back to canonical coefficients.

Run from the repository root:

```sh
cargo run -q -p holonic-engine --example phase_clock_smith
python3 research/experiments/pentagonal_torus_transport/run_public_session.py
```

The supplied matrices are

```text
L5 = 2 I - P - P⁻¹
K25 = L5 ⊗ I5 + I5 ⊗ L5
```

The script independently verifies the canonical polynomial identities and checks that the
inference receipt returns the same coefficients:

```text
L5³ - 5 L5² + 5 L5 = 0
K25⁶ - 20 K25⁵ + 150 K25⁴ - 525 K25³ + 850 K25² - 500 K25 = 0.
```

It forms `L5²` and `L5³` through the public resident `compose` request, then consumes `L5¹⁶`
through the native exact `power` request.  The 25-dimensional torus powers `K25²` through
`K25⁶` remain supplied as complete exact matrices for the independent annihilator check;
`K25¹²` is constructed through the same native `power` request.  All are rank-factorized,
resident-constructed, and applied through the public session.

The phase control supplies the real analyzer

```text
[[1,0,0,-1], [0,1,1,0], [1,0,0,1], [0,1,-1,0]]
```

to `(2,0,0,1)` and `(2,0,0,-1)`.  It returns `(1,0,3,0)` and `(3,0,1,0)`: the separate
input intensity face is `(4,1)` in both cases, while the later analyzer has normalized power
faces `(1/10,9/10)` and `(9/10,1/10)`.  This is a forward phase-separation witness; no
cross-entropy value is inserted into native execution.

The recorded process returned 25 mathematical events with no stream error.  The final
process census was 92 captured launches, 13 deed launches, 143,972 ingress bytes and
142,176 resident bytes.  Request-level native costs and all exact matrices/outputs are in
`public-mathematical-session.stdout.jsonl`, `public-mathematical-session.receipt.json`, and
`result.json`.  The portable `result.json` carries only the concise inferred recurrence summary;
the larger source inference ledger remains at the configured receipt path.
