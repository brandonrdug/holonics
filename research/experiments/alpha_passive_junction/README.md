# Exact passive junction observer

[definition] `inspect.py` is a bounded CPU observer for the proposed coupled passive junction.
It reads the private AC1 material-history report and does not run native code, update a model,
select a response, or invoke a proof assistant.

## Reference construction

[definition] For one actual linked field occurrence, let `q` be the complete root source field
(outgoing and held branches) at the source handle and let `a` be the complete arriving field. The
contact row is

```text
d = (q, -a) ∈ C^(3N),   b_birth = 0.
```

The contact is added before the current reaction. With unit reference admittance,

```text
C = Σ d d*,       h = Σ d b,
u = (q_now, 0),   v = 2 (I + C)^(-1) (u + h),
outgoing = v − u,
b_next = d* v − b,
h_next = C v − h.
```

The source `q` is the actual native field at the source occurrence named by the recorded handle;
it is never replaced by a predicted target field. The arriving `a` is the actual next field from
the report. Raw message text and source coordinates remain outside this reference calculation.

[established-bounded; computational-witness] The observer realifies each adjacent real/imaginary
coordinate pair with `J(x,y)=(-y,x)` and checks

```text
C_real = Σ (d dᵀ + Jd (Jd)ᵀ).
```

It independently checks `C_real v` against `Σ d(d* v)`, the condensed-current identity
`h_next = C v − h`, the alternating prefix decoder for every born contact, and the weighted passive balance

```text
||u||² + Σ|b|² = ||v − u||² + Σ|d* v − b|².
```

The synthetic witness uses opposite rows whose sum cancels while their paired moment is nonzero.
This refutes replacement by the sum of currents. Their linear span is also nonzero and is a
different object; the moment additionally retains the two-contact multiplicity. This witness
does not establish language conduct.

## Actual bounded observation

[established-bounded; computational-witness] The default run reads only the first 25 actual native
field lineages from the private `material-history-readbacks.json`. It adds contacts from the actual
`received_from` source occurrence before each reaction, carries each exact internal current, and
records reduced numerator/denominator widths and exact fraction-free arithmetic widths. The
Woodbury reference clears its rational contact system exactly; the native path separately
normalizes its covariance and RHS as described below. No fractional coefficient is converted with
truncating integer conversion.

The reference solve uses the contact-rank Woodbury system. For the first 12 occurrences it also
reproduces the native staging: normalize the covariance as `C_num/C_den`, form `A_num = C_num + C_den I`,
scale only the RHS by `rhs_den`, then run fraction-free Bareiss with integer adjugate
backsubstitution. It records multiplication and subtraction widths before each division and the
adjugate-equivalent `det(A) * v` numerator width. Those measurements are arithmetic observations
of this finite reference. The device's bound-by-operand-width checks can conservatively refuse
before a mathematically reduced product exhausts the carrier.

```sh
python3 research/experiments/alpha_passive_junction/inspect.py \
  .local/artifacts/athena-alpha/ac1/material-history-readbacks.json \
  --occurrences 25 \
  --output .local/artifacts/athena-alpha/ac1/passive-junction-reference-v7.json \
  --native-report .local/artifacts/athena-alpha/ac1/material-paired-junction-word.json
```

An optional `--native-report` argument compares each available exact `[v, outgoing, h, P]`
readback section from a paired-junction run. The comparison is a private arithmetic receipt and
does not feed the observer or native operation.

The output path must be new and is created with mode `0600`. The stdout summary contains counts and
bit widths only; it contains no message text. The private report contains exact reference values
and source-occurrence indices, so it remains capable of reconstructing private material through
the source report and must remain private. It reports the first reduced-value and RHS
common-denominator failures against a 63-bit signed-word magnitude budget separately from the
native-staged full-matrix predivision 127-bit observation.

The earlier v2-v6 aperture measurements are superseded by v7: multiplying
the coefficient matrix by the RHS denominator does not reproduce the native arithmetic path.

[established-bounded; measured] The [paired-junction native return](../../records/2026-09-06_AC1_THE_PAIRED_JUNCTION_RETAINS_ITS_INNER_CURRENT.md)
separately establishes its finite same-input contextual control and compares six actual native
material operations with this reference. The word carrier then refuses, preserving the complete
preceding body. The final artifact `material-paired-junction-word-v2.json` corrects the refusal
classification to carrier exhaustion alone and has the identical body/readback history compared
by v7. `paired-junction-final-comparison.json` retains that comparison.

[open] Continuing current representation, record-level situated channels and learned text-codec
conduct remain required. No alpha-quality or Athena-alpha claim follows from this observer.
