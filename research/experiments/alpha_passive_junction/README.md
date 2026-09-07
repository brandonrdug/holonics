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

[established-bounded] Evidence tags: `computational-witness`. The observer realifies each adjacent real/imaginary
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

[established-bounded] Evidence tags: `computational-witness`. The default run reads only the first 25 actual native
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

## Fixed-point enclosure observer

[established-bounded] Evidence tags: `computational-witness`, `measured`. `enclosure.py` is a separate CPU
observer for the same passive junction. It keeps the full 96-real-coordinate carrier in every run:
32 complex source coordinates and 16 complex arriving coordinates. It forms `C` exactly from raw
source/arrival rows, including `d dᵀ + Jd(Jd)ᵀ`, keeps `h` approximate only in its fixed-point
center, and uses native interleaved source ordering. It does not call `field.advance`, replay
formation, update a model, or invoke Lean.

For scale `Q = 2^g`, the center stores `H/Q`, `P/Q`, and candidate `V/Q`. It quantizes known exact
ingress `u` toward zero (floor for nonnegative and ceil for negative coordinates), retaining exact `u` and its L1 quanta
error `E_u`. The candidate solves `A = I+C` through integer fixed-point `LDL^T`, with positive
pivots and toward-zero division after each shifted product. The oriented residual is retained as
`r_hat = A(V/Q) - 2(Uhat/Q + H/Q)` and `R = ceil(Q ||r_hat||_1)`. The checked radii are

```text
E_v     = 2 E_h + 2 E_u + R
E_out   = 2 E_h + E_u + R
E_hnext = E_h + 2 E_u + R
E_Pnext = E_P + E_v.
```

They follow from

```text
e_v     = 2 A^-1(e_h + delta_u) - A^-1 r,
e_hnext = (I-2A^-1)e_h + (2I-2A^-1)delta_u + A^-1 r,
e_Pnext = e_P + (-1)^t e_v,
```

and `||A^-1|| <= 1`, `||I-2A^-1|| <= 1`, `||2I-2A^-1|| <= 2` for exact positive
semidefinite `C`. The full oriented residual is used in the radius and is never a quality score.

The private anchor run uses precision bits `12, 24, 48, 72` with the same full carrier. Its first
25 occurrences are exact anchors at every precision; all six checks (`v`, outgoing, `h`, prefix,
internal-current reconstruction, and the error-trace decoder) pass 25/25. The 72-bit run then
continues the certified center/radius recurrence through occurrence 727; it does not maintain an
exact evolving rational state after the anchor window. At occurrence 727 there are 724 admitted
contacts. The maximum 72-bit LDL intermediate width is 154 bits, with no emulated signed-256
overflow. Its maximum radii in quanta are `E_v=66,464,443`, `E_hnext=33,274,133`, and
`E_Pnext=16,112,079,081`. These enclosure results do not establish productive Athena-alpha
quality.

```sh
python3 research/experiments/alpha_passive_junction/enclosure.py \
  .local/artifacts/athena-alpha/ac1/material-history-readbacks.json \
  --occurrences 728 --precisions 12 24 48 72 \
  --output .local/artifacts/athena-alpha/ac1/passive-junction-enclosure-reference-v4.json
```

The earlier enclosure v1/v2 reports are superseded by v3/v4: they confused precision bits with
carrier dimension. v3 corrected the full 96-dimensional carrier and decoder; v4 corrected the
all-step LDL width summary.

The 25-anchor four-precision receipt is retained as
`passive-junction-enclosure-anchors-v1.json`; the 728-occurrence precision-72 receipt is
`passive-junction-enclosure-reference-v4.json`.

## Native certificate checker

[established-bounded] `verify_native.py` checks the serial enclosed report
`material-enclosed-junction-g72.json` directly. Its `evidence_tags` are
`computational-witness` and `measured`. It decodes each adjacent packed signed-i128 word, checks
all 728 exact source centers, residuals, center recurrences, radius recurrences, source links and
part boundaries, reconstructs the covariance prefix operator from every raw `d` and `Jd` row, and
compares the final covariance section. It does not rerun LDL, call native code, or claim exact
point equality after the first 25 anchors.

The first 25 exact anchors pass all four current balls; all 300 birth-current balls pass. The
earlier enclosure-reference run separately checks its exact error trace. This material checker
requires identity source frames; it does not transport recharted inputs. The final private
certificate is `native-enclosed-junction-certificate-final-v1.json`, mode `0600`.

```sh
python3 research/experiments/alpha_passive_junction/verify_native.py \
  .local/artifacts/athena-alpha/ac1/material-enclosed-junction-g72.json \
  --output .local/artifacts/athena-alpha/ac1/native-enclosed-junction-certificate-v1.json
```

[established-bounded] Evidence tags: `measured`. The [paired-junction native return](../../records/2026-09-06_AC1_THE_PAIRED_JUNCTION_RETAINS_ITS_INNER_CURRENT.md)
separately establishes its finite same-input contextual control and compares six actual native
material operations with this reference. The word carrier then refuses, preserving the complete
preceding body. The final artifact `material-paired-junction-word-v2.json` corrects the refusal
classification to carrier exhaustion alone and has the identical body/readback history compared
by v7. `paired-junction-final-comparison.json` retains that comparison.

[established-bounded; measured] The [native enclosure return](../../records/2026-09-06_AC1_THE_RESIDUAL_CARRIES_THE_CONTINUING_JUNCTION_WITHOUT_A_POINT_SEAL.md)
continues the same junction through all 728 material occurrences and 724 contacts. Cooperative
factorization, buffered diagnostic publication and exact unit-division shortcuts preserve its
complete body and history; the final report is `material-enclosed-junction-g72-final.json`.

[open] Efficient broader operation, lawful history placement, wider situated channels and
learned text-codec conduct remain required. No alpha-quality or Athena-alpha claim follows from
this observer.

## Contextual source and actual text-return inspections

[definition] `contextual_source.py` proposes a different contact source: the retained junction
outgoing source projection. It is a cold experiment, not a native implementation or a new
representation of the existing raw-source law. The full carrier remains 96 real coordinates.

[established-bounded; computational-witness] Its scalar operator-error bound accepts only
seven/eleven occurrences at 24/72 fractional bits
before its proposed report carrier refuses; four exact anchors pass. The
[source/text return](../../records/2026-09-06_AC1_THE_SHARED_SOURCE_MEETS_AN_EXPLICIT_TEXT_CURRENT_RECEIVER.md)
states why this bound does not settle the exact law's stability.

[established-bounded; computational-witness] `inspect_text_return.py` checks the actual new
18-port text study separately: source bytes and end markers, three shared parent contacts,
all 64 differential current readings and actual self-returns, and the final moment against its
full 856-contact population. All 63 consecutive outgoing-current balls are disjoint despite the
64 repeated `d` bytes. Cold current capture leaves the complete observed body and output unchanged.
The checker is a targeted comparison of the retained first-return reports, not a language gate.

```sh
python3 research/experiments/alpha_passive_junction/inspect_text_return.py \
  .local/artifacts/athena-alpha/ac2/first-text-return-v2.json \
  .local/artifacts/athena-alpha/ac2/first-text-return-v1.json \
  --output .local/artifacts/athena-alpha/ac2/new-text-comparison.json
```
