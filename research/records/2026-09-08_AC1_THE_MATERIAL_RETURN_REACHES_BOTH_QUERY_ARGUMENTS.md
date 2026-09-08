# AC1: the material return reaches both query arguments

[definition] This continues the [normalized receiver](2026-09-08_AC1_THE_NORMALIZED_RECEIVER_RETURNS_ITS_COMPLETE_CURRENT_AND_TWO_METRIC_FACES.md)
and [active-interior/boundary-flux synthesis](2026-09-08_BOUNDARY_FLUX_COUPLES_ACTIVE_INTERIORS_AND_TOLERANCE_IS_RECEIVER_RELATIVE.md).
It concerns AC1 step 2. The native operator is the existing operative-contextual material chart;
no alphabet, task score, sampled point selection or new learner is introduced.

## The actual derivative and its scope

[definition] Write `u(x)=(1,x)`, `Q(x)=u(x)u(x)* / ||u(x)||²`, and
`Psi(s,c)=Q(s) tensor Q(c)`. The producing prediction is `M Psi(s,c)`. Here `s` contains both
visible branches and `c` contains all outgoing branches and all internal currents in actual
contact birth order. Older factors have exact zero coordinates for contacts not yet born.

[proved-derived] For a fixed retained operator and a real-potential covector `r`, each signed
operator factor `beta_i Psi(s_i,c_i)*` contributes, with `a_i=Re<beta_i,r>`,

```
n = 1 + ||c||²; n_i = 1 + ||c_i||²; h_i = 1 + <c_i,c>
Kc_i = |h_i|² / (n_i n)
gc = (2/n) sum_i a_i Ks_i [c_i h_i/n_i - Kc_i c]
```

The visible-source derivative is the same expression with `s` and `c` exchanged. This follows
by the real quotient rule on `|1+<x_i,x>|² / [(1+||x_i||²)(1+||x||²)]`. Relative phase enters
the complex pairing and multiplication before the real covector pairing. It is not a derivative
of magnitudes alone.

[definition] The factor population includes each ordinary factor plus its contextual factor,
and the negative contextual factor at its actual reference source. Both contributions use the
immutable historical producing carriers. The receiver's source occurrence selects the original
emitted prediction and the operator **after that source occurrence**, even if reception is delayed.
This is distinct from the material learner's contemporary effective-source prediction immediately
before receiving; the API does not silently exchange those scopes.

[definition] `RelativeEntropy` uses `r=q-p`; `SquaredProbability` uses `r=J_p(q-p)`. They are
different metric covectors already returned by the normalized receiver. Neither is silently
declared a complete finite learning displacement. Historical operator factors are held fixed
in this partial derivative; their own causal adjoints and the paired-contact adjoint remain
additional parts of the complete chronological return.

## Numerical return, ownership and tolerance

[proved-derived] With the Euclidean real chart and Hilbert–Schmidt projector norm,
`||DQ|| <= 2` and `||D²Q|| <= 20`. The latter follows by twice differentiating `N/n`:
the five norm contributions are bounded by `(2+4+4+2+8)/n`, with `n>=1`.
The derivative of the other tensor factor contributes at most `4` times its source displacement.
If `E` bounds the difference between the ideal retained operator and its numerical factor sum,
`N` bounds that numerical operator, and `es,ec` bound the two query-coordinate errors, then
the additional context-covector norm error is at most

```
[2 E + N (4 es + 20 ec)] ||r||.
```

Exchange `es,ec` for the visible-source return. The implementation uses an upper bound on
`||r||` from the full covector interval box. Each coefficient multiplication, rational division
and final sum also has outward dyadic rounding. Thus the returned intervals include both
arithmetic remainder and the declared material/source error; they do not select a centre as an
actual cause. These are numerical/source enclosures, not calibrated physical detector thresholds.

[definition] `pull_back_material_source` requires the normalized return's actual field owner,
not just matching occurrence numbers. The result retains immutable producing reports and internal
carriers. It holds no second continuing ecology and commits no morphology or current. Cold
inspection is explicit. The public interface currently requires `OperativeContextual`, whose
complete internal coordinates are available directly; unsupported source charts return that
precise obstruction.

[definition] The GPU first computes five interval coefficients per signed historical factor,
then reduces them across the visible and complete current coordinates. No dense tensor-product
feature matrix is expanded. The work still grows with historical factor population times query
current dimension; this is not a claim of population-independent transport or completed compression.

## Verification position

[established-bounded; measured] The focused native test passed: `cargo test -p holonic-engine
--lib material_source_pullback -- --include-ignored --test-threads=1`. Its actual retained factors
agree with an independent exact-rational quotient-rule derivative at every corner of both
two-coordinate metric-covector boxes. It covers complex phases, reflected factors, delayed
reception, foreign-field rejection and zero numerical section readouts during construction.
Both visible and internal coordinate families include certified nonzero returns. The first run
after compilation took 109.45 seconds, including device-module startup. This is not a warm
operation timing. After retaining the observation and normalized report with the returned
carrier, the complete changed receiver suite was checked again: `cargo test -p holonic-engine
--lib receiver::normalized -- --include-ignored --test-threads=1`, **4 passed in 8.15 seconds**.
This includes the original common-gauge, open-ball and source-qualified normalization controls.

[established-bounded; measured] The changed `alpha_contextual_lift` example builds successfully
and observes the saved 1,930-occurrence, eight-family conversation model. The
[portable receipt](2026-09-08_material_source_pullback/return.json) retains its command, exact
rational enclosures summarized by family, source/receiving cuts, metrics and costs. The whole
process took 10.409 seconds. Both metrics returned without numerical section readout during
construction and without changing the field cut:

| Receiving / producing occurrence | Relative-entropy pullback | Squared-probability pullback | Certified nonzero real coordinates, visible / outgoing / internal |
|---|---:|---:|---|
| 1 / 0 | 0.410 ms | 0.171 ms | 0 / 0 / 0; the initial material operator is exactly zero |
| 20 / 19 | 0.679 ms | 0.672 ms | 32 / 48 / 19, for both metrics |
| 1600 / 1599 | 26.401 ms | 26.116 ms | 36 / 54 / 1599, for both metrics |

The last return contains 72 visible, 108 outgoing and 3,198 internal real coordinates. Its
largest internal coordinate interval width is below `1.52e-10` in the declared chart for both
metrics. This decimal is an exterior summary of the receipt's exact rational width. These are
single-operation measurements at the recorded populations, not an asymptotic or power claim.
The full numerical report remains local; the portable receipt includes no conversation text.

[open] This component does not establish a finite successor, endogenous contact-morphology
development, full chronological adjoint, useful language, or completion of AC1–AC5. Its purpose
is to make the previously absent material-to-source/current port executable so the producing
interior and successor can be composed next.
