# The homogeneous phase moment joins the native material return

[definition] This implements the source variant posed in the
[homogeneous-moment construction](2026-09-07_AC2_A_HOMOGENEOUS_PHASE_MOMENT_IS_THE_NEXT_MATERIAL_SOURCE_CHART.md).
The complete contextual current remains the operand. The mathematical source is
`Q(x)=(1,x)(1,x)* / (1+||x||²)` in the declared unit-reference chart. The unchanged material
return law now has denominator two because `||Q(x)||_F=1`. A numerical source is an
approximation accompanied by its error; it is not selected as the actual physical source.
This source chart establishes neither a unique original cause in the Preimage Fibre nor
a universal preparation operation on unknown quantum states.

[established-bounded; source-inspected] `NativeMaterialTransportSource::HomogeneousMoment`
joins the existing `NativeConstitutiveField` owner. `field_moment_material.cuh` evaluates
retained source-qualified factors on the GPU. `field/material_transport/moment.rs` mounts
their immutable addresses and decodes cold reports. The existing field operation stages the
complete return before publishing its successor. No fixture-local learner, host semantic
calculation, inherited model or Lean process supplies native development.

[definition] The retained numerical operator is the exact generative expression

```text
Mhat = sum_i beta_hat_i Q(xhat_source_i)*.
k_Q(x,y) = |1+<x,y>|² / ((1+||x||²)(1+||y||²)).
```

Here `Q*` in the operator expression denotes the source's Hilbert-space covector. The old
complete-current source owner supplies the outgoing current, every born internal current's
prefix expression, norm and pairing. No full Hermitian matrix is enumerated. Retained factors
are already formed coefficients; evaluating them does not replay their learning. The initial
representation costs work proportional to the retained factor population for each source
evaluation and requires those factors and source expressions to be resident during the return.
It is not a claim of a bounded-size or constant-work model.

[definition] Each native evaluation uses `floor(S k_Q)/S`, where `S=2^grain`, and retains
whether its exact division remainder is nonzero. For each output component, the signs of
the retained beta coefficients give an oriented lower/upper bound on the omitted kernel
remainder. The signed grid accumulation and both bounds remain in the report. The original
source/factor expression is sufficient for the exterior exact rational decoder
`inspect_exact_numerical_moment_forward(operator_at,source_at)`; it never conducts a native
operation. Grid-kernel evaluation is not reported as the exact numerical operator value.

[proved-derived] A complete-source pairing or norm occupies an unsigned magnitude of at
most 256 bits. Adding the homogeneous reference may need 257 bits; multiplying two such
values needs at most 514 bits. Adding the two squared components or doubling the division
remainder needs at most 515 bits.
The new arithmetic uses seventeen 32-bit limbs (544 bits), with checked overflow, while
retaining the existing signed-128 current and signed-256 source charts. Repeated remainder
doubling computes the grid quotient without forming an additional shifted dividend.

[proved-derived] Put `f=Q(x)`, `g=Q(xhat)` and `e=||f-g||_F`. Both sources have norm one.
The ideal return is `F(M,f,y)=M(I-ff*/2)+yf*/2`. Its difference from the corresponding
numerical-source return is bounded by

```text
E_M + (N_M + ||yhat||) e + E_y/2,
```

because `||I-ff*/2||=1`, `||ff*-gg*|| <= 2e` and
`||yf*-yhat g*|| <= E_y + ||yhat|| e`. Replacing the exact numerical source evaluation
by its enclosed native value adds at most half its evaluation error; rounding beta adds
its retained half-grid residue bound. Thus the implemented coefficient-error update is

```text
E_M' <= E_M + (N_M + ||yhat||) e + (E_y + E_eval)/2 + E_beta.
N_M' <= min(N_M + ||beta_hat||, sqrt(N_M² + 2 Re <c_hat,beta_hat>
                                    + ||beta_hat||² + 2 E_eval ||beta_hat||)).
E_forward <= E_M' + N_M' e_query + E_query_eval.
```

The second norm bound follows by expanding `||Mhat+beta_hat g*||_F²`, using `||g||=1`,
and bounding `Re <Mhat g-c_hat,beta_hat>` by `E_eval ||beta_hat||`. Its signed cross-current
is retained before the square root; the triangle bound remains a valid alternative. This
avoids counting cancelling returns as monotonically accumulated operator magnitude. Existing
saved upper bounds remain valid inputs to the tighter recurrence; no wire reinterpretation
or change to the numerical coefficients is needed.

Each native bound rounds outward. `e <= min(2 E_x,2)` follows from the source-chart proof
and the unit norms. Componentwise kernel bounds precede their conservative Euclidean
bound. The beta report retains the signed half-grid residual, not just its magnitude.

[established-bounded; source-inspected] Historical returns retain their producing operator
cut. A delayed return evaluates that source with all later committed factors before forming
its new beta. Previously stored reports remain immutable. Rest/archive validation carries
the new source kind, its birth expression, coefficient bounds and factor reports. The native
text differential receiver reads the same forward-current ball without host numerical
readback. Select the variant on a fresh public `alpha_text` run with
`--material-source homogeneous-moment`; existing checkpoints keep their original source kind.

[established-bounded; measured] All 133 constitutive tests pass on CUDA in 27.39 seconds;
all 16 SDK alpha tests pass in 1.49 seconds. The five new native controls compare the actual
small field's exact rational current and ideal normalized-source learning law against every
forward/return ball and the full operator-error bound. They also check the numerical factor
decoder and oriented division bounds, complex phase/recharting, delayed reception, late-refusal
preservation and an archived continuation. Opposite dark sources retain their relative phase;
alternating actual targets cancel in the operator norm before its scalar bound is formed.

[established-bounded; measured] The
[portable conversation receipt](2026-09-07_moment_material/conversation-return.json) records
the private dataset runs. The initial four-family variant retains 732 development occurrences
and a 20,695,430-byte checkpoint. Its answer to “Explain the difference between a function and
its derivative.” is exactly `va` repeated 64 times. All 128 emitted symbols have resolved
receiver signs; generation stops at the caller's work limit. A separate process restores that
checkpoint and reproduces the response, full body report and emission-current reports exactly.
This is a failed language response, not a numerical obstruction.

[established-bounded; measured] Continuing that first checkpoint through four more families
retains 1,930 development occurrences. With the initial triangle-only operator-norm bound,
the same prompt emits nothing: bits 3, 4 and 6 are unresolved. The first response's coefficient
error is approximately `0.3200001`, while kernel evaluation error is approximately `5.97e-19`.
The larger obstruction comes from the accumulated coefficient bound, not division of the
homogeneous kernel. These decimals are exterior renderings of retained exact rational bounds.

[established-bounded; measured] A fresh eight-family run with signed norm transport uses the
same exposure records, source lineage and 72-bit grain. At the first response cut, the complete
junction report is identical and the material report differs only in current-error radii and
operator-error/norm bounds. The coefficient norm upper bound drops from about `1824.63` to
`16.6385`, and the forward radius from about `0.320866` to `0.00404160`. The same numerical
current now has resolved text signs. Its actual answer again repeats `va` 64 times; this
repair removes the numerical obstruction and still fails the requested language product.

[established-bounded; measured] The final eight-family checkpoint is 54,248,891 bytes.
Cultivation takes 54.81 seconds, prompt/emission 5.65 seconds and the entire fresh process
70.21 seconds on this desktop. Its development has zero numerical section readbacks; checkpoint
and cold diagnostics are separate exterior operations. A fresh process restores the final
checkpoint and reproduces the full body, generation and emission-current reports exactly in
23.38 seconds overall. Private models, detailed reports and prior failed variants remain in
`.local/artifacts/athena-alpha/ac2-moment/`. No other source model was overwritten.

[open] Athena-alpha and the full AC0–AC5 product remain unfinished. These conversation
prefixes contain 728/1,922 text octets; they are not a broad cultivated language model.
The [chronological future contraction](2026-09-07_AC2_THE_MOMENT_FACTORS_ADMIT_A_CHRONOLOGICAL_FUTURE_CONTRACTION.md)
provides a derived representation option for broader cultivation, with its
delayed-source and numerical obligations explicit. Reducing its work does not by itself
solve contextual progression or useful language. The live roadmap retains AC1’s missing
generative composition and AC2’s useful responses as the priority. The measured repetition remains an actual
failed response; no output filter, alternative emitter or inherited-language fallback hides it.
