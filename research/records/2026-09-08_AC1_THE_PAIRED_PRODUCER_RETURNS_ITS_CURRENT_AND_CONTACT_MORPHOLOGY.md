# The paired producer returns its current and contact morphology

[definition] This continues AC1–AC2 from the
[material context cotangent](2026-09-08_AC1_THE_MATERIAL_RETURN_HAS_A_CONTEXT_COTANGENT.md).
The actual paired producer now has an exact differential and adjoint reference, checked against
native conduct and on the conversation model. This does not implement its developmental return
inside the native successor or establish useful language.

## The producing map and its separate operands

[definition] Use the existing paired-junction source and unit constitutive metrics. The contact
columns are `D=[d_i]`, their row map is `R=D*`, and `A=I+R*R=I+D D*`. The entering exterior
current is `u`; `b` is the complete internal input, with zero in a just-born contact row. The
actual producer is

```text
v = 2 A^-1 (u+R* b),
o = v-u,               b_plus = R v-b.
```

For fixed morphology this is the reflection `S_R=2P_graph(R)-I` on the complete incoming
`(u,b)`. Its complex phase, internal population and source/receiver roles remain distinct.
A source-only chart is a restriction of this producer, not the whole return.

[proved-derived] The reflection is Hermitian and unitary: `S_R*=S_R`, `S_R^2=I`. Consequently
its current differential is itself, and its full current adjoint preserves the unit-metric norm.
Appending a zero-current birth is an isometric inclusion. Its adjoint returns both the old-current
component and the new row's constraint reaction; the latter cannot be silently varied before birth.

[definition] These are partial derivatives of the paired primitive at its actual producing cut.
The material operator and earlier state-building operations are fixed operands of this primitive
calculation. It is not the complete Jacobian of every earlier material update or the entire
recurrent history. Their dependencies and retained overlays remain part of the joined return.

## Morphology has a rank-two return

[proved-derived] For independent variations of `u,b,R`, put `k=2b-Rv=b-b_plus`. Directly
differentiating `A v=2(u+R*b)` gives

```text
delta_v = A^-1 [2 delta_u + 2 R* delta_b
                + delta_R* k - R* delta_R v],
delta_o = delta_v-delta_u,
delta_b_plus = delta_R v + R delta_v-delta_b.
```

The two morphology terms are both necessary. Neither differentiating the right-hand side alone
nor holding `R*R` fixed while changing `R` gives this derivative.

[proved-derived] Given the output covector `(g_o,g_b)`, solve
`lambda=A^-1(g_o+R*g_b)`. Pairing the displayed differential in the real part of the complex
inner product returns

```text
g_u = 2 lambda-g_o,
g_b_in = 2 R lambda-g_b,
G_R = k lambda* + (g_b-R lambda) v*.
```

In the contact-column chart, `G_D=G_R*`, so

```text
G_D = lambda k* + v (g_b-R lambda)*.
```

Thus the complete contact-morphology covector is a sum of two oriented outer products.
Its rank is at most two. The two factors remain retained when their sum cancels; no singular
vector or preferred cause is selected. The adjoint uses the real Frobenius metric on complex
contact maps. A contact-phase rechart carries this covector with the actual contact chart.

[established-bounded; implemented-exact] The existing junction owner now contains the cold
[`PairedJunctionLinearization`](../../crates/holonic-engine/src/native_ecology/constitutive_fibre/field/junction/producer.rs)
reference. It composes `ExactRatMatrix` and `ExactComplexWaveCurrent`, retains an immutable
producing cut, and supplies pushforward, full current pullback and the two contact factors.
It is not a second ecology, CUDA operator or public cultivation loop. Enclosed actual operands
retain their uncertainty separately from this exact numerical reference.

## Native and actual-data checks

[established-bounded; measured] Four exact Rust controls verify full complex differential/adjoint
duality, current reflection/isometry, rational contact-phase covariance, scalar analytic contact
derivatives, empty contact families and shape refusal. An additional CUDA control follows one
actual enclosed field through four occurrences, phase rechart and delayed shared-source reception.
Its complete potential, outgoing current and every decoded internal current match the producer
reference exactly. These are five focused checks; no new native developmental law was exercised.

[established-bounded; computational-witness] The
[actual-model observer](../experiments/alpha_passive_junction/inspect_paired_producer.py) joins the
material return at receiving occurrence **20** to producer **19**, whose input is the standing
at **18**. The producer has nineteen contact rows; eighteen are old internal-current inputs,
and the nineteenth is its zero-current birth. The observer retains that last row's constraint
reaction separately. The same saved bilinear model and already exported material history are used;
no additional exposure, native deed or model update occurs.

[established-bounded; computational-witness] Its full material cotangent has error at most
`2.096996798288666e-11`. The squared norm of the returned **old internal-current** component is
approximately **0.009121912909929614**. Because the producer's current pullback has norm one,
that component is certified nonzero. A concrete old-current tangent constructed by the observer
also satisfies the exact isometry and adjoint pairing identities. This resolves the previously
open question about a nonzero return through this existing paired-current input range, at the
stated partial-derivative scope.

[established-bounded; computational-witness] The contact-morphology covector has squared
Frobenius norm approximately **0.15986733603574851**, with error at most
**1.709413150104801e-10**. It is certified nonzero as well. The
[portable receipt](2026-09-08_paired_producer/producer-return.json) retains the full oriented
current returns, birth population, constraint reaction and both contact factors, with exact
rational values and bounds. Inspection takes 0.58 s after the prior cold history export.

[proved-derived] The current error transfer uses `||S_R||=1` and
`||A^-1[I,R*]||<=1`. Also `g_b-R lambda` is the internal block of
`(I-P_graph(R))g`, whose norm is at most `||g||`. Let `e_g` be the full cotangent error,
`e_c` the producer's complete current error and `e_previous` the prior current error.
The source `u` and contact map are exact in this model. With numerical factors bearing hats,
a sufficient contact-covector error is

```text
e_k = e_previous+e_c,
e_D <= e_g (||khat||+e_k) + ||lambda_hat|| e_k
       + e_c (||ell_hat||+e_g) + ||vhat|| e_g,
ell = g_b-R lambda.
```

Each term follows by expanding one outer-product difference. The observer uses exact rational
arithmetic and outward integer norm ceilings. No numerical centre is installed as a current.

[established-bounded; source-inspected] The producer comparison caught and corrected a cold
observer defect: `explicit_context` had added a factor `(-1)^birth` to each internal coordinate.
The prefix already alternates by occurrence, so the native decoder requires `(-1)^at`, with
birth determining the lower prefix cut. The erroneous factor was a fixed per-contact unitary
rechart: it preserved the previous norm, kernel and scalar cotangent checks, while mismatching
the un-recharted native `R`. The corrected observer now verifies `b_plus=R v-b` as well. The
previous scalar cotangent result remains exactly unchanged, and no native coefficient or model
artifact was changed by this repair.

## Successor and chronology obligations

[definition] A morphology covector is not permission to rewrite an observed contact's source
or its old realization. Native construction must retain the immutable birth/source description
and separately carry its evolving operative contact map. The current junction has only the
fixed-contact realization and its condensed `(C,h)` current; a productive update needs the
operative map/return and its executable current decoder in that same owner.

[proved-derived] For a current contact change `DeltaD`, the complete next moment is

```text
C_next = C + D DeltaD* + DeltaD D* + DeltaD DeltaD*.
```

For simultaneous internal-current change `Delta b`, its aggregate is
`h_next = h + D Delta b + DeltaD b + DeltaD Delta b` before the next reflection. The mixed
terms cannot be dropped. The rank-two return supplies compact operator factors; this does not
by itself prove constant memory or a lawful future-receiver condensation.

[proved-derived] Changing contacts invalidates the fixed-contact prefix shortcut. With actual
chronological columns `d_i(k)` and zero input at birth `j`, the general decoder is

```text
b_i(t+1) = sum_(k=j)^t (-1)^(t-k) d_i(k)* v_k.
```

This follows immediately by induction through `b_i(k+1)=d_i(k)*v_k-b_i(k)`. Every earlier
operative contact belongs to its own forward cut. A new deposit joins the successor after the
complete return; it never changes that earlier summand. A cold stored sum is not a substitute
for the required resident representation and executable decoder.

[proved-derived] An old internal-current variation transports through later fixed-input
producer passages by their actual internal blocks
`H_k=2R_k(I+R_k*R_k)^-1 R_k*-I`, with zero-extension at births. Each block has norm at most one.
The corresponding outgoing differences must remain part of the transported return; they account
for current leaving that internal projection. This supplies the chronological transfer for a
return to an earlier current without editing the past. It is not an inverse reconstruction law.

[definition] The next AC1 construction is now concrete: compose the native joint constitutive
return for material parameters, retained current and operative contact morphology; retain the
actual producing maps, metrics, old overlays and chronological transfer; and publish its complete
successor atomically. The joint coercive tangent contact derived in the preceding record is
available with this producer differential. Its native implementation must include the operative
map/current representation and bounds, rather than applying this cold covector as a displacement.
A current-only or source-drive-only update must not silently replace the morphology return.
Then exercise the changed model on actual conversations and inspect AC2's complete responses.
The full AC0–AC5 goal remains active and Athena-alpha remains unattained.

[definition] Reproduction: run the five `junction::producer::tests` with `--include-ignored
--test-threads=1`, then run `inspect_paired_producer.py HISTORY --receiving 20 --report NEW.json`
using Python `-P` and SymPy. The private receipt is
`.local/artifacts/athena-alpha/ac2-contextual-diagnosis/producer-return-v1.json`. No Lean execution,
external memory database use, new Apple kernel or acoustic implementation was involved.
