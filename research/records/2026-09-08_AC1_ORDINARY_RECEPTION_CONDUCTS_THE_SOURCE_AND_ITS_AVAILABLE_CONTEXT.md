# Ordinary reception conducts the source and its available context

[definition] This ordinary-cultivation construction uses the existing native field/material
owner. It replaces the study driver's historical-pair choice for the declared equal-source
families. Source, available context, observed return, reference history and both parameter
contacts belong to the same staged field operation. Useful language remains an AC2 obligation.

## Source and condition are separate operands

[definition] `s` is the actual addressed two-branch source in its root chart. `c` is the
complete paired-field current available immediately before reception: outgoing current and
all born internal currents. They need not have the same epoch when an old source is reused.
The material source chart is

```text
h(s,c) = (1,s) tensor (1,c),
Psi(s,c) = Q(s) tensor Q(c),
Q(x) = (1,x)(1,x)* / (1+||x||²).
```

The reference is explicit. The source and condition retain their original carriers and numerical
errors; numerical representatives are not installed as inferred physical causes. This extends
the existing phase-moment chart after the bound bilinear contact, including its source,
condition and mixed product. Both ports retain their own normalization.
It assigns no wavelength or semantic identity to an exterior codeword.

[proved-derived] The homogeneous bilinear contact has squared norm
`(1+||s||²)(1+||c||²)`. Its normalized outer product therefore factors as `Q(s) tensor Q(c)`
and has Frobenius norm one. Its exact pairing is

```text
<Psi(s,c),Psi(t,d)> = |1+<s,t>|² |1+<c,d>|²
                  / ((1+||s||²)(1+||t||²)(1+||c||²)(1+||d||²)).
```

This follows from the tensor-product inner product and the normalized Hermitian trace.
The existing complete-current prefix pairing supplies the contextual term. No full joint
matrix is enumerated, and reference off-diagonals retain both ports' relative phase.

[established-bounded; source-inspected] The initial direct-sum trial omitted the mixed
`source tensor condition` coordinates before taking its moment. It is retained as the
`Contextual`/`contextual-direct-sum` experimental variant with wire chart version 1. The complete
contact is `BilinearContextual`, chart version 2; fresh `--material-source contextual` selects
this corrected construction. Persisted chart kinds remain distinct, so old coefficients are
never silently reinterpreted in the new source chart.

[definition] A new emission presents `Psi(s_new,c_new)` after the completed field reaction.
A receiving occurrence with original source `s_old` instead conducts `Psi(s_old,c_before)`.
Its producing prediction stays attached to its original source/context and operator. Separate
receipts retain parameter change, condition change and their full returned discrepancy.

## Every later return contributes in the native reference frame

[definition] The first actual receiving occurrence of each exact visible source face fixes
its reference `(s,c_r,y_r)`. Discovery compares the canonical exact root-current face on the
device. Different occurrences remain different histories. The reference is a chart origin,
not a selected correct answer. Each later member `(s,c_i,y_i)` contributes

```text
d_i = Psi(s,c_i) - Psi(s,c_r),       t_i = y_i-y_r.
```

[proved-derived] These anchored pairs span all pairwise contrasts in that observed source
family: `(d_i-d_j,t_i-t_j)=(Psi_i-Psi_j,y_i-y_j)`. Thus anchoring does not exclude competing
observations or select one as the truth. A zero returned contrast is retained as well. These
are source-null comparisons in the fixed-source lifted condition chart; no claim of global
linearity in raw context is made.

[definition] Let the existing coercive operator-current contact be

```text
F(M,x,y) = M + (y-Mx) x* / (1+||x||²).
M_a = F(M, Psi(s,c_before), y).
M_next = F(M_a, d_i, t_i)          when a prior reference exists.
```

The two contacts are an explicitly ordered native composition. The ordinary contact has
denominator two. The contextual contact has denominator `3-2*k`, where
`k=<Psi(s,c_i),Psi(s,c_r)>` lies in `[0,1]`. Both contacts are staged before the one field
successor is published. This is a defined actual operator current, not a claim that the full
compatible operator family has become a singleton. A zero source difference cannot fit a
nonzero returned difference; its oriented discrepancy remains in the receipt.

[definition] The source/context error follows the normalized outer-product bound. For
either port `x=s` or `x=c`, `||x-xhat||<=e`, and any certified `L<=||(1,x)||`,
`||Q(x)-Q(xhat)||_F <= 2e/L`, capped by two. This follows by projecting the normalized
homogeneous vector onto the other vector's orthogonal complement. The implementation applies this bound to each source/condition factor. Since both
factors have norm one, their product error is at most the sum of those two errors, capped by
two. No new precision aperture is imposed.

[proved-derived] The coercive map has `I-xx*/(1+||x||²)` as its linear factor in `M`, with
operator norm at most one. Its rank-one factor and gain vector are blocks of `Q(x)`. For normalized homogeneous
vectors `u,v`, `||u u*-v v*||_op=sin(angle(u,v)) <= ||x-xhat||`, because the homogeneous
norm is at least one. Block compression cannot increase the operator norm, so both the
rank-one factor difference and gain-vector difference are bounded by `||x-xhat||`. Also `||x||/(1+||x||²)<=1/2`. Consequently a sufficient
operator-error update is

```text
E_next <= E + (N+||yhat||)*e_source + e_target/2
            + e_evaluation/2 + ||xhat||*e_beta.
```

The native implementation rounds outward and retains the original source operands, gain
remainder and oriented kernel-evaluation bounds. Computing the product of the two positive
kernel grid floors may omit up to three grid units; the signed beta contributions retain this
full oriented evaluation bound. For a fixed-source contrast the source self-pairing is exactly
one, and the coercive denominator uses the exact contextual kernel ratio. The signed cross-current in the operator
norm update remains intact. Immediately preceding sources share their operator and context
exactly; their parameter/condition differences are zero rather than two independent balls.

## Native and actual-model return

[established-bounded; source-inspected] The implementation lives in
`field/material_transport/contextual.rs` and `field_contextual_material.cuh`, under the existing
`NativeConstitutiveField` move owner. The fused field kernel publishes relation, held current and
material state only after both contacts complete. Fixed report metadata retains the actual
source, pre-reception context, first receiving reference and chart version. Rest checks those
against source lineage and the retained original profile. Exact ceiling-norm and profile-error
checks protect the lower norm used by the numerical decoder. The native text differential reads
the new report directly; cold inspection is separate from recurrence.

[established-bounded; measured] **141 native constitutive tests pass** (35.47 s), including an
independent rational reconstruction of the full bilinear source and two ordered ideal contacts.
Every reported current/error enclosure and oriented evaluation interval is checked in that
control, with delayed sources, complex phase, recharting, an unlinked occurrence and a zero
returned contrast. A late contextual failure after ordinary factor staging preserves the complete
predecessor and permits retry. A malformed standing bound reaches the shared refusal boundary
without stranding a CUDA block barrier. Full rest/remount continuation also agrees.

[established-bounded; measured] **20 SDK alpha tests pass** (2.86 s). Ordinary text intake
`ababac` forms its references natively and restarts; no test driver selects a historical pair.
The two actual-data `alpha_text` parent/partial-inscription regressions also pass (17.37 s).
These tests were run serially because the apparatus' initial allocation-grain receiver requires
an isolated VRAM measurement. Earlier overlapping runs failed that calibration before entering
the tested native operation; the serial results above are the completed checks.

[established-bounded; measured] The [public receipt](2026-09-08_ordinary_context/conversation-return.json)
records five actual private-conversation trials and preserves their artifact paths, costs and
complete generated strings. The corrected eight-family model's native receipts identify
receiving occurrences `12,20`, actual sources `11,19` and their common first receiving reference
`12`, in chart 2. Those references were formed during ordinary development, not supplied to it
by the later cold inspector.

[counterexample; measured] All five complete inspected responses fail the same request,
“Explain the difference between a function and its derivative.” The direct-sum eight/sixteen-family
trials repeat `n` plus a backtick, and `na`, respectively. The first corrected bilinear
eight-family trial begins `tife~` and becomes repetitive. At sixteen families its conservative
error bound leaves the first text receiver open, with no emitted text. Tightening the operator
source-error estimate then gives `Wmfa~ena~ena~…` through the 128-symbol work limit. This is
interrupted repetitive text, not a useful explanation or an attained alpha.

[established-bounded; measured] Comparing the conservative and corrected sixteen-family runs
preserves development records, lineage through the first response and that response's complete
junction exactly. The first material report differs only in error radii and its operator-error
bound. Its forward radius falls from approximately `0.0208376246` to `0.0104208797`; its numerical
current is unchanged. The improved proof certifies more signs and establishes no semantic gain.
The public receipt retains exact numerators and differing wire locations for this bounded check.

[established-bounded; measured] The latest fresh run develops **16 families / 5,064 native
occurrences** and saves a **183,509,491-byte** model before the fresh prompt. Development takes
**199.236018126 s**, issues zero numerical section readouts, and reaches **358,970,772 bytes**
of peak resident native payload. Whole-process time is **305.7586435569683 s** with peak host
RSS **2,194,532 KiB**; checkpoint/diagnostic time is included in that whole clock. Complete
historical factors and per-operation address tables remain growing storage/transfer costs.
These are not broad-corpus, physical-power or consumer-efficiency claims.

[established-bounded; measured] A **fresh-process restart** of that model with zero additional
families and the same prompt reproduces the complete final body, development records, generation
and emission-current history exactly. Its whole-process time is 58.63 s. The original direct-sum
eight-family model also restarts under the current executable with its original `contextual`
kind, identical lineage and identical generation; no coefficients are reinterpreted as bilinear.
The full private reports and checkpoints remain in
`.local/artifacts/athena-alpha/ac1-ordinary-context/`.

## Remaining AC1–AC2 attachment

[definition] This construction supplies anchored contrasts for the declared equal visible-source
families. It does not establish all source-null combinations across unequal source faces, general
class formation, a unique compatible cause or useful learned text-codec conduct. The actual
coercive current is defined by its contact law; the retained observation/family evidence is not
silently collapsed into a claim of identification.

[established-bounded; source-inspected] `TextFieldSession::generate_with_receiver` currently
reads the text differential and calls `receive(symbol)`, which supplies the exterior unit
codeword as the next input. The separate `stage_native_return` route instead retains an actual
exact point current. The enclosed material current cannot simply enter that exact port: its
numerical centre is not its full current. This identifies a concrete continuation boundary to
review, without establishing that it causes the observed language failure.

[open] Continue AC1's contextual organization and AC2's productive continuation from the actual
source/condition/returned differences. Derive the contact and uncertainty requirements before
changing the generation boundary, then inspect full responses and contextual revision. The full
AC0–AC5 objective remains active. Lean remains outside cultivation and inference, and the retired
external memory database remains unused. No new Apple or acoustic execution was performed.
