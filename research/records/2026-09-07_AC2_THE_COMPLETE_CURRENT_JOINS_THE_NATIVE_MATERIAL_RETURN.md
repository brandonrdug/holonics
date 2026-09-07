# AC2: the complete current joins the native material return

[definition] This return implements the material attachment derived in
[the complete-source construction](2026-09-07_AC2_THE_FULL_INTERNAL_CURRENT_HAS_AN_ADDRESSED_PREFIX_PAIRING.md),
at parent revision `f5bcd865`. The explicit `CompleteCurrent` material-source variant uses the same
field owner and the ordinary source-qualified recurrence. Existing outgoing-only checkpoints and
their reported scopes remain supported. Athena-alpha remains unachieved.

## One field return and its full source

[definition] The material source is `x_s=(p_s,b_s)`: the retained coupled outgoing current and all
internal currents born by that source cut. Its exact pairing and numerical source error use the
already derived prefix geometry. The actual incoming material is `y`. The admitted return is

```text
T' = T + beta x_s*,       beta = (y - T x_s)/(1 + ||x_s||^2).
```

The source-time forward remains retained separately from the current-parameter source forward.
Their chronological difference and the actual returned difference are both preserved. The adjoint
in the parameter return is the retained complete source covector, not a newly authored source.

[established-bounded; source-inspected] `field_complete_material_transport.cuh` is called inside
the existing `section_constitutive_field` operation after the paired encoder is staged and before
its continuing writes. It stages the birth moment, full source, parameter proposal and new forward
together. Source consumption and the whole field commit occur through the existing owner only
after the complete return succeeds. A failed complete-source construction leaves the old seed,
memory, relation, covariance, current, coefficients and receiving capability intact.

[definition] Numerical coefficient increments are stored as exact rank-one factors
`beta_hat x_hat_s*` after `beta_hat` is rounded to the declared grid. The complete coefficient
expression remains source-qualified. For a new source, the existing derived folding reads

```text
M = sum beta_hat_s p_hat_s*,
A = sum beta_hat_s epsilon_s u_hat_s*,
a = sum beta_hat_s epsilon_s conjugate(w_hat_s),
T_hat x_hat_t = M p_hat_t + epsilon_t (A P_hat_t - a).
```

`M,A` use exact signed-magnitude words at scale `S^2`; `a` and unrounded forward currents use
scale `S^3`. The source/birth construction retains its mixed scales and all uncertainty.

[definition] An older source retains its original exact numerical forward. Its current numerical
forward is that value plus the contraction of the later retained coefficient factors:
`sum beta_hat_i K(source_i,s)`. The source addresses come from actual native lineage. Historical
carriers are remounted by the existing archive owner; the host assembles physical addresses only.
The device performs the contraction in chronological order. This evaluates current coefficients;
it does not repeat the past learning operations. Each output row is independent and the receiver
uses the mounted hardware's warp width, iterating over its rows.

## Numerical defects

[proved-derived] Let `E_dot` be the counted error in presenting the exact numerical source
contraction on grid `S`, `E_beta` the counted coefficient-factor division error, and `N_s` an
upward bound for `||x_hat_s||`. Since `||x||/(1+||x||^2)<=1/2`, the numerical parameter error is
bounded by `E_dot/2 + E_beta N_s`. The existing projector proof then gives

```text
E_T' <= E_T + (||T_hat||_F + ||y_hat||) E_x + E_y/2 + E_numeric.
```

The native norm bound advances by `||beta_hat|| ||x_hat_s||`. New forward error is bounded by
`E_T' (N_new+E_xnew) + ||T_hat_new||_F E_xnew + E_dot_new`. Every charge is rounded upward in
its stated grid. The gain denominator is the exact numerical norm square plus one; it is not a
rounded indefinite Gram form. All parameter products and exact contractions retain the wider
integer carrier or return an obstruction.

[definition] The native report retains six target-current balls: new forward, contemporary old
source forward, observed input, returned difference against the original forward, chronological
change, and contemporary difference. It also retains the numerical return factor, exact numerical
new forward, complete numerical source and parameter/error charges. The source/current/parameter
expression has an executable cold decoder. It does not supply productive inference or learning.

## Returned native evidence

[established-bounded; measured] All 79 constitutive tests pass. The four new controls establish
learning on the hidden-current witness, full exact source-qualified coefficient/current
reconstruction through complex phase and a delayed return, late-refusal preservation, and
complete-source archived rest/remount followed by further reception. The independent continuation
reference is founded separately; no live ecology is cloned for that comparison.

[established-bounded; measured] On the earlier reachable zero-boundary witness, an actual
reception of `1` through the source with internal current `(1/3,-1/3)` learns material currents
`2/11` and `-2/11` on the two opposite internal sources. Both source outgoing currents are exactly
zero. The native reading balls strictly separate the signs, and the complete exact coefficient
decoder checks the return. This is actual native use of the formerly omitted source direction;
it does not establish language quality.

[historical; process-audit] The first older-source contraction requested the general 512-thread
block and CUDA refused graph instantiation for register resources. Its row receiver now uses the
hardware's declared warp width and iterates over rows. The corrected native tests pass. No
numerical current, coefficient or source was removed to obtain that launch.

## Actual conversation construction

[established-bounded; measured] The first four development families enter through the public
text session with `--material-source complete-current`, reaching 732 native development
occurrences. The new checkpoint is saved at that development cut. The existing function/derivative
prompt then adds 62 occurrences, followed by one returned self-emitted octet, for 795 total.
All native operations and checkpoint publication return without refusal.

[counterexample; measured] The response is `.` followed by a text-receiver obstruction. It still
fails the request. One differential sign is uncertified across the retained current enclosure;
the current itself is not missing or a semantic uncertainty verdict. Neither an arbitrary bit nor
an end marker is substituted. This is not a useful alpha response.

[established-bounded; computational-witness] `inspect_complete_material_transport.py` verifies
all 795 complete-source/current/parameter numerical certificates, including 474 later-factor
contractions for older sources. It checks the native source geometry, exact numerical beta law,
folded coefficient state, source-time/contemporary/returned currents, full radii and numerical
defect formulas. This all-step numerical certificate is distinct from the exact physical
coefficient reconstruction exercised in the native controls.

[definition] The first private artifacts are under `.local/artifacts/athena-alpha/ac2-complete/`:
`first-four.hna`, `first-four.json`, process/stdout/stderr receipts and
`first-four-certificate-v1.json`. The checkpoint ends before the diagnostic prompt, as explicitly
reported by the batch driver. No claim of a durably retained interactive conversation is made
from that earlier development cut.

[open] Broader actual cultivation, general useful responses, efficient handling of long older-source
contractions and the full AC0–AC5 consumer product remain unfinished. Complete-current transport
currently admits the integral root-contact representation; other contact denominators need their
actual numerical construction. No Lean dependency, external memory database or foreign language
fallback is introduced by this return.

[historical; process-audit] Brandon paused the subsequent 60-family continuation to correct the
ontology and direction. At goal resumption its native PID `775122` and wrapper were absent.
The stderr ends at 33 completed additional families / 10,663 native occurrences; these are last
reported progress coordinates, not a final saved cut. The 242,309,599-byte partial history backing
remains, and the intended `cultivated-64.hna` was not published. The reason the stopped process
departed is not established by these observations. The earlier four-family checkpoint survives.
The [generator/Preimage Fibre correction](2026-09-07_GENERATOR_RECOVERY_AND_PHASE_TRANSPORT_REJOIN_TEXT_AND_ACOUSTICS.md)
now governs construction; more exposure to this fixed field is not the missing generative attachment.
