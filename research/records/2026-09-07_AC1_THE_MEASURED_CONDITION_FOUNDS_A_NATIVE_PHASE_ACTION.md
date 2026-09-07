# AC1: the measured condition founds a native phase action

[definition] Parent `16dee286`. This return composes the existing native local relation with
the existing complex bilinear contact law. It answers the next question raised by the
[corpus relation's vertical directions](2026-09-07_AC1_THE_FIELD_RETURNS_A_RESIDENT_RELATION_FACE_AND_A_PLURAL_FIBRE_HAS_FIXED_RECEIVERS.md):
can an independently measured condition participate in a learned action, instead of pooling
different conditions into one unqualified source map? The returned scope is a rational phase
family, not a conversation or acoustic model.

## The bound source chart

[definition] `ConstitutiveSourceChart::BilinearContact` binds two complex input roles at founding.
For source `s` and condition `c`, the native contact carries

```text
Phi(s,c) = s direct_sum c direct_sum (c tensor s).
```

Both direct currents and every complex mixed product are retained. The existing rational-linear
relation receives `(realify(Phi(s,c)), y)` only when the actual receiving current `y` arrives.
Its domain, vertical fibre and staged row law are unchanged. In a functional chart this admits
`Gamma(s,c) = A s + B c + C(c tensor s)`, with the real-linear maps determined by observations.
This is an explicit local constitutive hypothesis, not a claim that every context or HNA ecology
is bilinear. A condition must come from its actual channel/receiver circumstances; the interface
does not turn arbitrary caller labels into context.

[definition] `ResidentConstitutiveFibre::found_bilinear_contact` allocates that declared chart;
`advance_bilinear_contact` accepts two resident currents and optional actual reception. The
ordinary flattened/linear ingress refuses on this body, so a caller cannot bypass the source law
by supplying an authored feature vector. Two decompositions with the same flattened extent retain
different source/condition roles. The caller's port dimensions are explicit interface choices.

[proved-derived] The mixed current has the finite difference

```text
(c+dc) tensor (s+ds) - c tensor s
  = c tensor ds + dc tensor s + dc tensor ds.
```

This follows by bilinearity. Retaining only the first two terms loses the simultaneous change.
The construction composes the complex product already carried by the native phase and mixed-contact
owners; it does not infer contact from mere co-presence. The operation declares the two interacting
ports and preserves their distinct roles.

## Native implementation

[established-bounded; source-inspected] The source owners are:

- `native_ecology/constitutive_fibre.rs`: bound source chart and existing relation founding;
- `constitutive_fibre/resident.rs`: exact rational views and one ordinary contact/return operation;
- `resident_section/surface_passage.rs::record_constitutive_bilinear_source`: source/condition
  shapes, same-surface admission and physical scratch extent;
- `exact_resident_section.cu::section_constitutive_bilinear_source`: direct and mixed current,
  using `fibre_current_denominator`, `fibre_phase_product` and `fibre_normalize`;
- the existing `section_constitutive_current`: query and staged relation formation.

[definition] The two input denominators are carried exactly. Direct terms and mixed products
share a checked common denominator, then normalize together. One native lane constructs the
contact; the dependent lane reads/forms the existing relation. All pointness, denominator, shape,
overflow and output checks precede the only continuing basis write. A refusal leaves the body and
its occurrence count unchanged. Host code schedules the two lanes but reads no numerical current
to determine the contact or deposit.

[definition] `NativePhaseCurrent::words` exposes its already validated exact exterior tuple;
`ResidentConstitutiveCurrent::rational` borrows numerator coordinates followed by one denominator.
These are codec interfaces. Numerical validity is checked on device when the view is consumed.
Neither tuple values nor source-chart dimensions identify a semantic class.

## Actual native observations and recovered action

[established-bounded; measured] The public
[`native_conditioned_phase`](../../crates/holonic-engine/examples/native_conditioned_phase.rs)
example controls the incoming phase of a native matched two-port field and measures its held
successor. The learner receives source, independently supplied channel condition, and that actual
native response. The driver contains no learning algorithm or source/condition multiplication
which fabricates the teacher's answer. Six declared observations span the local source chart;
six is the experimental population, not an admission threshold in the learner.

[established-bounded; measured] For a previously unobserved condition `(3+4i)/5` and source `2+3i`,
the learner predicts `(-6+17i)/5` before the teacher executes that condition. The subsequent native
field return agrees exactly. A comparison receiving the same source/return observations while
omitting the condition has a plural relation. Thus the condition participates in the action;
there is no source-ID or per-phase switch selecting it.

[proved-derived; computational-witness] The cold receiver of the learned basis verifies six
nonzero source pivots and, in every row, `target.re = mixed.re`, `target.im = mixed.im`. Those
pivots span the declared six-real-coordinate source chart; hence the represented relation is
exactly the graph of `Gamma(s,c)=c*s` in this chart. This proves the recovered polynomial action
of this body, not the identity of the teacher's hidden implementation or the validity of that
family for arbitrary exterior sources. The coefficient receipt is in `return-v2.json` below.

[proved-derived] For that recovered action, complex multiplication gives
`Gamma(Gamma(s,d),c)=Gamma(s,c*d)` and `Gamma(s,1)=s`. Restricting conditions to unit norm gives
the corresponding phase action and preserves the current norm. These are consequences of the
identified local action. Exact word execution still has its reported finite arithmetic aperture.

[established-bounded; measured] Holding the new condition fixed, actual resident continuations
return `(3+4i)/5`, `(-7+24i)/25`, and `(-117+44i)/125` from initial current `1`. Each has norm square
one. The emitted current itself supplies the next source without remount or numerical readback.
The retained relation is generative standing; the learner does not store a table of those future
values. The example's transcript is a cold observation, not an independently executable model file.

## Evidence and cost scope

[established-bounded; measured] The existing constitutive regression scope plus the first four
new contact controls passed: **93 tests**, zero failures, 58.80 seconds in
`/tmp/athena-bilinear-all-tests.log`. A subsequently added multiport control passed separately
(`/tmp/athena-bilinear-multiple-ports-test.log`): it checks all four complex cross-products with
different rational denominators, and refuses swapped source/condition roles despite equal total
extent. The other controls cover new physical conditions, native recurrence, the nonzero mixed
finite difference, explicit chart binding, and refusal before deposit. The native kernel uses
the existing checked complex-product helper. No Lean source or pipeline was changed.

[established-bounded; process-audit] The public example build passed. Its initial report attempted
to serialize `ResidentSectionRest` directly; the corrected cold report explicitly presents its
rows, width, grain and interval words. Both returned runs are retained:
[initial return](2026-09-07_conditional_phase/return.json) and
[return with the operator-identity receiver](2026-09-07_conditional_phase/return-v2.json).
Reproduce in a fresh destination with:

```sh
cargo build -p holonic-engine --example native_conditioned_phase
target/debug/examples/native_conditioned_phase NEW.json
```

[established-bounded; measured] The second example returned in 0.138 seconds by its own whole-run
clock on the standing desktop. Its three successive learned operations performed zero numerical
section reads/egress and uploaded twelve bytes of predecessor-edge metadata in total. The
withheld prediction also performed zero numerical section reads/egress. Source and condition
tuples were mounted before those measured intervals. The report's total apparatus census includes
the teacher and cold diagnostics; this small phase study establishes no general throughput,
audio latency, model footprint or power claim.

## Shared Mac work and next desktop construction

[definition] This is a useful point to re-engage the Mac workflow on the **shared conditional
generator primitive**. Apple `bd3ea689` was checked again and already has the field teacher and
`fibre_query`, `fibre_stage`, `wnorm` and `phaseprod` in `accelerators/metal/native_phase.metal`.
The [hardware guide](../../docs/HARDWARE_AND_MODALITY_BOUNDARIES.md#conditional-generator-port-for-the-mac-workflow)
states the concrete Rust/Metal port boundary. The forward local source law and receiver wire are
now executable and tested here; full conversational or acoustic usefulness is not a prerequisite
for beginning that shared port and research.

[open] General acoustic organization, note/chord identification and measured sound production
remain Mac work. The desktop conversation model still has its recorded failed responses. Its
conditions must be derived from the actual situated material and channels; replacing the missing
condition with a label or an arbitrary larger polynomial of the same inadequate local face would
repeat the earlier error.

[definition] The next desktop attachment is the **condition Preimage Fibre** inside this same
learned action: hold an actual source and later receiving current fixed, derive the compatible
condition family, and use its supported consequences in subsequent transport. For a functional
local chart this is `{c : (B+C_s)c = y-A*s}`; in the general represented relation it is
`{c : (Phi(s,c),y) belongs to R}`. Fixing `s` makes the latter an affine section in `c`, so the
existing native elimination can carry a particular solution, free directions or a scoped
obstruction. This is inference from limited observations, not inversion of the complete past.
Its resident implementation and real conversation attachment remain open.
