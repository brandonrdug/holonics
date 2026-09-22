# The pair response returns its rectangular factor cotangent

[definition] This is the first material-inference operation after the
[public generator source/session return](2026-09-21_ORDERED_SOURCE_AND_PHASE_RECEIVING_ENTER_THE_PUBLIC_GENERATOR_SESSION.md).
It returns an actual parameter cotangent through the existing global field action. Positive
parameter proposals, their publication and compatible geometry/closure inference remain the
next consuming operations; this return does not silently publish unconstrained D updates.

## The parameter and its producing source

[definition] The engine's global D is the rectangular boundary-by-contact coupling factor.
For a declared basis block B_a and amplitude rho_a, `D(rho)=Σ_a rho_a B_a`. The symmetric
contact form is a different object and scales quadratically. Thus

```text
delta D = delta rho_a B_a
lambda_rho_a = Re <G_D, B_a>_F
(rho B)^* (rho B) = rho^2 B^* B.
```

The factor cotangent cannot be contracted with the Gram form as if they had the same domain.
In particular, `2 rho` belongs to differentiation of the Gram form, not to this rectangular
factor derivative.

[definition] `NativeFieldActionPullback` already retains the complete q/b return as two factors:

```text
P0 = (h_q + g_q)/2,       P1 = x_q + y_q
C0 = x_b - y_b,           C1 = (g_b - h_b)/2
G_D = P0 C0* + P1 C1*.
```

The new `NativeFieldCurrentSource::declared_factor_scale_gradient` consumes those producing
operands and a source-qualified pure-CSR basis. A group is a contiguous set of contact columns;
the HNN pair binds three structural rows per arc, including zero rows. The returned object
retains both basis and producing field sources, with one real scalar enclosure per group.
All arithmetic and intermediate sections remain resident.

## Complete uncertainty and HNN consumption

[definition] With joint two-factor radii rP and rC, the matrix error satisfies
`rG <= rP ||C|| + rC ||P|| + rP rC`. The scalar receiving error additionally includes
`rG ||B_a,centre|| + (||P|| ||C|| + rG) rB`, plus outward arithmetic error. The norms cover
both factors jointly. A structurally zero centre group does not eliminate a nonzero global
basis-error bound. CSR columns are even real-component addresses; treating them as complex
channel indices reads different operands.

[definition] `NativeCoupledBody::prepare_incident_material_return` now collects this arc
cotangent across every producing source/refinement step and exposes
`NativeIncidentMaterialReturn::contact_scale_covector`. Here the basis is the producing
arc block itself, so the coordinate is a relative amplitude variation at that cut. The
complete internal-current contribution remains included. Existing E/M/text/stop publication
continues independently; the pair configuration and response remain fixed until the
constrained publication owner is constructed.

## Checked algebra and remaining construction

[established-bounded; formal-proof] `Transport/ContactFactorScale.lean` proves the rectangular
amplitude variation, directional pairing, quadratic Gram law, unchanged null kernel for
nonzero amplitude and the two-factor Frobenius contraction. Its real-coordinate statement
applies to the machine's realification. Dynamics imports it; the integrated Framework passes
at 9,210 jobs. The focused theorem axiom audit uses only standard axioms.

[established-bounded; computational-witness] Two native checks pass using a genuinely complex rectangular CSR basis with two groups,
nonzero q/b input and both output covectors. Their independent exact rational reference
realifies D and computes

```text
A = I + D_r D_r^T
v = A^-1 2(a + D_r b)
delta v = A^-1 [2 delta D_r b - (delta D_r D_r^T + D_r delta D_r^T) v]
delta out = (delta v, delta D_r^T v + D_r^T delta v).
```

The [verification receipts](../../docs/VERIFICATION_RECEIPTS.tsv) give the actual native
results and their scopes. This is an operator/parameter return, not evidence of improved
general text or a completed material-learning campaign.

[established-bounded; computational-witness] Six HNN checks pass across the fixed machine,
ordered source episode and public generator session. They exercise the returned arc covector,
the complete source reverse, codec growth and byte-identical resumed/uninterrupted state.
The combined engine/HNN test build passes. The first native process includes 228.91 seconds
of cold CUDA setup and checking; it is not a per-request latency measurement.

[project-postulate] The next constrained owner must keep the amplitude positive, retain the
active parameter and old producing cuts, and publish a map inside the declared pair family
with its coefficient error. Direct CSR scaling needs an explicit causal/rest receipt. A
pair-derived low-rank update can use signed factors—the positivity of a step size does not
forbid a negative matrix increment—but needs a retained parameter and a compaction law.
Neither route licenses an arbitrary operator delta or an unrecorded reset of the initial map.
