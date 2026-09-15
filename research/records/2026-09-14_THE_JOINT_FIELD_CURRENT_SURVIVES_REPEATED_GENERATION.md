# The joint field current survives repeated generation

[project-postulate] Brandon's “Continue Athena” resumes the public field-backed model. The
consuming operation is the same joint quarter-turn task in `athena_field`; the earlier
48-target attempt completed 39 targets and then overflowed in the paired adjoint. This
increment repairs the common current representation inside that model and its native rest.
The previous failure and one-pass outputs remain available in the
[experiment](../experiments/athena_field/README.md).

## The mathematical change

[definition] At a supplied exact condition h, the stored local material contracts to
`r=A(h)s+c(h)`. One generated section is

```text
q = (s,b)
F_h(q,x) = (A(h)s+c(h)+x, b)
q_next = S_D F_h(q,x)
y = boundary(q_next)
```

[proved-derived] If q belongs to a joint Euclidean ball of radius rho and x belongs to an
external ball of radius epsilon, the unrounded affine image is enclosed by
`max(||A(h)||_2,1)*rho+epsilon` when the internal tail exists. With no tail its coefficient
is `||A(h)||_2`. This follows by applying the block diagonal map to the single vector
`(delta_s,delta_b)`: its squared norm is bounded by
`max(||A(h)||_2^2,1)*(||delta_s||^2+||delta_b||^2)`. Restricting q twice and then adding the
marginal radii discards this joint restriction. The exact constituted scattering S_D is
unitary for the admitted paired solve; the existing reflection evaluator adds its signed
solve, material and arithmetic remainder to that transported input ball.

[established-bounded; source-inspected] `normal_applied_condition.cuh` contracts the actual
stored M at exact h before calculating its gain. It uses an outward dyadic enclosure of the
Frobenius norm of A(h), through exact coefficient products, division and integer square-root
operations. This is an upper bound on the spectral norm, not a claim that the two norms
coincide. The external radius and final coordinate-rounding remainder are added explicitly.
No uncertain source is converted to a point and no native float chooses a current or bound.

[established-bounded; source-inspected] The existing material view exposes
`read_applied_bilinear_joint`; the retained reaction exposes `apply_joint_current`.
`FieldModel::prepare` consumes that joint action directly. The separately retained reaction
still supplies its producing source/condition and normal-material response to an actual
model target. The forward centres and D/M learning laws are unchanged by this repair.

## One current and its persistence

[established-bounded; source-inspected] The field junction retains one immutable complete
reflection image qualified by the producing report and internal-current owners.
`read_current_source` shares that image while both owners match. A material-only return
retains the unchanged internal-current section; a changed report or internal current
invalidates the image automatically. A committed reflection replaces the image after all
fallible resident work succeeds. These are source qualifications, not an event archive or
a second continuing model.

[established-bounded; source-inspected] Field-rest versions 5/6 serialize that one image in
addition to the existing material/report sections. Their explicit report-presence byte also
supports a model that has generated before an ordinary observation. Versions 1–4 keep their
wire meaning. Validation compares the image against the outgoing report block and the actual
operative b coordinates, including the published common radius. Remount shares the restored
internal section instead of mounting a duplicate and breaking its owner identity.

[definition] This retains a common outer ball. It does not assert that every anisotropic or
nonlinear preimage fibre is represented exactly by that ball, or that every learned recurrent
operator is contractive. Source-qualified directional/factor representations remain available
when the admitted operator and task require them. No such further representation is made a
prerequisite for returning the current model task.

## Returned model task

[established-bounded; measured] The unchanged 48-target task now completes and reopens.
Held-out squared centre error is `3.4960448479268558` after training versus
`267.35802469135797` before training, a 98.692% reduction (exterior decimal readings of exact
rational comparisons). The largest output radius is `1717/281474976710656`. All four complete
held-out balls agree after file read/remount. The actual output, trained model, source/target
population and measurements are in the [experiment return](../experiments/athena_field/README.md#completed-repeated-generation).

[established-bounded; measured] The warm isolated debug process takes 1.088606 seconds and
peaks at 291,096 KiB RSS; native section accounting peaks at 195,156 bytes. The 81,449-byte
model includes its current/report, D/M material and the existing operative journal. This
increment does not compact that journal or claim bounded total storage for arbitrary repeated
training. Five focused tests, 165 wider native regressions and 12 public HNN tests pass, including
the previously delivered model-file compatibility fixture. The original one-pass
centres and errors remain exactly unchanged, and its new rest reproduces its four final balls.

[project-postulate] The next consuming operation is the source/receiver-relative field action,
including the actual receiver map and its variation in the same forward/adjoint. For
`y=E q_next`, `delta_y=(delta_E)q_next+E delta_q_next`; varying h/D/current requires their
corresponding terms inside `delta_q_next`. A common coordinate rechart must commute, while
physical relative motion changes the received face through the actual transport. The present
fixed-condition bound is not substituted for that complete derivative. This continues the
same public model; the roadmap retains pending-return durability and Athena application work.
