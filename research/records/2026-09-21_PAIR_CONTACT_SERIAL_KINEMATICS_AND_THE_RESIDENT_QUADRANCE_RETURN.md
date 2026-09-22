# Pair contact, serial kinematics and the resident quadrance return

**Date:** September 21, 2026. **Starting tree:** `363a6483`. **Direction:** execute the finalized
campaign, with Luna delegation authorized. This is its first construction return: the pair and
serial library owners, their formal laws, and a resident quadrance receiver consumed by the
existing HNN word. The fixed generator-machine source/phase binding remains the next consuming
operation in [the roadmap](../../docs/plans/THE_ROADMAP.md); this return does not identify the
legacy source-slot layout with that machine.

## The pair becomes an actual interaction

[established-bounded; implemented-exact] `holonic_interaction::helical::HelicalPairInteraction`
retains its `ScrewPair`, `PairQuadranceJet`, declared frame/parameter units, `Clock`, response,
weight and rate port. Its `interaction()` is the existing checked `HolonicInteraction`, with
`MediumContact` on two explicitly sized medium blocks. The local specialization uses unit
storage and zero skew structure; it is a declared contact/material reading, not a calibrated
physical evolution. The actual assembly is

```text
J_pair = [v_a | −v_b],    rates = C z,
J_medium = J_pair C,     M_medium = w C* J_pair* D_f J_pair C.
```

Positive weight and PSD response use the existing constructors. `material_kernel()` retains
material-null slip; `no_slip_kernel()` retains the kinematic kernel.
`material_power_implies_no_slip()` checks `rank(D_f J_medium)=rank(J_medium)`, so a globally
singular response can still be definite on the attained slip image. A singular response blind
to the image remains a separate case. `lock_reading` preserves signed/stationary rates and
returns a positive `LockAddress` only in that chart. These are local rate statements, not
periodic or attracting-lock claims.

[proved-derived; formal-checked] The fixed-generator feature return is
`J*λ_Δ + λ_Q DQ + (D²Q)*λ_DQ`. `PairFeatureCovector` implements it without discarding the
geometric/prestress Hessian term. `Transport/HelicalPairInteraction` proves the adjoint pairing,
Hessian quadratic, port congruence and PSD/material-null/no-slip laws. The pure rotating-circle
control has constant quadrance to its axis: the Gram and geometric Hessian terms cancel. A
separate translating pair makes the quadrance-gradient and Hessian contributions nonzero.

## Serial configurations, rates and receiving constraints

[established-bounded; implemented-exact] `holonic_chain::serial` composes the same
`SituatedScrew`/`ScrewGenerator`/`AffineMap3` owners. Its first exact joint charts are Cayley
revolute motions about coordinate axes/pivots and arbitrary-axis prismatic motions. The Cayley
parameter is `t=tan(θ/2)`, with `dθ/dt=2/(1+t²)`; it is not an angle or turn count. Each joint
validates its generator, chart parameter, clock rate and limit. A retained lift does not invent
a period. Broader finite screw flows remain at their stated #48/#62 scope.

[proved-derived; formal-checked] The local-joint product is `base ∘ T₀ ∘ T₁ …`. Native
`followed_by(next)` means `next ∘ self`, so the loop updates `prefix=T_i.followed_by(prefix)`.
`Transport/SerialScrewChain.serialFoldl_eq_configuration` connects that loop to the formal
ordered product. A quarter-turn about z followed by a local x translation moves along world y.
The spatial Jacobian recharts **unit-parameter** generators through the preceding product;
clock rates enter separately. Zero actual motion therefore leaves its available parameter
direction intact. The full continuous chain differential and generic proper-rotation
cross-product lift remain explicit formal obligations; the rational secant controls check the
implemented charts, including their exact Cayley remainder.

[established-bounded; implemented-exact] `closure_control` evaluates candidate parameter
vectors through the chain, checks limits and compares the resulting frames. It accepts no
caller-authored endpoint certificate. `prismatic_endpoint_fibre` derives the all-prismatic
linear target map and calls `ExactRatMatrix::preimage_fibre`; the returned particular solution,
nullspace and joint limits describe a constrained family. `admits` checks both the endpoint
equation and the limits. That intersection may be empty even when its ambient affine fibre
is nonempty. Unsupported nonlinear joints and an inconsistent linear target are distinct
returns. This is exact target inference at the all-prismatic scope, not general inverse
kinematics or a simulator result.

[established-bounded; implemented-exact] A link contact retains both link-local points, its
orientation and the full relative-velocity columns in joint coordinates. It creates one
`ContactFace` from `J_chain`, giving `J_chain* D_f J_chain`. Both sources' motion enters before
squaring; cross-joint terms survive. A common prismatic motion of both links cancels, while two
unit motions of only the second link add before producing power four rather than two on the
unit response. Covectors are in the parameter chart; evaluation at a physical/model clock
supplies that clock's parameter-rate vector once.

## The pair score reaches the resident HNN word

[proved-derived; formal-checked] For held β and geometric difference Δ,

```text
s(Δ) = −β⟨Δ,Δ⟩/2,
s(Δ+εd)−s(Δ) = −εβ⟨Δ,d⟩ − ε²β⟨d,d⟩/2.
```

`HelicalPairInteraction.pairScore_add_sub` proves this in arbitrary finite rational dimension,
including the realified complex row chart used by the native receiver. For separate geometric
query x, neighbors u and transported values v, let

```text
p = softmax(s),      y = Σ_i p_i v_i,
h = (diag(p)−pp*) (⟨g_y,v_i⟩ + g_p[i]).
g_x = −β Σ_i h_i(x−u_i),     g_u[i] = β h_i(x−u_i),     g_v[i] = p_i g_y.
```

[established-bounded; implemented-exact] `NativePairParticipation` executes that composition
through `pair_quadrance.cuh` and the existing normalized receiver/weighted-current owners.
Its geometric and value charts may have different widths. Forward and all three covectors
remain resident enclosures, with checked integer arithmetic, outward bounds, complete row
receipts and joined status. No host midpoint decides the result. The reverse result moves its
owned sections without extra numerical copies; when one source occupies both roles, the
consumer joins its two covectors through their declared chart maps.

[established-bounded; source-inspected] `IncidentParticipationChart::QuadranceCurrent` is the
explicit specialization `x=q_r`, `u_i=v_i=U_i q_i`. Its reverse therefore sums the neighbor's
geometric and value covectors before `U_i*`. This shared-source declaration is serialized in
`IncidentFieldSpec` and `IncidentFieldOptions`. Omitted fields mean legacy `Bilinear`, and that
arm remains omitted when serialized, preserving old wire semantics. Producing words and rest
retain the selected law. The example spec emitter accepts `incident-quadrance`. The field's
reaction, full global D/b return and publication contract are reused.

[definition] This current-quadrance arm is not the full moving-screw machine. Packet 3 still
supplies generator-family geometry, actual current/configuration/action maps, source injection,
phase/lift and tagged receiving phases. The generic resident receiver is ready for those
maps; it does not infer them from matching widths. Packets 4–7 retain their source-family,
material/clock, standing, economy and episode obligations. Both recorded text failures remain
open; no new conversation quality or fixed-machine cost claim is made here.

## Evidence and next consumer

[established-bounded; computational-witness] The resident controls distinguish axial separation
(logits `−1/2` and `−1`), independently sized geometric/value charts, nonzero input radii,
score-only receiving covectors and the full score/value return. The equal-distance value
control's enclosures contain output `2`, query covector `1`, neighbor covectors `−1/2` and
value covectors `1/2`. The HNN control executes the complete word and restores the frozen
quadrance comparison with exactly equal returned sections and material operands. These are
small declared mathematical controls, not trained Athena outputs.

[established-bounded; source-inspected] The [verification receipts](../../docs/VERIFICATION_RECEIPTS.tsv)
record exact changed-scope commands and their results. The first resident test process includes
cold CUDA setup; its elapsed time is not an isolated kernel or request latency. No full-source
GPU campaign or simulator was run. The next consuming operation is the generator-machine
geometry/source/receiver binding of #17, using these returned owners under the finalized
[contract](../../docs/plans/THE_ATHENA_ALPHA_CULTIVATES_GENERAL_CONVERSATION_THROUGH_NATIVE_CONTEXTUAL_TRANSPORT.md#situated-generator-and-receiving-composition).
