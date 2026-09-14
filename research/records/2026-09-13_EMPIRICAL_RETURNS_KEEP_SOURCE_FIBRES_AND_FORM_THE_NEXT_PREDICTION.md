# Empirical returns keep source fibres and form the next prediction

[definition] This continues the live HNN assembly from `ce288e14`, using the
[boundary/interior source](2026-09-13_BOUNDARY_AND_INTERNAL_CURRENTS_FEED_JOINT_HNN_PREDICTION.md).
The returned operation consumes a later observation at a retained prediction, develops the
local predictive material, and makes that material available to subsequent generation through
the same `NativeCoupledBody`. The construction retains the full source family, producing
condition, discrepancy and numerical bounds.

## Returned generating relation

[definition] For the original producing pair `(p_s,c_s)`, condition h_s, and emitted prediction
v_s, an observed next state y supplies

`a_s=(c_s-p_s,c_s,p_s)`, `eta_s=y-c_s`, `delta_s=y-v_s`.

The Wave chart uses a_s. The bilinear feature chart uses `f_s=(a_s,h_s,h_s tensor a_s)`.
The current local material receives the existing unit-prior normal increments

`H_next=H+f_s f_s*`, `B_next=B+eta_s f_s*`, `E_next=E+eta_s* eta_s`.

[proved-derived] For enclosing centres x,y and radii r_x,r_y, the existing moment owner
retains the full nominal matrices and bounds their errors by

- `(2||x||+r_x) r_x` for the source-normal matrix;
- `||y|| r_x + ||x|| r_y + r_x r_y` for the cross-source matrix;
- `(2||y||+r_y) r_y` for target energy.

These follow by expanding each outer product and applying the triangle/product norm bounds.
They cover correlated operands as well: no distribution or independent-source assumption is
needed. Numerical rounding enters the operand radii before these increments. The generating
material retains stored dyadic M and its normal-reference bounds separately.

[established-bounded; implemented-exact] `NativeCoupledBody::observe` dispatches this operation
to `ResidentNormalWave::observe_coupled_prediction` or
`ResidentCoupledConstitutive::observe_prediction`. `NormalCoupledObservation` exposes the
source, observed state, target increment and signed discrepancy as resident enclosures, together
with source/produced families and any backward joins. The selected member must have attached
normal predictive material. Its compatibility relation remains available for the separately
declared condition-contact/constitutive-incorporation operation.

[established-bounded; implemented-exact] Formation uses the producing condition and updates
contemporary M. It consumes the addressed pending prediction and invalidates stale affine
contact admissions. The held wave state retains its original producing map and wave epoch;
the material observation count increases. The existing observed-next and source-actuation
operations retain their own current-transport contracts.

## Whole-family bounds and shared native primitives

[proved-derived] Write the supported family as an affine relation between anchor and output,
with its anchor restricted to a ball of radius R. Let U be its anchor tangent space, x_* the
nearest admissible anchor to the ball centre, and A its output map on U. If there is no vertical
output direction, then

`||output-output_*|| <= ||A P_U||_2 R
 <= max(||A P_U||_1, ||A P_U||_infinity) R`.

Projection gives `||x-x_*||<=R` for every admitted x. The matrix bound follows from
`||K||_2^2<=||K||_1||K||_infinity`. The implementation rounds coefficient magnitudes outward
and adds the centre's rounding error. Nonzero unconstrained vertical output has no finite
enclosure at this port; the original source family and its generation remain available.

[established-bounded; implemented-exact] `NormalWaveFamilyReceiver::enclosure` uses the
retained joint and anchor basis. It reconstructs the anchor projector because the original
receiver reuses its projection scratch for a later vertical projection. Workspaces have checked
dynamic extents and remain owned through CUDA launch. Generated point words retain centre
rounding even when their true radius is zero. Tests cover identity, negative fractional slopes,
partial anchor domains, empty support, vertical freedom and 72-bit source/output charts.

[proved-derived] The reused wave lift satisfies `||phi(delta p,delta c)||<=sqrt(3)R<=2R`.
`UnitRealSum` first applies the affine real-sum section in each p,c block; its linear part is
an orthogonal projection, so the same bound applies with additional directed rounding.
At fixed h, `(a,h,h tensor a)` has linear norm `sqrt(1+||h||^2)<=1+sum_j |h_j|` over the real
coordinates. This supplies the enclosed conditional-feature port, including complex phase.

[established-bounded; implemented-exact] The source conversion used by normal material is
now also the common point-to-enclosure conversion. Coordinate restriction, wave-source
formation, fixed-condition feature formation and oriented differences compose these same
resident operands. No host numerical readout occurs in observation formation. Original
families and joins retain distinctions finer than the moment enclosure.

## Dependent material and the joining correction

[established-bounded; implemented-exact] An empirical operation in the dependent programme
retains its original Base or Programme producing frame and observed enclosure. Every evaluation
at theta recomputes that source-conditioned update. Existing locally formed members hold their
updated normal component; a normal-only change to an otherwise immutable base member is retained
as that component's difference. A later member action reads this returned material. The display
parameter does not become a common material matrix.

[counterexample; computational-witness] The two-member test exposed an incorrect intermediate
construction. A later root parameter restricted the source at its own cut, but an earlier
saved prediction still exposed its unrestricted source marginal. Updating another member
from that marginal produced the same B for two different source assignments. A one-member
test had not separated this error because its pre-existing parameter-dependent material
already differed.

[established-bounded; implemented-exact] The repair uses the existing
`read_retained_word_pullback`: transport the current parameter constraint backward through
the complete saved word, then use its jointly supported original source and original predicted
target. This restriction comes from the retained parameter/continuation constraints, before
the new y enters moment formation. The receipt retains the joins; immutable supported families
are shared through their existing owner. Tests now cover an earlier Base prediction on another
member, a later Programme prediction, two different parameter assignments, subsequent generation
and rest/remount with a further prediction pending.

[proved-derived] A concrete first return in that test has original p=1, h=1, observed y=4,
and parameter-dependent c in `{1,2}`. Its feature and cross-source rows are

| c | f=(a,h,h tensor a) | B increment |
|---|---|---|
| 1 | `(0,1,1,1,0,1,1)` | `(0,3,3,3,0,3,3)` |
| 2 | `(1,2,1,1,1,2,1)` | `(2,4,2,2,2,4,2)` |

With the unit prior and no earlier observations on this member, the corresponding normal-reference
minimizers are `f/2` and `f/7`, respectively. The runtime retains its dyadic realization and
error bounds. These are different inferred local operators arising from the same update law
on different compatible sources, rather than a member-label switch supplying coefficients.

## Chronology, persistence and costs

[established-bounded; implemented-exact] Wave and material clocks remain distinct. Affine
rest v10 records when the held current's map predates the current neighborhood material;
the decoder preserves that map while deriving new admissions from current standing. Existing
formats remain emitted when this extra distinction is absent. Dependent rest v5 carries
empirical operations and counts only wave-moving operations when interpreting prediction
clocks; it continues reading versions 1–4. Pending source/map joins retain their existing
validation. These changes serialize an actual source-cut distinction, not a history archive.

[established-bounded; measured] The real-source consumer uses one constitutive junction with
two caused internal contacts, giving five complex coordinates: three outgoing boundary ports
and two internal currents. After eight field transitions formed the initial model, a ninth
observation enters `NativeCoupledBody::observe`. The test checks every cross-source matrix
increment, the full signed discrepancy bound, unchanged held state, immediate rest/remount
and the next forecast against an independent contraction of the returned M.

| Receiver/cost | Observed value |
|---|---|
| Field source cut | 13 |
| Held wave epoch after observation | 1 |
| Local normal observation count | 9 |
| One warm empirical return, including staging/publication | 33417 microseconds |
| One two-step joint forecast delivery | 136024 microseconds |
| Source-feature radius | `159/16384` |
| Target-increment radius | `123/16384` |
| Prediction-discrepancy radius | `935/65536` |

[established-bounded; measured] These are individual `Instant` elapsed observations, not
sustained-throughput estimates. Hardware inspection returned AMD Ryzen 9 7900X, 24 logical
CPUs, and NVIDIA GeForce RTX 4080 SUPER with 16376 MiB reported VRAM. The host build used Cargo's
debug test profile; CUDA laws compiled with optimization for compute_89. Initial driver
compilation is separate from the warm timings above. No power measurement was made.

| Final relevant verification | Result |
|---|---|
| Engine `material_transport::normal::` ignored CUDA suite | 127 passed; 33.91 s test execution. |
| HNN `native::coupled_wave::` ignored CUDA suite | 11 passed; 7.78 s test execution, 55.61 s build. |
| HNN public examples Cargo check | Passed; 22.73 s. |

[definition] Commands, numerical output and hardware observations are in
`.local/artifacts/2026-09-13-empirical-return/`. The seven enclosure tests and first observation
tests also have their earlier logs; their initial driver compilation time is not a warm
operation cost. The abandoned earlier enclosure draft remains under
`.local/recovery/2026-09-13-family-enclosure-draft/`; this cycle replaced it and retained its
failure record. Unrelated local sources and evidence were preserved.

## Returned dependency

[definition] This closes the observed-field binding identified by the previous return. The
next source construction must expose the already-retained `OperativeSections.map`, its bounds
and caused contact incidence alongside the current source. The field experiment so far fixes
material/contact population after preparation. A material-changing interval must carry its
changed action and mixed current/material terms into the same generation/observation owner.

[open] The dependent programme still evaluates its operation representation. Its empirical
returns now have a defined moment/source/clock law to encode. Replacing a repeated segment
requires the matching `E_next T=U E` and decoder relation for its parameter family, current
material and pending source joins. That encoding and broader contextual products remain in
the live roadmap; the returned field experiment does not discharge them.
