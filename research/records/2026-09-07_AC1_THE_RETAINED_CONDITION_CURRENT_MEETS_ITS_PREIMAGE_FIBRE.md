# The retained condition current meets its Preimage Fibre

[definition] This AC1 construction follows the
[joint condition-family return](2026-09-07_AC1_CONDITION_FAMILIES_CONDUCT_AND_RETURN_THROUGH_THEIR_JOINT_FIBRE.md).
The compatible conditions supplied by limited observations and the model's actual current have
different roles. The contact below uses both. It does not identify the unknown external cause,
require a singleton fibre, or install the affine solver's particular solution as model standing.

## Contact, metric and derivation

[definition] Let the condition chart be the realification of finitely many complex ports, with
unit admittance on each real and imaginary coordinate. Let its nonempty affine condition family
be `F=a+V`, and let `h` be actual retained current. Write `P` for the orthogonal projection onto
`V`, `Q=I-P`, and `q=Qa`. The declared two-port contact is

```text
incoming ports:       (h, q)
successor current:    h' = Ph + q
returned normal:     r  = Qh
oriented difference: d  = h' - h = q - r.
```

[proved-derived] This is independent of the origin and basis used to represent `F`, belongs to
`F`, retains the unconstrained part of `h`, and balances the declared quadratic form exactly.
Here is the complete finite-dimensional derivation. Choose independent rational row vectors
spanning `V`, collect them in `B`, and set `G=BBᵀ`. For nonzero column `z`,
`zᵀGz=||Bᵀz||²>0` by row independence, so `G` is invertible and its inverse is rational.
Set `P=BᵀG⁻¹B`. Direct multiplication gives `Pᵀ=P`, `P²=P`, and `range(P)=V`.
Consequently `Q²=Q`, `PQ=QP=0`, `ker(Q)=V`, and the ranges of `P,Q` are orthogonal.
The zero-dimensional case uses `P=0`. These equations characterize the projection by its range,
so replacing the basis does not change it. Replacing `a` by `a+v`, `v∈V`, leaves `Qa` unchanged.
Moreover `h'=a+P(h-a)∈a+V`, and `Ph'=Ph`. Orthogonality gives

```text
||h||² + ||q||² = ||Ph||² + ||Qh||² + ||q||²
                 = ||h'||² + ||r||².
```

Subtracting `h` from `h'` gives the displayed full difference. If `h∈F`, that difference is zero.
If `V` is the full chart, `P=I`, hence the current continues unchanged despite wholly free
condition evidence. If `V=0`, the constrained current is exchanged in full.

[proved-derived] This composes the equal-admittance junction in
[`dimensional_wave.rs`](../../crates/holonic-engine/src/dimensional_wave.rs) and its native
phase-field realization in `exact_resident_section.cu`. On the normal subspace, two unit ports
arrive with `Qh,q`; the existing law gives junction potential `Qh+q` and departing currents
`q,Qh`. The tangential subspace keeps `Ph`. In block form the complete two-port operator is
`S=[[P,Q],[Q,P]]`; symmetry and the projector identities give `SᵀS=I`. For an orthogonal change
of chart `U`, the transformed projection is `UPUᵀ`, so applying the contact before or after
transport gives the same currents. A general coordinate change owes the corresponding metric.
No claim of a calibrated physical energy, force, acoustic medium or general quantum dynamics
follows from this dimensionless quadratic balance alone.

[definition] An empty compatible family returns `OutsideRepresentedRelation`, retains its
original evidence, and leaves the actual current unchanged. This disposition does not pretend
the current satisfies an inconsistent constraint, nor prevent it from entering a subsequent
native operation. Its contact count counts completed encounters, including an empty family.

## Native realization and ownership

[definition] `ResidentConstitutiveFibre::retain_condition_current` founds a
`ResidentConditionCurrent` from an explicitly supplied resident current and
`ConditionContactMetric::UnitAdmittanceRealification`. `contact` receives a
`ResidentConditionPreimage`. The source/condition chart must agree; numerical shape is not
semantic identity or an automatic chart-change receipt. Callers owe the actual coordinate
correspondence. This interface does not yet perform a moving-frame rechart.

[definition] The existing exact `fibre_stage`/`fibre_query` calculus constructs the projection.
With the direction rows arranged as `A`, it stages `(A v_i,v_i)` in a `2C`-coordinate relation
and queries it at `Ah` and `Aa`. Since `ker(A)=V⊥`, its restriction to `V` is injective; every
`Ax` is the image of precisely one point of `V`. The answers therefore are `Ph` and `Pa`, even
when zero rows pad the direction chart. This is the existing rational elimination owner; no
host projection, second numerical solver, random selection or float supplies the current.

[definition] The CUDA owner is
[`constitutive_condition_contact.cuh`](../../crates/holonic-engine/kernels/constitutive_condition_contact.cuh),
bound through `resident_section/surface_condition.rs` and packaged in
[`resident/condition_contact.rs`](../../crates/holonic-engine/src/native_ecology/constitutive_fibre/resident/condition_contact.rs).
The contact uses `9C` native wide scratch values and a temporary square relation of width `2C`.
Its output retains five `C`-coordinate currents—predecessor, successor, incoming normal,
returned normal, difference—with a common positive denominator and disposition. The original
family remains an immutable shared return. Each current has a resident consumption port.

[definition] The actual owner is not cloneable. Only immutable sections are shared with the
contact receipt. A complete new return is staged and checked before its owner publishes the
successor. Arithmetic refusal leaves the existing current and contact count intact. Receipts
do not recursively retain every previous ecology or require raw-state archival for learning.
The full affine evidence remains available separately from the actual generative current.

## Verification and integration position

[established-bounded; measured] All six new CUDA controls pass. They cover an oblique affine
family; a quarter-turn of both family and current; two complex condition ports; an altered affine
origin and direction scale for the same family; free/empty/unique condition evidence; repeated
contact and immutable old returns; invalid denominators, foreign surfaces and late arithmetic
refusal. They check the full difference, retained tangential current and exact quadratic balance.
The subsequent complete constitutive scope passes **114 tests**, zero failures, in **24.58 s**.
Commands and logs:

```text
cargo test -p holonic-engine --lib native_ecology::constitutive_fibre::resident::condition_contact -- --ignored --test-threads=1
/tmp/athena-condition-contact-tests.log

target/debug/deps/holonic_engine-6ae3d245ea632305 native_ecology::constitutive_fibre --ignored --test-threads=1
/tmp/athena-condition-contact-all-tests.log

cargo build -p holonic-engine --example native_conditioned_phase
target/debug/examples/native_conditioned_phase research/records/2026-09-07_conditional_phase/return-retained-contact.json
```

[established-bounded; measured] The updated public example returns
[return-retained-contact.json](2026-09-07_conditional_phase/return-retained-contact.json).
The existing learned action generates initial actual condition current `(3+4i)/5`. Free evidence
preserves it, and source `2+i` generates `(2+11i)/5` before the world's unknown condition is
observed. The native phase-field world then returns `(-38+41i)/25`; reception of that actual
output refines the producing joint family. Contact changes the retained current to
`(-7+24i)/25`, returning old normal current `(3+4i)/5` and difference `(-22+4i)/25`.
On later source `3-2i`, actual model generation gives `(27+86i)/25`, exactly matching the
subsequent native world return. Both recorded contacts satisfy the quadratic balance above.
The driver mounts interventions and observes returns; it contains no local learner or projection.

[counterexample; computational-witness] The first generated and observed currents above are
different but both have squared norm `5`. Their conditions also both have squared norm `1`.
These particular scalar receivers therefore cannot distinguish the change that the full
oriented current carries. The native contact retains that difference.

[established-bounded; measured] The initial native generation, retention, free contact and
next generation perform four deeds, zero numerical section reads/egress and eight bytes of
predecessor-edge metadata ingress. The contact after observation performs one deed with zero
numerical reads/egress and zero ingress. The later joint image plus both current consumers perform
three deeds, zero numerical reads/egress and eight bytes of predecessor metadata ingress.
The example's whole-run clock reads **0.149606481 s**, with 16 learned-action occurrences.
This is a small native phase-study measurement, not conversation throughput, acoustic performance
or power. The report is evidence rather than an independently executable model checkpoint.

[open] The continuing conversation owner still needs the actual source/condition incidence,
producing-law chronology, reception and codec attachment composed with this current. General
nonlinear generator recovery and useful conversation are not established by this affine contact.
The failed saved text models remain evidence; no unchanged corpus run is repeated as a substitute
for that attachment. Athena-alpha and the full AC0–AC5 goal remain unfinished.

[definition] The Mac extension is the same two contact kernels over its own wide layout and
existing exact elimination helpers, plus the common Rust wrapper. The contact scratch is
`9*C*sizeof(W)` on that target. Port the declared metric, full return and staged publication;
do not copy CUDA's wide byte size. Desktop execution does not establish Metal parity.
