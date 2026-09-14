# Boundary and internal currents feed joint HNN prediction

[definition] This construction follows the live boundary/interior assembly contract after
Brandon's refinement of context as a situated boundary over intersecting event histories.
The active goal supplies continuous turns; roadmap, blueprint and direct rulings govern the
work. The local source below is a finite passive junction and its retained internal currents.
Its normalized unit-admittance chart is explicit; this record makes no measured electrical
power or general conversation claim.

## Source and consuming operation

[established-bounded; source-inspected] The operative field already retained its outgoing
root current o, full internal population b, contact map and uncertainty. Cold inspections
could display these operands, but did not provide a productive direct-normal input. The new
`NativeConstitutiveField::read_current_source` packages `(o,b)` on device and returns an
immutable `NativeFieldCurrentSource`. With n root nodes and k actual contacts, it exposes
`3n+k` complex coordinates. k is the represented contact population, not effective modal rank.

[definition] This source retains all b coordinates, not only the aggregate D b seen by the
present boundary. The source object keeps its field owner, event cut, birth incidences,
original outgoing report and producing operative sections. Reading it does not advance or
clone the field. A declared joint outer ball uses radius `r_o+r_b`; the original separate
carriers remain source witnesses. The ball does not assert independence or identify the
complete finer physical preimage. The normal consumer operates at this stated outer scope.

[established-bounded; source-inspected] `field_current_source.cuh` and its resident port
perform this packing. `ResidentNormalEnclosureView` now supplies device-only join, oriented
difference and owned-copy receivers. A source subtracted from that same immutable source
cancels its uncertainty as well as its centre. Distinct sources retain the sum bound.
`difference_source` applies the existing `(c-p,c,p)` wave lift to a paired enclosure.
`into_joint_difference_wave` uses the existing JointEnclosure seed and rest representation;
it supplies no second wave engine or new persistent word format.

[definition] In the consuming source task, two caused contacts are formed in a one-node
junction, then material, frame and contact population remain fixed while zero external drive
continues the field. The measured source has five complex coordinates: three outgoing ports
and two internal currents. Consecutive full states provide

```text
a_t=(q_t-q_(t-1),q_t,q_(t-1)),
y_t=q_(t+1)-q_t.
```

Eight actual field returns feed the existing normal moment law. Both a_t and y_t retain
their enclosures. The inferred stored M then supplies `q_next=q+M a` through the existing
generator neighborhood and `NativeCoupledBody`. The unit condition is an unused coordinate
of this declared Wave specialization: the participating causal state is the actual `(o,b)`
source, not a classification attached to h. General changing-material/source formation remains
part of the wider programme; this source task states its fixed-material interval.

## Enclosed observations and normal geometry

[established-bounded; source-inspected] `ResidentNormalMaterial::receive` now accepts the
existing `ResidentNormalInput` on its observed port as well as its source port. Point callers
keep their behavior. Enclosed targets remain wide centre/radius data at the declared grain.
The direct kernel invokes the existing observation-frame, moment-increment and normal-fit
owners. No second fitter or host semantic update is introduced.

[proved-derived] For the existing bounded moment convention, centres x,y with radii ex,ey
and outward norm bounds nx,ny contribute errors

```text
H_error += (2 nx+ex) ex,
B_error += ny ex+nx ey+ex ey,
Y_energy = ||y||²,
Y_energy_error += (2 ny+ey) ey.
```

These bounds do not require x and y errors to be independent. They are retained with the
oriented coordinates and source/target operands. The coefficient action is stored dyadic M;
its numerical normal-reference certificate is a separate receiver. Neither certificate is
an empirical guarantee for every unseen physical trajectory.

[established-bounded; source-inspected] Review repaired two defects in the first delegated
target patch: the wide target was being copied into a narrow point packet, and the radius
was overwritten with zero before the increment. The final path passes the original wide
target ball into the common observation owner. The regression uses grain 72, with both
coordinates and a radius beyond i64, and verifies exact error increments. A zero-radius
target is compared against the established point path.

## Applied relation and direct functional pullback

[established-bounded; source-inspected] A normal Wave material acts on the already-declared
a=(c-p,c,p) source. Its graph in the neighborhood's larger bilinear chart therefore has zero
condition and mixed coefficients. The existing applied-graph kernel now distinguishes stored
source width from graph source width. Generic feature material keeps its existing full
bilinear binding. Staged updates follow the material's declared source chart; rest validation
retains this distinction and counts action construction rows separately from observations.

[proved-derived] If the retained relation L is the graph of a total single-valued map A, the
fixed-condition wave pullback is the graph of direct application of A to its source embedding.
The map takes `(lambda,anchor,p,c)` to `(lambda,anchor,c,c+eta)` with the existing lambda,
source/condition products and receiver rechart. It can be constructed one source-axis row at
a time. A residual-kernel elimination gives the same graph but is unnecessary in this case.
Partial domains and vertical fibres continue to require the full relational construction.

[established-bounded; source-inspected] The initial field consumer exposed an i64 carrier
refusal in that unnecessary residual/nullspace graph. `constitutive_wave_relation.cuh` now
recognizes total single-valued echelon material by its complete source pivots and absent
vertical pivots, applies the existing native query, and builds the exact wave graph directly.
The supplied function, input precision and source family are unchanged. The original kernel
path remains for partial and plural laws. This is a construction repair, not a raised bound.

[proved-derived] The same simplification applies to an affine source F=x0+span(V): when a
single-valued relation carries x0 and every v in V, its complete joined image is
`(x0,A x0)+span{(v,A v):v in V}`. Domain membership of the origin and generators establishes
coverage of F. The native image kernel checks these conditions, retains an equivalent residual
graph/RHS and maps every generator. Otherwise it uses the original general relation image.
`Mathematics/DependentConstitutiveReturn.lean` retains the shared-parameter word and affine
receiver-coordinate laws; this optimization realizes the same joint, not independent marginals.

## Verification and next dependency

[established-bounded; measured] The five focused source and enclosure tests passed together
in 1.26 s warm execution before the functional-pullback change. They include an aggregate-dark
source with nonzero internal currents, snapshot stability, exact self-cancellation and the
wide observed-target error convention. The first cold device load took about 200 s under
supervision, separately from compilation and ordinary test execution.

[established-bounded; measured] The consuming HNN test passed after the functional pullback
and image repairs. It independently contracts every inferred complex coefficient, compares
the joint forecast with sequential conduct, and remounts the actual body. The full warm test
took 0.69 s; one two-future-state delivery with full joint inspection took 141217 microseconds.
Those are one-run observations, not steady-state throughput or physical-time rates.

[established-bounded; measured] The subsequent field comparison retained these signed
`prediction minus actual numerical centre` differences, in boundary-then-internal order:

| Coordinate | Real difference | Imaginary difference |
|---|---|---|
| Boundary 0 | 319757/1073741824 | 347559/2147483648 |
| Boundary 1 | -1503077/2147483648 | 2015925/4294967296 |
| Boundary 2 | -1246913/4294967296 | 425987/536870912 |
| Internal 0 | -2417763/4294967296 | 147919/2147483648 |
| Internal 1 | -705711/2147483648 | 13997/33554432 |

The paired source radius was 159/32768 and the subsequent actual-state enclosure radius was
87/32768. The comparison uses declared numerical receivers; it does not identify the unknown
physical current with its centre or prove a generalization bound from one later observation.

[established-bounded; measured] Final related regressions passed: 169 engine tests in 54.09 s
and 21 HNN/workshop tests in 11.58 s, after a 36.52 s test-profile build. They cover normal
formation, conditional/affine images, partial and plural sources, original pending returns,
coupled execution and persistence. The public HNN example Cargo check also passed. Formal
source/imports did not change in this cycle. Relevant logs are retained under
`.local/artifacts/2026-09-13-boundary-current/`.

```sh
cargo test -p holonic-engine -p holonics-hna --lib -- --ignored --test-threads=1 native_ecology::constitutive_fibre::resident:: native_ecology::constitutive_fibre::field::material_transport::normal:: junction::operative::source::tests native::coupled_wave::tests native::mathematical::tests
cargo check -p holonics-hna --examples
```

[definition] The mathematical body's rest carries its admitted outer source and generator;
it does not claim to serialize the entire source field or its finer forensic decoder. The
application retains the field/model clock correspondence. Original source witnesses remain
in the field source objects when that finer scope is requested.

[definition] The returned source/current binding feeds the wider encoding and formative
work. Repeated execution still needs its actual factor/recurrence closure, including live
pending comparisons. A changed contact map or material must enter the admitted source/action
family and its interior return; the fixed interval above does not discharge that extension.
The dynamic reflection defect remains the corresponding closure equation.

[definition] The next observed-field consumer has a concrete distinction to preserve: the
fitted point graph specifies this forecast's action; a later empirical observation carries
`delta=y-M a` and its own bounds. The normal owner now accepts enclosed source/target operands,
but coupled `incorporate` still accepts a point and invokes condition compatibility. The
condition-independent graph used in this fixed forecast does not supply a general admission
law for discrepant later field observations. Bind the original producing source, bounded
observation and discrepancy into formation without choosing unknown source coordinates from
the target or dropping either uncertainty. The older explicitly calibrated conditional-return
application retains its own demonstrated contract.

[historical] A delegated workspace `cargo fmt` modified 118 unrelated tracked files. Those
changes were preserved in `.local/recovery/2026-09-13-cargo-fmt-unrelated-cycle.diff` and the
unrelated files restored to their original HEAD contents. The worktree was clean apart from
the recorded unrelated untracked material before this cycle. The development guide now states
the targeted formatting command explicitly; all semantic edits stay in the consuming owners.
