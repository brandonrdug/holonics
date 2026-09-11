# Coupled source fields react with complete arrivals

[project-postulate] This continues the active Athena goal from `1762ac71`. The next missing
join is an actual source interaction with the coupled current. More local observations alone
had not attached the previous wave to that local law's domain. This return reuses the existing
unit-admittance contact and passive source-union laws; it adds no alternate learner.

## The complete source reaction

[definition] An actual source pair `(p,c)` supplies `a=(c−p,c,p)` to its admitted local law at
the retained condition. Keep its complete prediction `η∈L(a,h)` and joined arrival family
`F={(c,c+η)}`. Let the offered joint be `x=(p,c)`. For nonempty `F=b+V`, with orthogonal
projections `P` onto V and `Q=I−P` in the declared unit-admittance realification, the existing
contact law gives

```math
y=P x+Q b,\qquad j_{\mathrm{in}}=Qb,\qquad
j_{\mathrm{return}}=Qx,\qquad y-x=Qb-Qx.
```

`ResidentConstitutiveReturn::read_contact` now exposes this already-used reaction for a general
affine return. It borrows the whole family. The realized point y is a new result of this declared
contact, not a cast of the family's particular solution or a claim that its compatible cause
is unique. `successor()` retains a compatibility guard; `actual_successor()` explicitly reads
the actual contact result without that assertion.

[proved-derived] The reaction lies in F and preserves `P y=P x`: `Qy=Qb` and `Py=Px` follow
from orthogonal projection identities. Replacing b by `b+v`, v in V, leaves Qb unchanged; changing
the generators without changing their span also changes nothing. Orthogonality gives the
complete two-port equality
`||x||²+||j_in||²=||y||²+||j_return||²`, by expanding x into Px+Qx and y into Px+Qb.
This is the declared current metric, not a physical-unit or force-identification claim.

[definition] Empty learned evidence preserves the actual offered x under the existing contact
law and returns the original outside-domain prediction. It supplies no assertion of a compatible
arrival. This is why the actual-result port and compatibility port differ. The original
prediction, including its full source remainder, is retained beside the joined family and
reaction. It must not be relabeled a learned zero difference.

## The same passive union acts on the whole held family

[definition] After that actual reaction, use the existing passive contact from
`HolonicOrientedSiteTransport.PassiveContact` and the
[source-union derivation](2026-09-10_SOURCE_PASSAGES_ACT_THROUGH_UNION_AND_PASSIVE_REFLECTION.md):

```math
d=x-y,\quad D=\lVert d\rVert^2+\left|\lVert y\rVert^2-\lVert x\rVert^2\right|,
\quad A=I-\frac{2dd^{\mathsf T}}D,\qquad G(q)=y+Aq.
```

At D=0 use A=I. The source union is the same joined expression `F(x,y,x+q)`; its x cancels
symbolically. In the empty-evidence case y=x, so the offered current still enters as `x+q`.
That identity source passage is actual source conduct with retained insufficiency, not a guessed
prediction from L. Conditional generation itself remains a separate partial family operation.

[proved-derived] A acts by one on the orthogonal complement of d and by
`1−2||d||²/D` along d, which lies in `[−1,1]`; hence the query map is non-expansive. For fixed
actual x,y the map is affine and total on q. Applying it to every member of the retained anchored
affine family therefore preserves its full image and original anchor support. No centre of that
family is supplied to a point-current port, and no new nearest-point solve is needed to establish
support after this total map. A simultaneous orthogonal change of source and receiver charts
transports P, A and the complete construction accordingly.

[definition] `resident/wave_relation/source.rs` and `constitutive_wave_source.cuh` retain the
actual source snapshot, original full prediction, joined arrival and actual reaction. They form
an exact homogeneous graph of G. It copies lambda and the original anchor and checks all input
pivots, establishing a total functional map. This source passage is distinct from the ordinary
conditional `(p,c)→(c,c+η)` join; `ConstitutiveImageReceiver` exposes the distinction.
`NormalWaveFamily` composes the source graph through the existing affine-image owner.

## One field, one continuing successor

[definition] `ResidentSourcePairs` prepares all adjacent pairs of the actual supplied section
on device, including its final pair. It invents neither an outside endpoint nor an observed
fitting target. `actuate_contact_section` stages the ordered source maps under one admitted
member/condition cut. Internal factors share one successor occurrence; the wave and neighborhood
publish once after the complete field returns. Failure leaves the continuing owner unchanged.
The optional callback reports completed internal factors, not numerical current or an admission
choice. A source row is not a universal model clock.

[definition] `NormalCoupledSourceActuation` retains the original field, its actual source pairs,
all complete local prediction fibres in order, and preceding/successor families. The last internal
source contact is named as such, not presented as the entire word. The continuing body retains
the composed current family and its last source evidence; it does not retain an ever-growing
source archive. No normal or local material receives a deposit during this unpaired operation,
and the retained condition is unchanged. Existing observed-source reception remains separate.

[definition] Relation rest v3 stores source evidence as exact separate operands. Legacy v1/v2
conditional maps remain readable. Cold ingress checks source-plane/receiver shape, the actual
offered joint, prediction and arrival scopes, total input rank and anchor preservation. Remount
reconstructs the joined arrival and unit-admittance reaction from the original prediction and
source, then recomputes the passive graph and compares it. Coupled remount additionally re-derives
the original prediction from the actual restored local law and condition. Metadata flags alone
supply none of those correspondences.

[definition] The public-owner `conversation_coupled actuate` assay reads the prepared development
source and records part progress alongside the complete model and delivery cursor. It advances
part progress immediately when a field commits, before optional cold observation, so an observer
failure cannot cause that committed part to be delivered again on resume. Full prediction
witnesses and their dispositions are exterior evidence; they do not choose native conduct.

## Verification and live position

[established-bounded; implemented-exact; computational-witness] The source controls return exact
source motion, retained plural and outside-domain predictions, an unchanged original anchor,
unchanged material, and complete rest/remount. A three-factor field matches explicit ordered
composition while publishing once; a fresh process continues it to byte-identical complete rest.
The contact covaries under a common source/receiver quarter turn. Altering a stored returned-normal
current while preserving the endpoints is rejected by native reconstruction on remount.

[established-bounded; process-audit] The final scoped runs returned 53 wave controls, eight affine/
condition-contact controls and three relation-rest controls. The subsequent admission barrier
also passes all twelve coupled controls. Logs are `.local/scratch/athena-source-final-wave-tests.log`,
`athena-source-final-contact-tests.log`, `athena-source-final-rest-tests.log` and
`athena-source-image-admission-tests.log`. The public `conversation_coupled` example builds.
No Lean or presentation source changed.

[counterexample; computational-witness] The first prepared sequence-66 attempt contains 200
source scalars. The initial compatibility-only source-map gate refused an outside-domain learned
arrival, leaving epoch ten. That gate was too strong for source actuation: the existing contact
law had retained the actual offered current. The repaired source union carries it and the full
unresolved prediction explicitly. The first private run is retained at
`.local/athena-coupled-source-2026-09-11-actuated-66`; its post-load operation/checkpoint interval
was 307,537 milliseconds, with no field published.

[definition] The unit-admittance Gram construction now skips exactly zero generator coefficients
and padded rows. It computes the same per-coordinate sums in the same order. This removes dense
cubic work on zero entries without a numerical tolerance, source-label mask or changed projection.
All nonzero coefficients and the full affine span remain operative.

[definition] Source maps are total functional graphs, so their exact affine image is
`G(a+span(V))=G(a)+span(A V)`. The specialized image validates its immutable source/family first,
then maps the particular state and every generator in separate work rows, and finally reduces
the resulting direction basis. Workers have disjoint query/output rows; only their carrier-failure
flag is combined. Invalid carriers are rejected before that parallel work. The final source image
and field successor are published only after all dependent stages return. General relation image
remains available for partial/plural conditional maps and as an independent comparison.

[established-bounded; computational-witness] Complete affine-family comparisons agree with the
general relation solver, including a held family with free directions. The real sequence-66
field completes with 200 source scalars, 199 internal passages, 197 plural predictions and two
outside-domain predictions. It advances the owner once, from epoch ten to eleven, with no
intermediate numerical readout. Full predictions, source cursor and part progress remain in
its private checkpoint. The [general-image receipt](2026-09-11_coupled_source_field_receipts/general-image.json)
and [total-image receipt](2026-09-11_coupled_source_field_receipts/total-image.json) retain the run scopes.

[established-bounded; measured] The general image took 667,783 milliseconds for the native field;
the total-image specialization took 273,513 milliseconds. Peak resident storage decreased from
512,347,588 to 385,550,036 octets. Cold prediction observation took 21,889 and 22,714 milliseconds,
respectively. These are operation wall times including host orchestration, not isolated device
throughput or calibrated power. The total-image timing precedes the added validation barrier. The
[final validation-first run](2026-09-11_coupled_source_field_receipts/validated-image.json) takes
287,069 milliseconds for the field and 22,854 milliseconds for cold prediction observation;
peak residency is 385,550,120 octets. It retains the same 197 plural and two outside-domain
predictions, at source rows 36 and 37. The latter remain complete original obstructions.

[established-bounded; computational-witness] The
[complete comparison](2026-09-11_coupled_source_field_receipts/total-image-equivalence.json) checks
all other persisted components and the source/delivery witnesses byte-for-byte. The current's
340 direction vectors agree exactly. The two affine origins differ in 82 coordinates; their
full difference is an explicitly reconstructed linear combination of those same directions.
The original anchor ball is identical, so the constrained current families agree. Neither
origin was installed as the actual current. This proves the stated finite representation
comparison; it is not a claim that different arithmetic charts have identical future refusal
or performance boundaries.

[established-bounded; computational-witness] The
[final full comparison](2026-09-11_coupled_source_field_receipts/validated-image-equivalence.json)
returns the same constrained family after validation was separated from parallel image work.
The [material comparison](2026-09-11_coupled_source_field_receipts/material-invariance.json)
checks the complete normal bank, condition, all local law bytes and condition evidence against
the pre-actuation checkpoint; all remain unchanged. Wave epoch advances 10→11 and neighborhood
epoch 0→1. The separate [fresh-process receiver](2026-09-11_coupled_source_field_receipts/current-receiver.json)
returns `Supported` with zero anchor displacement and no anchor-independent free coordinate.
Anchor-ball uncertainty remains; the projected joint is not installed as actual current.

[conditional] In an assay whose local rows all have unit source sums and h=(1,0), the row-span
invariant `sum Re(source.current)=Re(h)`, `Im(h)=0` persists. For a subsequent fixed unit source,
its compatible condition is therefore h=(1,0), or the preimage is empty. The existing inverse
contact preserves actual h=(1,0) in both cases; forming another such row preserves the invariant.
This is a limitation of that declared fixed-condition/source assay, not of every neighborhood.
Further unit-source exposure must not be described as condition development. Actual conditional
source/receiver comparisons and their condition-transport scope remain part of the pending join.

[proved-derived] For a fixed linear relation `L⊆X⊕Y`, every nonempty source fibre is
`L_x=η₀+V`, where `V={η | (0,η)∈L}`. Subtracting two elements over the same x proves one
inclusion; adding `(0,v)∈L` to `(x,η₀)∈L` proves the converse. V is independent of x.
Thus the unit-metric vertical projector can be reused at this material scope, while each
particular response and source remains distinct. For the joined arrival its direction space
is `0⊕V`.

[established-bounded; computational-witness] The
[vertical-standing check](2026-09-11_coupled_source_field_receipts/vertical-standing.json) compares
all 197 nonempty predictions from the real field: their complete target direction tables agree
at local material cut 9,254. This identifies a concrete reuse opportunity, not a claim that the
source occurrences or predictions are identical.

[open] Coupled emission/re-entry, the continuing conversation session, producing-family
observations, broader formation/reuse and useful-model evaluation remain. Reusing the fixed law's unchanged vertical projector across a source field is
also a concrete remaining cost reduction. This source interaction is not a conversation-quality
result or a completion claim for Athena-alpha.
