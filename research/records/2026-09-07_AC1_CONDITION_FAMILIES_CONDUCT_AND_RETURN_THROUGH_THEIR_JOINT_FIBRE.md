# AC1: condition families conduct and return through their joint fibre

[definition] Parent `d3820ac3`. The existing condition Preimage Fibre now transports through the
learned action as a whole family. Its supported condition domain, supported output and joint
condition/output fibre remain distinct. A later actual return refines that same joint family.
The result extends the native conditional construction; it does not attain Athena-alpha.

## Joint transport

[definition] For the represented relation `R`, fixed source `s`, and nonempty condition family
`F = c0 + span{v_j}`, the transported object is

```text
J(s,F;R) = { (c,y) | c in F and (Phi(s,c),y) in R }.
```

Its condition projection is the supported domain; its output projection is the supported image.
Those projections do not replace `J`: independently varying their coordinates would invent
condition/output combinations that the joint relation never admitted.

[proved-derived] Fixing `s` makes `Phi(s,c)=s ⊕ c ⊕ (c ⊗ s)` affine in `c`. Let `P_R` be the
existing exact echelon residual map, with kernel `R`. Put

```text
v0 = (Phi(s,c0),0),
v_j = (0,v_j,v_j ⊗ s,0),
w_k = (0,0,0,e_k).
```

The native graph spans `(P_R(v_j),v_j,0)` and `(P_R(w_k),0,e_k)`. Querying it at `-P_R(v0)`
returns the compatible condition variations and outputs; adding `c0` restores absolute condition
coordinates. This follows by linearity and retains the original relation's vertical directions.
It uses the existing `fibre_query` and `fibre_stage`, not a second solver or condition chooser.

## Domain coverage is part of the return

[proved-derived] The supported condition domain `D = pr_c J` is a subset of `F` by construction.
For nonempty `D = d0 + V_D`, equality holds exactly when `c0-d0` belongs to `V_D` and every
direction of `F` belongs to `V_D`. These finite linear checks establish coverage of the whole
affine family, without enumerating its points.

[definition] `ConditionCoverage` distinguishes complete coverage, a proper supported subset,
no supported condition, and an empty input family. A partial result carries an actual condition
witness and its complete nonzero residual in the projected domain chart. The original family
remains shared immutable standing. The joint fibre describes the supported subset, so together
they retain the full unsupported complement; the witness is not a substitute for that family.

[definition] A point-current port and an unqualified differential receiver are valid only with
complete condition coverage. A constant supported output on a strict subset does not become a
claim about the whole input family. Native guards enforce this; cold inspection still exposes
the supported output and its domain. Conversely, complete coverage can return a unique output
even when the condition remains plural. No particular condition is selected to get that result.

## A later return restricts the producing relation

[definition] `ResidentConditionImage::receive` restricts a complete-domain joint family by an
actual observed output. If its affine origin is `(c0,y0)` and its directions are `(dc_j,dy_j)`,
the kernel forms the homogeneous relation spanned by `(1,y0,c0)` and `(0,dy_j,dc_j)`, then queries
it at `(1,y_observed)`. The resulting condition Preimage Fibre is exactly

```text
{ c | (c,y_observed) belongs to J }.
```

The leading one pins the affine origin coefficient. A plural result keeps its full free span;
an incompatible observation returns an outside-represented-relation residual. The old family
and image are unchanged. Partial-domain images retain their obstruction rather than silently
discarding unsupported conditions during this unqualified refinement.

[established-bounded; source-inspected] Reception uses the immutable joint relation that produced
the earlier image, even if the action has subsequently received more deposits. It does not use
the changed action to rewrite a past return. The original condition is shared through an immutable
`Rc`; no continuing ecology is cloned, restored or rolled back.

## Native owners and public boundary

[established-bounded; source-inspected] `ResidentConstitutiveFibre::read_condition_image` returns
`ResidentConditionImage` from `constitutive_fibre/resident/condition_image.rs`. The return exposes
the original condition family, joint/domain/output inspection, guarded current and differential
ports, and subsequent reception. The existing `ResidentConditionPreimage` remains the successor
condition type; repeated refinement does not require a new family of model containers.

[established-bounded; source-inspected] `resident_section/surface_condition.rs` owns the new
bindings, and `kernels/constitutive_condition_image.cuh` implements joint construction, exact
projection, coverage and reception. Native arithmetic and all coverage decisions remain on the
device. The ordinary differential kernel accepts an optional coverage guard; its unguarded
existing receivers retain their prior numerical law. Source charts and relation cuts retain
their declared roles, with no invented physical source occurrence.

[definition] For original relation width `W`, condition width `C`, and output width `Y`, joint
construction uses graph width `W+C+Y` and `W+2*(W+C+Y)` wide scratch values. Reception uses
`1+Y+C` graph coordinates and twice that many wide scratch values. These are current dense local
representations admitted against the actual device aperture, not intrinsic semantic dimensions
or general performance bounds. The original relation and condition family survive numerical
refusal; unsuccessful derived outputs are not published.

## Returned evidence

[established-bounded; measured] The original regression scope plus seven image controls passed
**107 tests**, zero failures, in 20.83 seconds (`/tmp/athena-condition-image-all-tests.log`). A
subsequent translated-domain control passed separately
(`/tmp/athena-condition-image-affine-origin-test.log`); it verifies the branch where the original
affine origin itself is unsupported. The public text-codec control passed with the new optional
native coverage guard (`/tmp/athena-condition-image-sdk-test.log`).

[established-bounded; measured] The controls include:

- a wholly free condition family yielding a fixed zero current which enters another native operation;
- a nontrivial fixed differential of a plural output family;
- correlated joint directions rather than the Cartesian product of separate images;
- strict, empty and translated supported domains, with guarded point use and reception;
- rational images and repeated refinement;
- an earlier joint family retaining its meaning after a later model deposit; and
- foreign surface, invalid denominator and word overflow preserving the original action/family.

[established-bounded; measured] The public `native_conditioned_phase` example now records the
whole cycle in [return-family-cycle.json](2026-09-07_conditional_phase/return-family-cycle.json).
It begins with free conditions, obtains a fixed zero output without choosing a condition, then
reads a joint family for source `2+i`. The native world supplies a later response under hidden
condition `(-7+24i)/25`. Reception refines the family; a later source `3-2i` produces the prediction
`(27+86i)/25`, agreeing with the subsequent actual native return. The inferred family was not
decoded and remounted to make that prediction.

[established-bounded; measured] Image construction and refinement each performed one native deed,
zero numerical section reads/egress, and zero ingress after their operands were mounted. The later
image plus a native current consumer performed two deeds, zero numerical section reads/egress,
and four bytes of predecessor-edge metadata ingress. The example's own whole-run clock read
0.130 seconds. These are small native phase-study costs, not language, audio or power measurements.
The report remains research evidence, not an independently executable model checkpoint.

## Integration boundary

[project-postulate] These are whole-family evidence receivers. Their unqualified-use guards must
not become a universal demand that a developing body identify every external condition before
it can generate its own actual current. A compatible-condition family and the realized current
of the model are different objects. Do not manufacture the latter by treating an arbitrary
affine particular solution as an identified external cause.

[definition] The next binding is an actual retained condition current and its response to an
inferred family through the existing native current/contact discipline. It must keep the prior
current in undetermined directions, carry the returned difference, and publish one successor.
The family remains evidence about compatible conditions. This distinguishes native generative
standing from a catalogue of possible answers or a proof that every possible source agrees.
The concrete contact law and its frame/metric are owed before implementation is graded.

[open] Bind that continuing native owner to the actual conversation material and inspect its
responses. The saved text model still has the earlier failed outputs; this turn did not repeat
unchanged corpus exposure or claim a language improvement. The full AC0–AC5 product remains open.
Mac work can port the image/reception kernels through its existing wide arithmetic and elimination
owners; no Apple execution, Lean pipeline or retired database use is introduced here.
