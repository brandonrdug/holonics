# NCF2: the live rechart carries the relation and returns old sources through their frames

**Date:** 2026-09-05, local apparatus date. **Status:** NCF2 complete for fixed-node rational unit-phase gauges.
**Contract:** [native HNA](../../docs/plans/THE_NATIVE_HNA_FOUNDS_CONTEXTUAL_TRANSPORT_BEFORE_INHERITANCE.md).

## What changes, and what is retained

[established-bounded; source-inspected] `NativeConstitutiveEcology::rechart` transports the live
held phase, incoming incidence, initial-field presentation, learned relation and root-to-local
frame on CUDA. The relation is a span of paired current points: its source coordinates push
forward by the gauge while the root incoming/receiver chart stays fixed. A fresh echelon
representation is formed on-device. Staging succeeds before ownership transfers; the previous
live fields are never partially overwritten.

[established-bounded; source-inspected] Issued emissions remain immutable in their actual frames.
Every source retains a shared immutable resident frame and the constitutive material used when
it occurred. A later receiving edge applies the current-frame map composed with the old-frame
inverse on-device before comparison and formation. It does not reinterpret old coordinates or
require the source to be the latest emission. Historical incidence reads historical material.
Held-boundary composition now retains both incidence occurrences and the explicit middle-frame
transport; coordinate faces in different frames are not asserted equal.

[definition] `root_source_currents` is an exterior codec projection through the emitted source's
own immutable frame description, not a native learning step. The native current, state, relation
and old-source transport have already operated on-device. A frame ordinal is a scoped chart
position, never a source identity or global semantic key.

[established-bounded; source-inspected] `replace_incoming_transport` is a distinct physical
material intake. It changes one declared incoming incidence without rotating the held field,
relation or prior sources. It preserves prior material snapshots and returns its own change
receipt. No inference/training mode split or relevance classifier was introduced.

## Exact laws and controls

[proved-derived; formal-checked] `HolonicConstitutiveRechart.lean` supplies explicit rational
phase linear equivalences and inverses; the relation/source/held/issued/receiver component-wise
circulate--rebase square; and transport of an actual issued handle through the list-map law.
The old-to-current source-frame passage composes and agrees with transporting the original
source directly. Source-domain transport and equivalence of residual classes are proved as well.
These are ideal-law statements, not a kernel-verified proof of the CUDA implementation.

[historical; process-audit] The first native comparison incorrectly equated raw Gaussian source
remainders across charts. That assertion failed. The corrected, stronger control checks that
source minus remainder belongs to the actual source domain, that the obstruction class is
nonzero, and that the transported remainders agree modulo that domain. It also compares the
complete relation under the requested gauge. The kernel was not changed to force identical
remainder coordinates or to discard their distinction.

[established-bounded; measured] Six new CUDA controls and all sixteen preceding native controls
passed. They verify the requested gauge and composed gauge word, complete held field, native
frame and seed fields, full relation row space, continued development, and delayed original-frame
handles across two successive rechartings. Old emitted words and their historical incidence are
unchanged. Cross-frame held pullbacks return their nontrivial middle transport.

[established-bounded; measured] A gauge and its inverse recover the original held field, seed
presentation and relation without erasing chart history. A genuinely plural receiver remains
the same full affine fibre, with its later receiving comparison retained. Matched bodies can
emit equal faces while retaining different held successors. Zero paired currents permit unchanged
morphology while keeping their distinct native occurrences. Physical incidence change instead
changes the tested new current while preserving the old material and phase at the change boundary.

[established-bounded; measured] Invalid non-unit gauges refuse before native allocation. A valid
unit gauge outside the exact word aperture refuses without changing the held field, relation,
material, current frame or source handles. The two-node rechart transferred 192 input and 288
report-section bytes in one graph launch and one section read; the old relation did not cross
to the host. Failed attempts still have their actual apparatus costs.

[established-bounded; measured] Verification returned successfully:

```text
cargo test -p holonic-engine --lib native_ecology::constitutive_fibre -- --ignored --test-threads=1
lake build ElementaryHolonics.Computation.HolonicConstitutiveRechart
cargo test -p holonics-hna --lib
cargo check -p holonics-hna -p holonics-workbench
```

[established-bounded; measured] The native set returned 22 passing tests without fallback or
skips; the existing HNA library returned all 35 tests. The HNA/workbench dependency check passed.

## Remaining construction

[definition] NCF3 now exposes this same continuing owner through a usable native application
interface. Frame-qualified current, explicit receiving handles, open fibres and physical changes
must survive that interface; the application may not manufacture an internal learning rule.

[open] The admitted rechart family here has fixed nodes and rational unit phase gauges; it is
not every possible topology, nonlinear constitutive family or source-domain enlargement. Native
production adapters and an independently usable application remain NCF3. Durable model/session
artifacts, process-separated continuation (including frames, material history and source handles),
and integrated consumer-resource evidence remain NCF4. No pretrained model, language competence,
frontier parity or measured power claim is part of this return. The full corrected goal remains active.
