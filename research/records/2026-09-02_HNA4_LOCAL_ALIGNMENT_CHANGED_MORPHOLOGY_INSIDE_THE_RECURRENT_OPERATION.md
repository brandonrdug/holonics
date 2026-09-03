# HNA4 local alignment changed morphology inside the recurrent operation

**Date:** 2026-09-02  
**Truth status:** `established-bounded`  
**Evidence:** `implemented-exact`, `source-inspected`, `process-audit`, `measured`  
**Campaign:** HNA4 under the recurrent HNA contract.

## Correction before the return

[counterexample; source-inspected] The first HNA4 draft stored a caller-supplied factor under
operation ordinal 41. Although the carrier changed, operation 42 did not read that morphology; the
caller had authored the update. That draft receives no HNA4 grade.

[implemented-exact] The corrected owner realizes the formal `advanceMorphology` shape inside the
ordinary operation:

```text
MorphologyBefore x (occurrence, presented carrier, reacted carrier)
  -> exact local alignment
  -> MorphologyAfter
  -> scaled reacted carrier
  -> emission, trace, successor ecology.
```

The developmental occurrence may carry a positive exact local conductance but cannot supply the
morphology result. The operation reads the complete presented and reacted interval populations,
forms their exact midpoint inner-product alignment over `BigInt`, refuses non-positive alignment,
and only then composes the conductance into the ecology's global local-morphology factor. Every
later operation applies the stored factor to its own reacted carrier and reports the factor in its
trace. No output label, expected answer, loss, reward, status, world verdict, candidate, or commit
object enters this relation.

## Return

[established-bounded; implemented-exact; measured] Two ordinary source-neutral occurrence rows
advanced through the first 41 full-ecology operations. At the learned-scalar operation 41, a
positive exact conductance `2 * 2^0` entered. The operation's presented/reacted alignment was
positive; the trace returned morphology factor `1 * 2^0 -> 2 * 2^0`, generation `41 -> 42`, and a
nonempty successor emission.

[established-bounded; implemented-exact; measured] Operation 42 was invoked through the same
`NativeFullOperatorSession::advance` API. Its graph input was operation 41's emitted carrier, its
trace joined generation 42 exactly, and its trace reported the changed morphology factor 2. The
following successor retained that same factor. Supplying another morphology current at operation
42 was rejected because that operation has no admitted morphology-current port.

## Grade

[established-bounded] **HNA4 PASSED.** The morphology difference is derived and installed inside an
ordinary recurrent operation, belongs to its returned successor, and is read by the immediately
following operation without a second semantic API. No rest/remount control was requested, so none
is used as evidence. HNA5 is now the sole current deed.

[open] This is one bounded exact local-conductance learning law. It does not establish that the law
improves language behavior, optimizes a loss, or is an unrestricted learner; HNA5 must report the
actual application faces without interpreting the morphology change as quality.

## Reproduction

[process-audit] The return was produced by:

```text
cargo check -p holonic-engine --example developmental_morphology_hna4
cargo run -q -p holonic-engine --example developmental_morphology_hna4 -- /home/b/models/gemma-4-E4B-it
```

