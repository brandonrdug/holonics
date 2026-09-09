# AC1: the return journal keeps zero extension as a generator

[definition] This continues AC1 steps 3–4 from `0802fa42`. The existing material-contact response
and its historical decoder remain the owners. The change reduces repeated representation of
their actual constrained return; it changes neither the constitutive learning law nor the
selected-word application introduced by the preceding return.

## The generator and its exact domain

[proved-derived] Let a response be produced with k contacts and applied after K contacts have
been born, with k ≤ K. In contact birth order, let `E : C^k → C^K` extend a vector by zero.
For the retained two-factor contact covector,

```
G = p0 f0† + p1 f1†,
G_extended = p0 (E f0)† + p1 (E f1)† = G E†.
```

The displayed equality follows entrywise: the first k columns are the original columns, and
every later column is zero. E preserves the complete Euclidean norm, so the existing covector
radius remains valid. Componentwise dyadic truncation commutes with this extension because
truncation sends zero to zero. The extended numerical increment, all its nonzero rounding
defects and its norm are therefore recovered without allocating the zero suffix.

[established-bounded; source-inspected] The actual `field_operative_adjoint.cuh` producer holds
the input internal current fixed during this contact response. Its internal-current increment
is identically zero; incoming-current reactions remain in the response diagnostics. Previously
it wrote an expanded zero array, and `apply_material_contact_realization` allocated another
expanded zero array while extending the factors to the current contact count. Every successful
return retained that array in the journal. The sixteen-family measurement attributed 820,449,024
native bytes to these internal-delta carriers.

[definition] The zero increment is not the live internal current, a source remainder or a
zero uncertainty bound. Those retain their existing owners and receivers. The full contact
population K and application cut also remain unchanged. Only the increment's numerical zero
generator and the factor extension receive a smaller representation.

## Native update, historical return and wire

[established-bounded; source-inspected] `OperativeReturn` now retains `factor_count` separately
from `contact_count`. The native producer's unexpanded factors are shared immutably; no separate
extension launch or zero-delta output is allocated. The update kernel reads the original factor
extent, returns zero outside it, and copies the actual internal current when the delta generator
is zero. It still recomputes the complete changed map's covariance and aggregate with the
existing mixed terms and bounds.

[established-bounded; source-inspected] Historical producing-map recovery uses the stored
factor extent and the original chronology. The cold deposit receiver expands the same zero
suffix when presenting its complete numerical projection defect. Neither operation substitutes
a current map for the map that produced an older carrier.

[definition] `OperativeReturnFrame` carries optional `factor_count` and `zero_internal_delta`
wire descriptors. Missing descriptors keep the legacy expanded interpretation. The zero marker
is a declared one-word zero, validated with its shape; it cannot carry a nonzero value. New
readers also recognize an exactly zero legacy delta while mounting its already-read cold wire.
Nonzero legacy deltas retain their full payload. This is an exterior representation check and
does not read hot numerical state or enact another occurrence. Existing error bounds are kept
independently, including any nonzero unrounded comparison bound.

[established-bounded; source-inspected] The source fields and future generators determine the
decoder: at a contact below `factor_count`, read the stored factor; at a later contact below
`contact_count`, return zero; outside the declared domain, the existing shape contract refuses.
This is an executable zero-extension generator. It does not identify source occurrences,
discard the Preimage Fibre or claim bounded representation of the remaining nonzero factors.

## Verification and product scope

[established-bounded; measured] The focused native control compares the compact return with
its independently expanded factors and zero array. Complete staged contact maps, internal
currents, radii, covariance and aggregate agree in both `EnclosedFlow` and `DyadicDeposit`.
Staging performs no section readout. The control also rejects a malformed zero marker, mounts
the old expanded wire and returns through an older producer after compact remount and another
actual occurrence. It passes, including the initial CUDA module load, in 105.60 seconds.

[established-bounded; measured] All 111 field tests pass in 128.91 seconds, and all 25 alpha
SDK tests pass in 7.49 seconds. The text study and actual post-generation restart example compile.
The [portable receipt and logs](2026-09-09_zero_extension/return.json) retain the commands,
scopes and comparisons.

[established-bounded; implemented-exact; measured] The saved 5,064-occurrence model mounts from
its original expanded wire, saves the new wire and continues through the same prompt. A second
fresh process mounts that compact checkpoint and executes the same continuation. Both runs
match the original complete recorded body, emission-current history and generation exactly.
The journal shrinks from 2,496,666,560 to 1,676,217,536 native bytes: 820,449,024 bytes of expanded
zero deltas are replaced by their generators. Old factor extents remain as recorded; this
conversion does not infer a smaller historical producing population from coefficient values.
The checkpoint shrinks from 2,327,563,760 to 1,917,516,453 bytes, saving 410,047,307 bytes.

[established-bounded; measured] The conversion process, including checkpoint output, takes
91.28 seconds with peak RSS 4,758,388 KiB. Fresh compact remount plus the prompt, generation and
cold diagnostics takes 71.82 seconds with peak RSS 3,954,196 KiB. Native residency before cold
body diagnostics is 3,878,996,320 bytes, exactly 820,449,024 below the preceding actuation run.
Checkpoint readouts in the conversion run are durable I/O and are recorded separately from the
no-checkpoint continuation comparison; they are not claimed as hot semantic readouts.

[established-bounded; implemented-exact; measured] A fresh matched first-family development
returns all 75 occurrences and 74 contact responses with the same complete body as the prior
run. No numerical section readout occurs during development. The journal shrinks from 1,049,024
to 862,080 native bytes, including the saved factor suffixes on new returns. The checkpoint
shrinks from 11,770,284 to 11,680,724 bytes. Development takes 7.628 seconds versus 7.615 in the
prior run: this evidence establishes storage reduction, not a speed improvement.

[definition] This is representation reuse within AC1, not a new learning result. The last
measured model emits `I’mn` and `EndPart`; useful AC2 language remains open. The nonzero return
factors, recurrent path formation and their actual future receiver family still require further
construction. AC3 remains experimental, and AC4–AC5 remain open.
