# AC1: material reports reuse their coordinate support

[definition] This continues AC1 step 4 from the [complete-current metric return](2026-09-08_AC1_THE_MATERIAL_AND_CONTACT_RETURN_SHARE_THE_COMPLEX_CURRENT_METRIC.md).
The eight-family model retained a full 512-coordinate target in every material report, despite
its sparse coordinate support. This return supplies a native restriction/decoder and a smaller
whole-model checkpoint. It does not establish learned path formation, a condensed recurrent
learner, or useful Athena-alpha.

## The retained coordinate law

[definition] A contextual material report has `82*T+68*N+96` exact words, for `N` root channels
and `T` target coordinates. Each target coordinate owns 82 words: its complex components in
eleven current balls, two complex coefficient factors, and the signed wide evaluation evidence.
The remaining `68*N+96` words contain the radii, source/condition geometry, chronology and scalar
defects. The words are codewords for this finite report chart, not independent physical holons.

[proved-derived] Write the report as `(A,c)`, where `A` has one 82-word column per target and `c`
is the common standing. Define `S` as the coordinates with a nonzero column. Restriction retains
`(S,A|S,c)`; its decoder extends the missing columns by the constant-zero generator. Thus
`decode(restrict(A,c))=(A,c)` for the actual report. This is a sparse coordinate presentation,
not a minimal-rank factorization, intrinsic neural capacity, or identification of causal sources.
A decoder of this finite computational chart does not invert the holon's complete Preimage Fibre.

[established-bounded; implemented-exact] `field_material_support.cuh` discovers that inventory,
packs its columns and common standing, and unfolds either the complete report or only the first
current face. Discovery occurs on device. The inventory crosses the process boundary for
allocation; amplitudes and current values do not determine a host learning branch. The full
report's phase components, source lineage, all radii and signed residual evidence are retained.

[definition] An omitted column is not an omitted target coordinate or an assertion of zero
uncertainty. The original ambient target extent and common current-ball radii remain. The
existing joint-ball packet receiver therefore still sees implicit zero-centred coordinates and
all uncertainty admitted by that ball. This is not an observed-word filter. A later observation
can introduce another coordinate in the ordinary field, and its later report receives its own
support inventory; an old support is not imposed as a permanent alphabet or interaction boundary.

[established-bounded; implemented-exact] `NativeMaterialReportPacking` holds this immutable native
representation. Its packet receiver unfolds only `4*T+2` words, keeping the other current balls,
factors and raw evaluations packed. Its rest/remount and full decoder also operate after the
original field has been dropped. This is reuse of historical report standing, not a second
continuing ecology.

## Durable field integration

[established-bounded; implemented-exact] Tensor/operative field checkpoints now write field-rest
version 2. Each material report chooses the packed representation only when its encoded byte
length is smaller; otherwise it retains the dense representation. Non-tensor field writers keep
version 1, and the reader accepts both versions. Packed reports bind to the enclosing field's
actual lineage, root extent and target chart before complete field validation.

[definition] Durable serialization uses the cold implementation of the same restriction/decoder.
It is an I/O operation over already-retained words, not a host implementation of learning or
coefficient formation. Cold and native encoders are compared exactly. The decoded field restores
its complete original state, capabilities and pending boundary; no development or source replay
is used to obtain it.

[open] The current whole-field mount still unfolds historical material reports into their
original dense resident sections. Therefore this checkpoint return does not reduce whole-field
GPU residency or make the recurrent material kernel operate on compressed history. The native
packed-report receiver is available, but integration with the complete material-query/adjoint
family remains unfinished. A present report decoder alone is not the dynamic generator square
for a compressed learner.

## Native and actual-model evidence

[established-bounded; measured] The two focused native controls pass, including complete word
coverage, empty and dense support, complex phase, source-free report/packet reuse, invalid
inventory refusal, agreement with the cold encoder, and version-2 whole-field round-trip.
All 103 constitutive-field CUDA tests then pass in 89.10 seconds. Both changed examples compile.
An initial cold-reader helper used `Read` where the bounded blob reader required `Take<Read>`;
that signature was repaired before these checks passed.

[established-bounded; measured] The actual 1,930-occurrence model returns:

| Occurrence | Retained coordinates | Original report words | Packed report words | Packed native bytes, including inventory | Packed rest bytes | Native packing time |
|---|---:|---:|---:|---:|---:|---:|
| 0 | 1 | 43,304 | 1,402 | 30,640 | 12,179 | 5.19 ms |
| 75 | 33 | 43,304 | 4,026 | 72,624 | 33,293 | 4.70 ms |
| 1,000 | 51 | 43,304 | 5,502 | 96,240 | 45,163 | 4.54 ms |
| 1,929 | 57 | 43,304 | 5,994 | 104,112 | 49,124 | 4.51 ms |

[established-bounded; measured] Every complete decoded report equals its original, and every
packed packet reading equals the original receiver reading. Each packing performs two native
deeds and one coordinate-inventory readout. The original field remains resident during these
comparisons; the table's packed-object sizes are not whole-process memory savings. The original
report alone occupies 692,864 resident bytes in its two exact-word lanes.

[established-bounded; measured] The whole checkpoint shrinks from **975,051,301** to
**390,957,778 bytes**, saving **584,093,523 bytes** (about 60%). Repacking the existing model takes
48.68 seconds with peak RSS 2,112,808 KiB. A fresh process reads the packed model and reproduces
the complete body, recorded emission currents, generation readings, text and `SquaredCurrent`
metric exactly. That process takes 101.09 seconds with peak RSS 2,118,312 KiB. The native-report
inspection process takes 29.63 seconds including model loading. The
[portable receipt](2026-09-08_material_report_packing/return.json) retains commands and full costs.

[counterexample; measured] The answer still repeats `The its the its ...`. Compression preserves
that failed behavior; it does not establish language improvement. AC1 path formation and a
compressed recurrent representation, AC2 useful continuation, broad AC3 cultivation and AC4–AC5
remain unfinished. No unchanged cultivation run was repeated for this storage comparison.
