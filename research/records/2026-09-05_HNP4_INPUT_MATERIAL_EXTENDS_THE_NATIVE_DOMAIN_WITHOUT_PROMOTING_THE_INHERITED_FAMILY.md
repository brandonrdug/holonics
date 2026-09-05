# HNP4: additional input material and native continuation

**Date:** 2026-09-05 local. **Position:** HNP4 remains in progress. This is the input-material
and persistence return, not completion of its text/document or second-application obligations.

## Concrete missing material

[established-bounded; source-inspected] `target/ske4/rest.bin` retains all 262,144 rows of native
lookup population 0 (width 2,560), but only 21 rows of lookup population 1 (width 10,752). Its
other restricted cross-sections and original signature-family records remain as returned by SKE.
The old family check is not the same question as whether a wider native occurrence has actual
input sections. Zero insertion inside the declared restricted matrix does not recover a missing
foreign input row or establish inherited correspondence outside the declared family.

## Returned composition

[established-bounded; implemented-exact] `operative_condensation.rs::NativeInputExtendedIntake`
composes the existing restricted intake with `NativeInputRowExtension` sections. It accepts only
previously absent rows of populations whose every use is a lookup. It rejects replacement,
overlap, invalid shape/order/range and any population also used by a contraction or another
primitive. Packed and expanded delivery preserve the original codewords and insert the actual
new sections. Original classes, cones, histories and remainders are not mutated or regraded.

[established-bounded; implemented-exact] `holonics-hna::input_material` acquires the requested
missing sections through the exterior source chart. Source chart equality aligns population
ordinals; it is not coefficient identity or a new excitation-founded quotient. The application
does not execute the foreign model. Its return is ordinary Safetensors with U32 row addresses,
BF16 codewords, section dimensions and the original base's wire pin. The separate acquisition
receipt names the source container. Native intake sees only ordinals and integer codewords.
Acquisition supplies material; the existing observed-passage law still owns learning.

[proved-derived; formal-checked] `HolonicResidentRestriction` now proves
`gather_old_rows_unchanged_after_extension` for ordered words, including repeats;
`extension_returns_exact_added_section`; and the conditional
`deterministic_continuation_preserves_old_word`. The concrete repeated-old-row and new-row
discriminator controls also check. This establishes the stated matrix/gather relations and
their consequence through the same supplied continuation, not a machine-checked CUDA program.
The focused `lake env lean ElementaryHolonics/Computation/HolonicResidentRestriction.lean`
returned without new axioms or `sorry`.

[established-bounded; implemented-exact] `HnaModel::with_input_material` composes the immutable
material before mounting. `HnaSession::advance_native` uses the same continuing native owner
under the observed-passage law, checking actual supplied rows at every input port and the mounted
input-workspace aperture. Missing material refuses before advancement. Its admission receipt
states original-family membership separately; `advance` retains the original family check.
Neither membership nor native execution asserts fidelity of the cultivated successor.

[established-bounded; implemented-exact] Checkpoint versions 3/4 explicitly retain input-material
dependencies, respectively without/with transport state. Versions 1/2 preserve their old meanings.
Resume verifies each dependency and reads its same opened handle through
`foreign_map::manifest_safetensors_file`; the files must remain immutable while consumed.
Input material is not silently embedded, and no foreign executor is needed on resume. The
existing JSONL session adds the explicit `advance-native` action and `native-advanced` event;
`--input-material` composes a new artifact. Its old `advance` action is unchanged.

## Actual native return

[established-bounded; measured] The driver `crates/holonics-hna/examples/input_material_hnp4.rs`
used the actual HNP3 cultivated checkpoint and the standing Gemma source as exterior material.
Two ordinary text occurrences were encoded by `AthenaTokenApplication`: “Describe a red cube.”
and “Correction: the cube is blue.” Acquisition added nine rows of population 1, or 96,768
codewords, in a 193,980-byte Safetensors artifact. No source output or expected answer supplied
the added rows or chose the native update.

[established-bounded; measured] With that material mounted, the old family receiver still refused
the new text without changing anatomy. An old admitted occurrence then produced the **entire
same native successor rest** as the earlier unextended reference: generation 5,100, factor extent
7,112. This comparison includes all held arrays, morphology, carriers, chronology and numerical
origins, not only a face or digest. A missing row (`u32::MAX`) also refused before mutation.

| Ordinary native occurrence | Generation / factor extent | Selected exterior token |
|---|---|---|
| `Describe a red cube.` — 14 input rows, outside original family | 6,375 / 8,890 | 31,166 → ` mik` |
| `Correction: the cube is blue.` — 16 input rows, outside original family | 7,650 / 10,922 | 86,169 → ` yên` |
| First occurrence again after the saved state | 8,925 / 12,700 | 86,169 → ` yên` |

[established-bounded; measured] The mounted input aperture was 512 rows. The first two new
occurrences retained their developmental successor in `developed.hna`. A further uninterrupted
operation produced `expected-after.hna`. A separate process resumed `developed.hna` with its
material dependency, advanced once, and compared the complete successor equal to that reference.
The exercise process took 103.985 s and the fresh-process continuation 112.977 s, including base
I/O, mounting and artifact work; these are not hot inference latency measurements.

[established-bounded; measured] The public JSONL CLI then resumed that same material-bearing
model, executed `advance-native`, emitted sequence 1 with original-family class absent, and
saved a 770,265,349-byte version-4 checkpoint. Its complete native rest also matched the
reference; transport buffers were empty and the native state was awaiting the next occurrence.

```sh
target/debug/examples/input_material_hnp4 prepare \
  .local/artifacts/hnp3/checkpoint-01.hna /home/b/models/gemma-4-E4B-it \
  .local/artifacts/hnp4/input-01/material.safetensors

target/debug/examples/input_material_hnp4 exercise \
  .local/artifacts/hnp3/checkpoint-01.hna .local/artifacts/hnp4/input-01/material.safetensors \
  /home/b/models/gemma-4-E4B-it .local/artifacts/hnp4/input-01 \
  .local/artifacts/hnp3/expected-after-01.hna

target/debug/examples/input_material_hnp4 resume \
  .local/artifacts/hnp4/input-01/developed.hna /home/b/models/gemma-4-E4B-it \
  .local/artifacts/hnp4/input-01/expected-after.hna
```

[definition] Reproduction uses new publication destinations. The example's `request SOURCE_ROOT`
command emits the corresponding native-domain JSONL request; the actual CLI artifacts are
`continue.jsonl`, `stream-events.jsonl`, `stream-process.json`, and `stream-after.hna` in the same
ignored local directory. `checkpoint_hnp3 compare-stream STREAM EXPECTED` performed the last
complete native-state comparison. No large model artifact was committed or overwritten.

## Verification and open application work

[established-bounded; measured] Both focused native intake tests passed, including packed/expanded
delivery and the valid shared-contraction refusal. Ten existing foreign-map tests passed after
adding same-handle manifestation. All 32 HNA and nine workbench library tests passed, including
material round-trip, wrong/missing/stale dependency and overlapping-row refusals, explicit
native-stream dispatch and CLI material-argument parsing. The workbench binary and HNA examples
built. `git diff --check` returned cleanly.

[established-bounded; measured] The independent installed Safetensors/PyTorch reader loaded
`material.safetensors`: `input/1/addresses` has shape `[9]`, dtype `torch.uint32`;
`input/1/words` has shape `[9,10752]`, dtype `torch.bfloat16`. This is an independent storage-format
check, not target-model execution or an HNP6 export result.

[open] These token readings are not useful descriptions or evidence that the correction was
understood. They are single-cycle observations, not complete generation under a finished
application boundary. HNP4 still requires complete multi-cycle text/document products, an actual
later correction of behavior, natural completion versus open/interrupted cases, and a genuinely
different stateful/sensory application. Material acquisition currently occurs before mount; a
new generated address without its sections remains an obstruction. The other restricted
computational populations have not thereby acquired wider inherited-fidelity evidence. These
relations must be addressed through the production pipeline, not hidden by a renderer, a larger
token count, a source executor or a regraded successful API transcript.
