# Athena and the HNA training/inference interface

[definition] Athena is one continuing native ecology: its constitutive morphology, current,
incidence, chronology, lineage and admitted receiver domain. Eros is the composition and recurrent
operation that forms and refines it. The current public Rust entry point is `holonics::hna`;
the implementation is in [holonics-hna](../crates/holonics-hna/src/hna.rs).

## One operation, two uses

```text
contemporary Athena + ordinary occurrence
    -> native current and reaction
    -> emission + trace + successor Athena
    -> next ordinary occurrence on that successor
```

[definition] Inference reads the emitted result. Developmental recurrence additionally changes
the morphology where the declared local return law applies. These are uses of one operation,
not separate forward and world-verdict engines. A receiver result or a loss scalar is testimony;
the native operation owns its current, reaction and successor.

[established-bounded; source-inspected] The earlier full-operator prefix return compares a continuing
occurrence with the previous emission, propagates its differential through the retained forward
morphology and stages factorized deposits. Previously retained overlays participate in the
adjoint. New atoms join after the return succeeds. Three-cycle/two-return CUDA execution and
exact local pullback controls stand at the [September 4 repair scope](../research/records/2026-09-04_THE_AUDIT_REPAIRS_THE_RECURRENT_ADJOINT_AND_RECONCILES_THE_OPERATING_CONTRACT.md).

[established-bounded; measured] The native session now also exposes
`NativeFullOperatorSession::found_with_passage_return`: ordinary non-prefix material operates
the same body, and actual joined-output changes return through their retained local reactions.
New factors publish when the cycle closes. Three native-model occurrences, the zero-partner
discriminator and exact withdrawal/restoration returned in
[HNP1](../research/records/2026-09-04_HNP1_THE_ACTUAL_JOINED_PASSAGE_RETURNS_LOCAL_DEVELOPMENT_AND_THE_DELTA_SURVIVES_ATTRIBUTION.md).
The older batch/text commands retain their prefix chart. The continuing public session and
stream below expose observed-passage development; useful production applications are HNP4/HNP5.

[established-bounded; measured] The observed-passage session now retains complete native numerical
segments and reopens their dependency closure when entering material or coefficients change.
It still enacts local returns and chronology. Reuse traces name their prior numerical computation;
the actual reference/reuse continuation and costs are in
[HNP2](../research/records/2026-09-04_HNP2_THE_NUMERICAL_SEGMENT_IS_REUSED_THE_NATIVE_OCCURRENCE_STILL_DEVELOPS_AND_CHANGED_DEPENDENCIES_REOPEN.md).
`without_forward_reuse` supplies a full-execution observer comparison, not a second learning law.

## Commands

Build the application:

```sh
cargo build -p holonics-workbench --bin holonics
target/debug/holonics hna --help
```

[established-bounded; source-inspected] The current commands call the full native session:

| Command | Return |
|---|---|
| `hna infer MODEL TEXT` | One selected native terminal face, decoded by the supplied exterior tokenizer. This is one inference cycle, not a full chat response. |
| `hna train MODEL SEQUENCE.json` | One developmental session over a JSON array of strictly extending text prefixes; optional `--learning-shift` and `--series-terms` declare the existing return aperture. |
| `hna run REQUEST.json` | A typed address/history sequence over a supported resident operator directory or a restricted SKE rest. |
| `hna inspect REST` | A native restricted-rest header, without initializing CUDA. |
| `hna session SOURCE --checkpoint NEW.hna` | A continuing observed-passage session with versioned JSONL input/output and a final native-plus-transport checkpoint; use `--resume` for a checkpoint source. |

For the batch commands, use global `--format json` for the versioned response envelope,
`--format jsonl` for events, or the default human summary. `session` always uses its own JSONL
stream on stdout and final process receipt on stderr. `MODEL` names a supported local Gemma directory with
its configuration, Safetensors coefficients and tokenizer. The tokenizer is an application codec.

Example developmental material:

```json
[
  "Explain holonics briefly.",
  "Explain holonics briefly. Holonics is the study of",
  "Explain holonics briefly. Holonics is the study of systems."
]
```

[definition] The tokenizer must preserve a strict prefix between consecutive occurrences.
Unrelated samples are refused by this training convenience command before CUDA use: the current
implemented return needs a continuing sequence. General dataset batching/packing is a separate
pipeline adapter, not something the command silently invents.

## Native request schema

```json
{
  "source": { "kind": "resident-operator-directory", "root": "/path/to/model" },
  "receiver": "terminal-face",
  "occurrences": [
    { "row_addresses": [155122, 4790, 76615, 21485, 236761], "history": [] }
  ],
  "cultivation": null
}
```

[definition] The address values above are codec-specific example data, not intrinsic native
identities. For SKE input, use `{"kind":"native-restricted-rest","path":"/path/to/native.rest",
"class":null}`; `class:null` mounts the composed extent, while a class ordinal restricts admission
to that class. The base address occurrence and declared history are admitted together and both
are executed. An unsupported receiver or outside-family request refuses.

[established-bounded; source-inspected] `HnaRunReceipt` returns source kind, actual selected
faces, predecessor/successor generations and overlay ranks, deposited populations and final
apparatus census. Add `"include_trace":true` to a native request for the full morphology trace.
All cycles use one move-owned session. The low-level native session remains
available for consumers needing complete emitted interval sections or interactive recurrence.

## Model artifacts and persistence

| Artifact | Meaning and current scope |
|---|---|
| Native restricted SKE rest | Executable inherited class/extent material, with declared domain and remainder. |
| HNA run receipt | Evidence of a completed session; it is **not a trained checkpoint**. |
| Native HNA checkpoint | Actual full-session state and integer factor codewords, with an explicit pinned native-base dependency; process-separated remount and further development returned in HNP3. |
| Earlier `NativeCirculationSnapshot` / `NativeMorphologyArtifact` | The existing persistent workspace's exact package/snapshot family. It has a specialized lifecycle and does not silently contain the full operator's device overlays. |
| Standard executable model | Target architecture, parameters, configuration/codecs and validated runtime behavior; see [interop](INTEROPERABILITY.md). |

[established-bounded; measured] The cultivated full native operator now has a durable checkpoint,
including overlays, carriers, chronology, numerical origins and interrupted/pending state.
Every held field and a later complete successor matched after process restart in
[HNP3](../research/records/2026-09-05_HNP3_THE_CULTIVATED_SESSION_RESTORES_EVERY_HELD_FIELD_AND_CONTINUES_AFTER_PROCESS_EXIT.md).
The native base remains an explicit dependency, not silently embedded or identified by a path.

[definition] Current `hna train` still retains the successor during its legacy prefix session and returns its receipt; it does not
claim to save a deployable trained model. The older `workspace` commands remain usable for their
own snapshot family and are labeled accordingly.

## Continuing public session

[established-bounded; implemented-exact] `HnaModel::from_native_rest` opens admitted material with
an explicit cultivation aperture; `from_checkpoint` restores its recorded state and profile.
`with_session` mounts once for the callback's lifetime. `advance` uses the same owner on every
request; `checkpoint` borrows that owner and publishes without overwrite. `declared_occurrences`
exposes the actual family/history records, and `anatomy` reports the model's held structure and
status. No tokenizer is reopened or old text re-encoded inside these calls.

```rust
use holonics::hna::{HnaModel, HnaSessionError};

fn continue_model() -> Result<(), HnaSessionError> {
    let model = HnaModel::from_checkpoint("checkpoint.hna", None)?;
    let occurrence = model.declared_occurrences()[0].occurrence.clone();
    model.with_session(|session| {
        let output = session.advance(&occurrence)?;
        println!("generation {}", output.final_emission.generation);
        session.checkpoint("checkpoint-next.hna")?;
        Ok(())
    })
}
```

[definition] Keep the callback open across a continuing request stream. Returning closes the
runtime; save explicitly if development must outlive it. Admission and publication refusals leave
the owner available inside the callback. A native failure after work begins retains an explicit
interruption and refuses silent replay.

## Streaming session and restart

[established-bounded; implemented-exact] `HnaModel::with_stream_session` supplies the same native
owner plus an exterior `HnaStream`. It reads one complete request before advancing and drains and
flushes the resulting event before accepting another. Transport packet boundaries create no
native occurrences. The request schema is `org.holonics.hna.stream-request.v1`; each JSONL record
has a `command` with `action` equal to `advance`, `inspect`, `checkpoint`, or `close`:

```json
{"schema":"org.holonics.hna.stream-request.v1","command":{"action":"inspect"}}
{"schema":"org.holonics.hna.stream-request.v1","command":{"action":"advance","occurrence":{"row_addresses":[1,2],"history":[]}}}
{"schema":"org.holonics.hna.stream-request.v1","command":{"action":"checkpoint","path":"during-session.hna"}}
{"schema":"org.holonics.hna.stream-request.v1","command":{"action":"close"}}
```

[definition] Replace the illustrative addresses with an actually admitted occurrence/history
from `declared_occurrences()`; the current SKE family restriction still applies. An `advance`
can request `"full_emission":true` to include all terminal intervals. The default returns the
selected face, emission shape, local-return receipt and anatomy; it does not decode prose.
Full interval responses can be large (118 MB in the native recovery control).

```sh
# Fresh observed-passage model; source is a native restricted SKE rest, not an HF directory.
target/debug/holonics hna session native.rest --input requests.jsonl \
  --checkpoint first.hna --learning-shift 16 --series-terms 14

# New process, same saved native development and delivery state.
target/debug/holonics hna session first.hna --resume --input more.jsonl \
  --checkpoint second.hna
```

[definition] Input defaults to stdin (`--input -`). `--checkpoint` is required and must name a
new file. EOF or `close` triggers a final checkpoint; input/output errors also attempt that save
and exit nonzero. A failed final publication is reported as unsaved state, not rollback.
Resume preserves the stored learning aperture; explicit aperture overrides are refused.
`--base PATH` on resume relocates the separate immutable base only if its wire pin matches.

[definition] `HNA-CHECKPOINT` version 1 carries native state; version 2 additionally carries
partial input, a pending response, the writer's accepted-byte cursor, event sequence and connection
state. Both retain the exact separate base dependency and the existing integrity footer. Native-only
read/session APIs refuse a transport-bearing checkpoint rather than discarding delivery state.
The native model requires the standing CUDA apparatus; the returned actual run uses an RTX 4080
SUPER/16 GiB, an 8.8 GiB base and 0.36--0.58 GB session artifacts. These are measured sizes for
this model/configuration, not general model limits or host-memory requirements.

[definition] Retrying the same writer continues at its accepted-byte cursor. Opening a new
connection replays the pending event from its start with the same sequence, without repeating
the native request. Accepted bytes and successful flush are not peer acknowledgment; peer-side
deduplication is external, and arbitrary process crashes do not imply end-to-end exactly-once
delivery. The CLI opens a new connection on each process. Incomplete input can receive its tail
after restart. A completed malformed frame remains held until the API operator explicitly takes
it with `take_input()`; later records are not silently appended to it.

[established-bounded; measured] The [HNP3 streaming return](../research/records/2026-09-05_HNP3_THE_STREAM_RETAINS_PARTIAL_INPUT_AND_REPLAYS_OUTPUT_WITHOUT_REPEATING_DEVELOPMENT.md)
compared complete native successor states after normal streaming, split-input process restart,
and a broken output pipe followed by replay. `input-exhausted` and `connection-closed` describe
transport only: the native anatomy remains `awaiting-occurrence`, not naturally completed output.

## Production expectations

[established-bounded; measured] HNP4 now has an explicit input-material extension. The actual
restricted base kept all 262,144 rows at one lookup port but only 21 at the second. The public
`HnaModel::acquire_input_material(source_root, addresses, output)` acquires missing rows through
the exterior source chart and saves ordinary Safetensors; `with_input_material(path)` composes
them before mounting. Only previously absent rows of lookup-only populations are accepted.
Retained rows and populations used by any other operation cannot be replaced through this seam.
This is material acquisition, not a new learning rule or an enlarged Soulkiller fidelity claim.

[definition] `HnaSession::advance_native` uses the same observed-passage recurrence on the
actually supplied input domain. It refuses missing sections or the mounted input-workspace limit
before native advancement. Its admission receipt distinguishes original-family membership from
native operation; it does not assert fidelity of a cultivated model. The existing `advance`
retains its original-family check. The corresponding JSONL action is `advance-native` and its
event is `native-advanced`; no existing `advance` request changes meaning.

```sh
target/debug/holonics hna session cultivated.hna --resume \
  --input-material inputs.safetensors --input native-requests.jsonl \
  --checkpoint extended.hna
```

[definition] Checkpoint versions 3 and 4 carry explicit input-material dependencies, respectively
without and with transport state. Versions 1 and 2 retain their old meanings. Resume verifies and
loads all named material without reopening a foreign source executor. Additional material is
presently composed at mount, not acquired automatically during a live session; a generated address
without its input sections remains an explicit obstruction. Safetensors here stores input sections,
not an executable standard-model export. The original base and every material artifact must remain
available and immutable.

[established-bounded; measured] Nine added rows (193,980-byte artifact) preserved the entire
old native successor and admitted two new text occurrences. A material-bearing checkpoint then
continued after process restart with complete successor equality. Their single-token readings
were ` mik` and ` yên`; neither is a useful response to the corresponding description/correction.
The [input return](../research/records/2026-09-05_HNP4_INPUT_MATERIAL_EXTENDS_THE_NATIVE_DOMAIN_WITHOUT_PROMOTING_THE_INHERITED_FAMILY.md)
states the control and remaining output obligations. This does not close HNP4.

[definition] The [production campaign](plans/THE_HNA_PRODUCTION_CAMPAIGN_COMPOSES_LOCAL_LEARNING_PERSISTENT_MODELS_AND_EXECUTABLE_EXPORT.md)
specifies the general material/current binding and local development missing from the narrow
prefix convenience pathway, as well as persistence and multi-cycle output. The public callback
and durable stream now exist; useful multi-cycle application output remains in construction. Dataset delivery
must preserve actual causal occurrences and may not define learning through arbitrary batching,
shuffling or an optimizer callback.

[definition] A production training pipeline must stream declared material through the same owner,
retain its successor, checkpoint/remount it and evaluate later behavior without changing the
training population from the evaluation target. Inference must retain state across requests,
support declared output/termination receivers and report insufficiency honestly. Export must
identify whether it is native persistence, package storage or an executable target graph.

[project-postulate] Quality, useful throughput, latency, memory, transfer and measured energy
belong in end-to-end evaluation on declared consumer hardware. The frontier-model objective is
the product goal; the current mechanical receipts establish the components from which that
pipeline is being built, not a completed quality benchmark.
