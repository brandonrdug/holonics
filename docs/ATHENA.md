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
The CLI commands below still expose their earlier prefix chart; persistent public sessions and
general production delivery are HNP3/HNP4, not implied by this low-level addition.

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

Use global `--format json` for the versioned response envelope, `--format jsonl` for events,
or the default human summary. `MODEL` currently names a supported local Gemma directory with
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
| Earlier `NativeCirculationSnapshot` / `NativeMorphologyArtifact` | The existing persistent workspace's exact package/snapshot family. It has a specialized lifecycle and does not silently contain the full operator's device overlays. |
| Standard executable model | Target architecture, parameters, configuration/codecs and validated runtime behavior; see [interop](INTEROPERABILITY.md). |

[open] A durable checkpoint of the cultivated full native operator—including overlays, carrier
state, chronology, base realization dependency and exact remount—is the next persistence bridge.
Current `hna train` retains the successor during its session and returns its receipt; it does not
claim to save a deployable trained model. The older `workspace` commands remain usable for their
own snapshot family and are labeled accordingly.

## Production expectations

[definition] The [production campaign](plans/THE_HNA_PRODUCTION_CAMPAIGN_COMPOSES_LOCAL_LEARNING_PERSISTENT_MODELS_AND_EXECUTABLE_EXPORT.md)
specifies the general material/current binding and local development missing from the narrow
prefix convenience pathway, as well as persistence and multi-cycle output. Its target session
interfaces are planned, not already implemented versions of the commands above. Dataset delivery
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
