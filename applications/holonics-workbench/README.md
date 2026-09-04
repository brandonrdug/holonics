# Holonics command application

`holonics hna` runs the current full native recurrent model interface. `holonics workspace`
retains the earlier persistent snapshot family; low-level probes remain under `diagnostic`.
The [Athena guide](../../docs/ATHENA.md) owns the training/inference contract, and
[WORKBENCH.md](WORKBENCH.md) describes command-family composition.

## Native training and inference

```sh
holonics hna infer /path/to/supported/model 'Explain holonics briefly.'
holonics --format json hna train /path/to/supported/model sequence.json
holonics --format json hna run request.json
holonics hna inspect /path/to/native.rest
```

The native commands support the configured Gemma realization and restricted SKE material.
Training uses one session over continuing tokenized prefixes and returns a run receipt, not a
saved full-operator checkpoint. Inference returns one selected face, not a complete chat response.

## Install

```bash
cargo install --path applications/holonics-workbench --locked
holonics --help
```

Running `holonics` without arguments prints the high-level command help and exits successfully.

## Actual inherited-snapshot workflow

[2026-09-03: the per-event construction departed without alias under SKE4 and
`lift-gemma-receipt` went with it. The admitted inherited input is an already valid native
circulation snapshot, not an excitation-return directory and not an arbitrary raw model directory.]

```bash
holonics workspace create /data/athena/first first-athena
cd /data/athena/first

holonics workspace import-snapshot \
  /data/athena/generation-0.snapshot.json

holonics workspace define-experiment \
  primary \
  --ingress 0

holonics workspace conduct primary

holonics workspace stage-return \
  100 200 1 1/2 1

holonics workspace commit
holonics workspace evaluate primary
holonics workspace export onnx
holonics workspace export safetensors
holonics workspace inspect
```

Each command is a separate process. Active boundaries and staged candidates persist in the
workspace, so conduct, return, commit, evaluation, and export survive process exit. One workspace
owns at most one active run. Commands after `create` use the current directory by default; use
`--root /data/athena/first` when invoking them from elsewhere.

`continue` accepts only an actual successor returned by the active boundary:

```bash
holonics workspace continue 0
```

Native snapshots carrying an admitted predecessor relation can continue through this
command; a snapshot whose occurrences carry no predecessor returns no actual successor. A false
successor refuses without changing the active run.

## Where artifacts go

There is no hidden artifact root. Everything is beneath the root supplied to `workspace create`:

```text
/data/athena/first/
  workspace.json
  snapshots/generation-0-import-1.snapshot.json
  experiments/primary.json
  runs/run-N/boundary-0.json
  runs/run-N/candidate.json
  runs/run-N/commit.json or decline.json
  snapshots/generation-1-run-N.snapshot.json
  evaluations/evaluation-N.json
  exports/export-N.onnx or export-N.safetensors
  exports/export-N.receipt.json
```

Every successful response prints:

- `workspace_root` as an absolute path;
- `current_snapshot` as an absolute path; and
- `written_artifacts` as absolute paths.

Immutable artifacts use create-new writes. `workspace.json` and an active `run.json` use
same-directory atomic replacement. Relative references and symlinks may not escape the explicit
root.

## Structured I/O

Human output is a typed projection of the same response returned by JSON:

```bash
holonics --format human workspace inspect
holonics --format json workspace inspect
```

The versioned request form is:

```json
{
  "schema": "org.holonics.workbench.request.v3",
  "command": {
    "domain": "workspace",
    "command": {
      "action": "inspect",
      "root": "/data/athena/first"
    }
  }
}
```

Execute a request with `holonics --format json run request.json`. Responses use
`org.holonics.workbench.response.v3`; streamed events use
`org.holonics.workbench.event.v4`.

## Diagnostic boundary

The old bounded mechanisms remain explicitly subordinate:

```bash
holonics diagnostic status
holonics diagnostic athena open alpha /data/athena/generation-0.snapshot.json
holonics diagnostic eros atlas .
holonics diagnostic soulkiller inspect /path/to/config.json
```

They inspect or exercise low-level owners. They do not create a persistent model workspace.
[2026-09-03: the per-event construction departed without alias under SKE4 and the workbench demo
went with it; `diagnostic demo` and `athena demo-open` are absent.]

## Snapshot-workspace boundary

Every workspace names these as open:

- `raw-model-directory-lift-open`;
- `qualitative-emission-codec-open`; and
- `persistent-configurable-diffusion-open`.

These workspace limitations do not describe the new `hna` command family. This snapshot
application persists its own morphology variant; it does not persist the full HNA operator's
device overlays. Its ONNX/Safetensors exports are package containers, not standard executable
model recompilation. See [interoperability](../../docs/INTEROPERABILITY.md).
