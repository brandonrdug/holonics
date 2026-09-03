# Holonics command application

`holonics` operates persistent, explicit-root morphology-variant workspaces. The model lifecycle is
the primary CLI. Low-level transport probes remain under `diagnostic`; the premature Ratatui surface
has been removed.

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

## Honest open capabilities

Every workspace names these as open:

- `raw-model-directory-lift-open`;
- `qualitative-emission-codec-open`; and
- `persistent-configurable-diffusion-open`.

The current application produces a real source-neutral, persistently cultivated and evaluable
morphology variant from an admitted native snapshot. It does not yet accept a text prompt
or emit a useful natural-language answer.
