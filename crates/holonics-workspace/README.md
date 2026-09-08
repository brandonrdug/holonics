# Holonics persistent snapshot workspace

This library is the presentation-independent boundary for the earlier native circulation/snapshot
artifact family under an explicit root. The full-operator HNN interface is
[`holonics::hna`](../holonics-hna/README.md); its run receipt is not one of these snapshots.

It composes existing owners for:

- native circulation snapshot import;
- resolved experiment specifications;
- persisted conduct and actual-successor continuation;
- separately staged world returns;
- atomic commit or decline;
- current/latest-withdrawn/replay-restored evaluation; and
- exact package round-trips inside ONNX and Safetensors containers.

This specialized workspace accepts no arbitrary Hugging Face model directory and has no prompt
codec. Those limitations describe this artifact family, not the separately supported full native
Gemma execution path. Its package exports are not standard executable neural graphs; see
[interoperability](../../docs/INTEROPERABILITY.md).

## Workspace layout

```text
ROOT/
  workspace.json
  lifts/lift-N/
  snapshots/
  experiments/
  runs/run-N/
  evaluations/
  exports/
```

Every returned `WorkspaceReturn` contains the absolute workspace root, absolute current snapshot,
and absolute newly written artifact paths. The native package and snapshot remain the engine's
existing exact wire types; the workspace manifest is an exterior application chart.

The library always receives an explicit root. The `holonics` CLI resolves that root from
`--root PATH` or, by default, the current directory so an operator does not repeat it throughout a
workspace session.
