# WB2 Eros, Soulkiller, engine, and CLI returned one event surface

**Date:** 2026-09-01
**Truth status:** `established-bounded` for the callable Workbench adapters and CLI in their
declared command families.
**Evidence:** `implemented-exact`, `source-inspected`, `process-audit`, and `measured`.
**Construction effect:** WB2 passed; WB3 becomes the sole current deed.

## Returned adapters

[established-bounded; implemented-exact] Eros `mouth` reads complete files under an explicit root,
extension and octet aperture, then calls the standing exposure-codec ladder and returns each rung,
founded compound units, and exact stop/refusal. Eros `atlas` calls the standing prose, Rust or Lean
incidence owner, then returns constituents, contacts, heights, rank-gauge testimony, face quotient,
collapsed blocks and separators. The Workbench does not shell to the historical `eros` binary.

[established-bounded; implemented-exact] Soulkiller `config`, `index`, and `onnx` use the lossless
foreign-chart owners. Configuration retains raw root fields; shard index retains declaration order,
tensor-to-shard map and total size; ONNX retains IR/opset, graph, nodes, initializers, ports and
operator testimony. Every receipt explicitly reports `foreign_execution: false`.

[established-bounded; implemented-exact] Engine `status` reads actual process parallelism and opens
the CUDA apparatus owner to report device/block testimony or a typed obstruction. `capabilities`
reports only the local callable application surface and open fibres. `package` reads either native
package wire or a circulation snapshot and returns the derived manifest. `export` emits exact
rested-inference ONNX or Safetensors through the standing lens.

[established-bounded; implemented-exact] The `holonics` CLI now executes one
`WorkbenchCommand` through `WorkbenchRuntime` and renders the returned `WorkbenchEvent` population
as human text or JSON Lines. It exits nonzero on an obstruction. CLI help contains Athena, Eros,
Soulkiller, engine, capabilities and TUI entry points.

## Receipt

[established-bounded; process-audit; measured] The focused command

```text
timeout 180s cargo test -p holonics-workbench --test adapters -- --nocapture
```

returned exit `0` in 7.21 seconds: two passed, zero failed. One control executes status,
capabilities, Eros mouth/atlas over two material files, Soulkiller config/index, Athena demo
snapshot, engine package/ONNX export, Soulkiller ONNX inspection, direct runtime status, CLI JSON
status equality, and complete CLI help. Missing files, malformed JSON, and absent material return
obstructions without foreign execution.

[open] WB2 contains no interactive interface. WB3 owns only the Ratatui/Crossterm view, update and
event loop over `WorkbenchRuntime`, headless rendering, and exact direct/TUI command equality.
