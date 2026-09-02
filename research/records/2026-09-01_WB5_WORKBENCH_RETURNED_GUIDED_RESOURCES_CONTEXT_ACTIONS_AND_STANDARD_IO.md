# WB5 returned guided resources, contextual actions, and standardized Workbench I/O

**Date:** 2026-09-01
**Truth status:** `established-bounded` for Holonics Workbench 0.2.0 over its declared local
resources, live sessions, typed commands, and request/response surfaces.
**Evidence:** `implemented-exact`, `source-inspected`, `process-audit`, and `measured`.
**Construction effect:** WB5 passed; WB0--WB5 are complete and no Workbench deed remains scheduled.

## The rejected surface

[established-bounded; source-inspected] Brandon's direct review correctly identified the first
Ratatui surface as a glorified CLI pane split. `COMMAND_CATALOGUE` contained raw strings and
unresolved placeholders, `Enter` copied them into a command editor, decorative category tabs never
changed state, the inspector was passive, and filesystem operations required path transcription.
Runtime ingress, receivers, boundaries, and actual successors already existed but did not determine
the available UI actions. The documented first demo was nine manual commands rather than a demo.

[established-bounded; source-inspected] CLI runtime events had one schema, but direct input was only
positional and malformed Clap input bypassed the JSON event surface. JSONL contained events without
one command echo, overall disposition, or stable structured-input boundary. Potentially slow
operations also executed inside the TUI key handler and prevented redraw.

## Returned interaction model

[established-bounded; implemented-exact] The raw command catalogue, embedded command parser,
command palette, and decorative tabs are absent. The TUI now starts from Guided start, live Athena
sessions, the current directory, subdirectories, and recognized configuration, Safetensors-index,
ONNX, circulation-snapshot, and morphology-package resources. `w`, `h`, and `Backspace` traverse
workspace, home, and parent roots without path entry. Discovery is bounded ephemeral application
state, not a repository catalog, hash identity, or retained semantic registry.

[established-bounded; implemented-exact] Selecting a directory returns Eros atlas, material-mouth,
and bounded discovery actions with automatic Rust/Lean/Markdown material choice. Selecting a model
chart returns the applicable lossless Soulkiller inspection. Snapshots and packages return remount,
anatomy, and adjacent non-overwriting export actions. User-local session snapshots and exports use
fully displayed non-overwriting destinations under `~/.local/share/holonics-workbench`.

[established-bounded; implemented-exact] Live-session actions are derived from the package and
current boundary. Every ingress/receiver pair and every actual successor is separately selectable.
Return and decline exist only while a boundary exists. Exact returned occurrence, world boundary,
real/imaginary current, and storage are visible and editable in a typed form. Only bounded demo
sessions receive an application-authored demo return; remounted morphology requires actual exterior
values.

[established-bounded; implemented-exact] A potentially slow command temporarily moves the one
`WorkbenchRuntime` to a worker. Rendering, pane navigation, and prior-event inspection continue.
A second mutation is refused until the runtime returns. Panic recovery returns the same owner and a
typed obstruction; this apparatus behavior does not claim parallel engine conduct.

## Complete demo and I/O

[established-bounded; implemented-exact; measured] `holonics demo` accepts zero required
parameters and returned five ordered events: bounded morphology open, generation-0 conduct, local
return 100 committed as generation 1, generation-1 conduct with two actual successors, and a final
next-action receipt. The same command returned from the real installed TUI through `d` and left the
live session selectable.

[established-bounded; implemented-exact] `WorkbenchRequest` and `WorkbenchResponse` standardize
structured input and output. A response echoes the typed command, carries one consequence or
obstruction disposition, and contains ordered `org.holonics.workbench.event.v2` events with optional
machine-readable refusal codes. `--format human`, `json`, and `jsonl` are explicit. Runtime refusal
exits 1; malformed CLI/request input exits 2 and remains a valid response envelope in JSON mode.
Direct status shorthand and the equivalent JSON request returned exactly equal responses.

## Controls and release

[established-bounded; process-audit; measured] The focused Workbench suite returned thirteen
passed, zero failed: ten library controls and three integration controls. It covers discovery and
filtering, request/response round trip, direct/structured equality, structured malformed input,
zero-parameter demo, filesystem navigation, context-valid actions, every actual successor, exact
return form, asynchronous runtime return, 80x24 and 120x36 rendering, adapters, and refusals.

[established-bounded; process-audit; measured] The installed `/home/b/.cargo/bin/holonics` reports
version 0.2.0. A real 80-column pseudo-terminal showed Guided start, resource/action/detail/event
regions, ran `d` to the five-event generation-1 boundary, exited 0, and restored the terminal.

[established-bounded; formal-checked; process-audit; measured] A cold complete receiver first met
its 180-second outer boundary while rebuilding the workspace compiler population and returned no
partial pass. Its separately bounded test and example sections returned, after which the complete
receiver passed within the boundary: 2,970 tests passed, zero failed, 50 ignored over 35 result
lines; every example target type-checked; the live Lean umbrella built 3,771 jobs; tracked authority,
source shape, epistemic tags, claim index, equation atlas, all ten Typst roots, and document law
passed. Nine gates passed and zero failed.

[established-bounded; process-audit; measured] Root `target/` measured 37 GiB before cleanup.
`cargo clean` removed 17,507 replicable files totaling 39.0 GiB. Root `target/` and `output/` are
absent. The installed user binary remains available.

[open] This correction does not establish unrestricted foreign dismantling, qualitative multimodal
generation, universal engine-owner discovery, or distributed ecology control. It makes the bounded
owners operable; it does not widen them.
