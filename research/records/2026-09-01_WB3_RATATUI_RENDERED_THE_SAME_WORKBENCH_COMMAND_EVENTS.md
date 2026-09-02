# WB3 Ratatui rendered the same Workbench command events

**Date:** 2026-09-01
**Truth status:** `established-bounded` for the Ratatui view/update/event loop and shared-runtime
equality in their declared terminal controls.
**Evidence:** `implemented-exact`, `source-inspected`, `process-audit`, and `measured`.
**Construction effect:** WB3 passed; WB4 becomes the sole terminal deed.

## Returned terminal application

[established-bounded; implemented-exact] `WorkbenchTui` owns only presentation state: command
input, pane focus, catalogue/event selections, status and quit condition. It owns one
`WorkbenchRuntime`. `submit_line` uses shell-like token separation only to create the same Clap
argument vector as the CLI; the parsed `WorkbenchCommand` enters `WorkbenchRuntime::execute`
directly. The TUI never invokes the CLI binary or another subprocess.

[established-bounded; implemented-exact] The Ratatui view returns category tabs, command catalogue,
causal event timeline, structured payload inspector, command palette, active session list, status
and key help. Immediate rendering is pure over the application view. A 60x16 terminal and a 120x36
terminal render through `TestBackend` with the same command consequences.

[established-bounded; implemented-exact] Crossterm key updates open/cancel the palette, edit exact
command text, execute on Enter, traverse panes/selections, and quit only outside editing. The
interactive loop uses `ratatui::run`, which initializes and restores the terminal on ordinary exit
and error according to the Ratatui 0.30.2 application contract.

## Receipt

[established-bounded; process-audit; measured] The focused command

```text
timeout 180s cargo test -p holonics-workbench --lib tui:: -- --nocapture
```

returned exit `0` in 4.85 seconds: three passed, zero failed. Direct-runtime and TUI `status`
events are exactly equal; the palette/key sequence executes `capabilities`; and headless small/large
terminal buffers contain the expected Holonics and capability surfaces.

[open] WB3 establishes the TUI mechanism, not a qualitative interface grade. WB4 owns the operator
guide, real CLI walkthroughs, pseudo-terminal smoke, complete workbench tests, coherent release,
cleanup and final position.
