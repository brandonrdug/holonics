# WB0 Holonics Workbench shared command/event protocol returned

**Date:** 2026-09-01
**Truth status:** `established-bounded` for the application protocol and parser in their declared
command family.
**Evidence:** `implemented-exact`, `source-inspected`, `process-audit`, and `measured`.
**Construction effect:** WB0 passed; WB1 becomes the sole current deed.

## Returned boundary

[established-bounded; implemented-exact] `applications/holonics-workbench` is an independent
workspace application with a `holonics` binary. `WorkbenchCommand` is the one serializable request
family; `WorkbenchEvent` is the one serializable consequence family. Human and JSON Lines output
are pure projections of the same event population.

[definition] The command tree already types Athena live-session operations, Eros mouth/atlas,
Soulkiller configuration/index/ONNX inspection, engine package/export, status, and capabilities.
Application categories remain exterior navigation and do not occur in engine owners.

[established-bounded; implemented-exact] Clap parsing returns `WorkbenchInvocation`; no command is
executed at WB0. Nested commands, exact rational strings including negative values, paths, session
names, receiver/occurrence addresses, export codecs, and output mode are retained in the typed
command. Unknown or incomplete input refuses through Clap instead of being guessed.

[established-bounded; source-inspected] Ratatui 0.30.2 and Crossterm 0.29 are confined to the
workbench manifest. Ratatui's official documentation recommends the main crate for applications,
Crossterm as the default cross-platform backend, and a draw/event loop with automatic restoration
through `ratatui::run`: <https://docs.rs/ratatui/0.30.2/ratatui/>. The TUI will consume the shared
runtime rather than create another command switch.

## Receipt

[established-bounded; process-audit; measured] The initial dependency build and focused command

```text
timeout 180s cargo test -p holonics-workbench --lib
```

completed inside the aperture. Its first result exposed Clap interpreting the negative exact
rational `-1/4` as an option. The exact-rational fields now explicitly admit hyphen values. The
unchanged focused command then returned exit `0` in 0.67 seconds: two passed, zero failed.

[open] WB0 executes no engine deed. WB1 owns only named Athena sessions, exact live commands,
snapshot/remount persistence, diffusion demo, and package export through the existing public API.
