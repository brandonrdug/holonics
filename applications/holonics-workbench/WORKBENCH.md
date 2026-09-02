# Holonics Workbench — one operator surface for the engine ecology

**Date:** 2026-09-01
**Kind:** active application contract composed by
[`../../blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md).
**Current position:** WB4.

## 0. Product boundary

[definition] Holonics Workbench is an exterior operator application. It is not an engine blueprint,
native ontology, scheduler, model manager, or second implementation of any deed. It composes public
owners and presents their exact returns through one typed interface.

[definition] The operational invariant is:

```text
WorkbenchCommand -> WorkbenchRuntime -> List WorkbenchEvent.
```

The CLI parses arguments into `WorkbenchCommand`. The Ratatui terminal UI edits and submits the
same command values and renders the same event values. Neither presentation shells to the other,
invokes historical examples as implementation, or carries hidden inference logic.

[definition] Application categories are navigation only:

- **Athena:** live morphology sessions, conduct, actual continuation, exterior return,
  commit/decline, diffusion, snapshot/remount, package inspection, and export;
- **Eros:** exposure-driven codec recovery and material incidence/face inspection through existing
  `life` owners;
- **Soulkiller:** lossless configuration, shard-index, and ONNX chart inspection plus explicitly
  labeled bounded demo admission through the sole dismantling boundary;
- **Engine:** apparatus status, supported command capability/open-fibre display, native package
  anatomy, exact export, and exact diffusion testimony; and
- **Workbench:** session/store navigation, command history, structured output, and help.

These labels never select native transport. Every command names its actual source owner and returns
an obstruction when that owner cannot perform it.

## 1. Shared command and event protocol

[definition] `WorkbenchCommand` is a serializable exterior request family. `WorkbenchEvent`
contains severity, subject, summary, and an optional structured JSON payload. Events are append-only
within one application run and may be written as JSON Lines. Human rendering is a projection of
the event; it cannot change the command consequence.

[definition] Commands initially admitted are:

```text
status
capabilities

athena demo-open SESSION
athena open SESSION SNAPSHOT
athena inspect SESSION
athena conduct SESSION SPOOL THREAD OCCURRENCE RECEIVER
athena continue SESSION SUCCESSOR_INDEX
athena return SESSION OCCURRENCE BOUNDARY REAL IMAG STORAGE
athena decline SESSION
athena diffuse-demo SESSION OCCURRENCE INTERVAL
athena snapshot SESSION PATH
athena export SESSION {onnx|safetensors} PATH

eros mouth DIRECTORY EXTENSION RADIUS SCALES OCTET_BUDGET
eros atlas DIRECTORY EXTENSION OCTET_BUDGET

soulkiller config PATH
soulkiller index PATH
soulkiller onnx PATH

engine package PATH
engine export PACKAGE {onnx|safetensors} PATH.
```

[definition] “Demo” is explicit wherever the application supplies a bounded fixture or uniform
capacity/conductance realization. Demo material never becomes a capability gate and cannot be
mistaken for unrestricted Soulkiller or physical diffusion.

## 2. Runtime and persistence

[definition] One `WorkbenchRuntime` owns live named Athena applications and the latest returned
boundary per session. Session names are operator handles only. Conduct uses explicit native
addresses. Continue accepts only an actual successor returned by the preceding boundary. Return
uses that exact emission. Commit and decline consume and replace the session owner atomically.

[definition] Persistent artifacts are explicit paths supplied by the operator:

- native morphology package wire;
- circulation snapshot wire;
- exact export artifact; and
- optional JSONL event transcript.

Paths are exterior carriage and lineage, not native identity. No content-addressed store, checksum
registry, workspace census, or hidden default corpus is introduced. Parent directories may be
created only for an explicit output path.

## 3. CLI

[definition] The `holonics` binary uses Clap only to parse operator input. With a subcommand it
executes one command and prints human or JSON output. With `tui` or no subcommand on an interactive
terminal it enters the terminal UI. CLI help is generated from the same admitted command family;
unsupported engine owners are displayed as open, not stubbed with plausible output.

[definition] One-shot CLI invocations are naturally stateless. Long-lived multi-step Athena
interaction is available in the TUI, or through explicit snapshot/open commands across invocations.

## 4. Ratatui terminal interface

[definition] Ratatui 0.30.2 is an immediate-mode renderer. Crossterm supplies terminal events. The
TUI owns only presentation state:

```text
top      category tabs and active sessions
left     command catalogue
center   event summaries and causal chronology
right    selected structured payload / package anatomy / boundary fibres
bottom   command palette, status, and key help.
```

[definition] `:` focuses the command palette; `Enter` parses and executes through the shared
runtime; `Tab` changes panes; arrows move selection; `Esc` clears/closes overlays; `q` exits only
when the palette is not editing. Terminal restoration occurs on ordinary exit and error.

[definition] Rendering is pure over `WorkbenchView`. A headless `TestBackend` control proves the
same view can render without a real terminal and that command execution is independent of frame
size, color, selection, or focus.

Ratatui's official application guidance recommends the main `ratatui` crate, Crossterm as the
default cross-platform backend, a draw/event loop, and automatic terminal restoration through
`ratatui::run`; those are adopted as apparatus practice, not engine law.

## 5. Ordered construction

### WB0 — shared typed protocol and application architecture — PASSED

[definition] Deposit this contract, add the independent application crate, and return serializable
commands/events, runtime error/refusal, deterministic human/JSON rendering, and command parsing
without executing a deed.

**Pass WB0:** [definition] CLI and TUI types depend on one command/event owner; no application
category appears in engine crates; command serialization round-trips; malformed command input
refuses; document/source-shape checks pass.

[established-bounded; implemented-exact; source-inspected; measured] WB0 returned the independent
application crate, complete serializable command/event protocol, nested Clap parser, human/JSONL
renderers, negative exact-rational handling, round-trip and malformed-input controls. Two focused
tests passed. Its receipt is
[`../../research/records/2026-09-01_WB0_HOLONICS_WORKBENCH_SHARED_COMMAND_EVENT_PROTOCOL_RETURNED.md`](../../research/records/2026-09-01_WB0_HOLONICS_WORKBENCH_SHARED_COMMAND_EVENT_PROTOCOL_RETURNED.md).

### WB1 — Athena runtime, sessions, store, and export — PASSED

[definition] Compose the released Athena-alpha API into named live sessions and explicit
snapshot/package/export paths.

**Pass WB1:** [definition] demo-open, inspect, conduct, actual continue, later return/commit,
decline, exact diffusion demo, snapshot/open, and exact ONNX/Safetensors export use public owners;
one multi-step runtime control remounts and continues; false successor, missing boundary, missing
session, and unsupported export refuse.

[established-bounded; implemented-exact; source-inspected; measured] WB1 returned named live
sessions, explicit conduct/continue, recoverable return/commit, decline, uniform exact diffusion
demo, snapshot/open, anatomy inspection, and exact export. The positive and refusal controls
returned two passed tests. Its receipt is
[`../../research/records/2026-09-01_WB1_WORKBENCH_ATHENA_SESSIONS_COMMIT_DIFFUSION_SNAPSHOT_AND_EXPORT_RETURNED.md`](../../research/records/2026-09-01_WB1_WORKBENCH_ATHENA_SESSIONS_COMMIT_DIFFUSION_SNAPSHOT_AND_EXPORT_RETURNED.md).

### WB2 — Eros, Soulkiller, engine adapters and CLI — PASSED

[definition] Add read-only Eros material mouth/atlas summaries, lossless Soulkiller exterior-chart
inspection, engine status/capability/package/export surfaces, and the Clap command tree.

**Pass WB2:** [definition] every command returns structured events; Eros calls existing codec and
incidence owners; Soulkiller inspection retains unknown/raw material and executes no foreign model;
engine package/export round-trips exactly; `holonics --help` exposes the complete admitted surface;
and CLI JSON equals direct runtime events.

[established-bounded; implemented-exact; source-inspected; measured] WB2 returned Eros mouth/atlas,
lossless Soulkiller config/index/ONNX inspection, engine status/capabilities/package/export, and
actual human/JSONL CLI execution. Direct and CLI status events agree; two focused integration tests
passed. Its receipt is
[`../../research/records/2026-09-01_WB2_EROS_SOULKILLER_ENGINE_AND_CLI_RETURNED_ONE_EVENT_SURFACE.md`](../../research/records/2026-09-01_WB2_EROS_SOULKILLER_ENGINE_AND_CLI_RETURNED_ONE_EVENT_SURFACE.md).

### WB3 — Ratatui interface over the same runtime — PASSED

[definition] Add the interactive terminal loop, catalogue, event timeline, payload inspector,
command palette, session status, help, and deterministic headless rendering.

**Pass WB3:** [definition] the TUI executes commands through `WorkbenchRuntime::execute`; no shell
subprocess or duplicate command switch exists; terminal restoration is guaranteed; headless render
and key/update controls pass; a scripted TUI command sequence returns the same events as direct
runtime execution.

[established-bounded; implemented-exact; source-inspected; measured] WB3 returned the Ratatui
layout, command palette, event timeline, payload inspector, session/status surface, Crossterm
updates and auto-restoring event loop. Direct/TUI equality, key/update, and two headless terminal
sizes returned three passed tests. Its receipt is
[`../../research/records/2026-09-01_WB3_RATATUI_RENDERED_THE_SAME_WORKBENCH_COMMAND_EVENTS.md`](../../research/records/2026-09-01_WB3_RATATUI_RENDERED_THE_SAME_WORKBENCH_COMMAND_EVENTS.md).

### WB4 — operator documentation and coherent application release

[definition] Document install/build, CLI and TUI entry, first-session walkthrough, artifact
locations, commands, controls, hardware expectations, and exact capability boundaries. Run the
real CLI and a pseudo-terminal TUI smoke deed, then the affected package and coherent repository
release receivers.

**Pass WB4:** [definition] the workbench is runnable as `holonics`; the documented Athena, Eros,
Soulkiller and engine walkthroughs return; CLI/TUI share exact command consequences; no generated
surface is graded; the release passes within 180 seconds; Git is clean and pushed; and reproducible
`target/`/`output/` material is absent.

## 6. Scope

[definition] WB0--WB4 build operator convenience only. They do not widen Athena capability,
complete unrestricted Soulkiller dismantling, refound Eros, add a general engine plugin registry,
schedule UI/web work, or promote a qualitative output. A callable owner absent from this first
surface remains an explicit future application extension, not a missing engine organ.
