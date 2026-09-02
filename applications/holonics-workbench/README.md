# Holonics Workbench

Holonics Workbench is the local operator application for Athena, Eros, Soulkiller, and the Holonic
Engine. The terminal UI is selection-driven. The CLI is the scriptable face of the same typed
operations and receipts.

## Install and open

From the repository root:

```bash
cargo install --path applications/holonics-workbench --locked
holonics
```

The initial selection is **Guided start**. Press `Enter`, then `Enter` again on **Run complete Athena
demo**. The demo requires no session name, path, spool, thread, occurrence, receiver, successor, or
current values. It:

1. opens bounded source-neutral demo morphology;
2. derives the first valid package ingress and receiver;
3. conducts generation 0;
4. commits an explicitly labeled bounded return; and
5. conducts the changed generation 1, leaving a live boundary to inspect or continue.

Pressing `d` runs the same demonstration immediately.

## Terminal workflow

The interface follows one progression:

```text
select a resource -> choose an action valid for it -> inspect returned events and exact detail
```

The Resources pane contains:

- Guided start;
- every live Athena session;
- the current directory;
- subdirectories; and
- recognized model configurations, Safetensors indexes, ONNX files, circulation snapshots, and
  morphology packages.

Directory selection provides Eros atlas, material-mouth, and resource-discovery actions. Model
artifacts provide the applicable Soulkiller inspection action. Snapshots and packages provide
remount, anatomy, and exact export actions. Session actions are derived from actual runtime state:
conduct is offered only from a real ingress and receiver; continuation is offered only when a
returned actual successor exists; every actual successor is separately selectable; return/decline
are offered only while a live boundary exists. Exact world returns can use a typed form whose
occurrence, boundary, real/imaginary current, and storage fields are visible and editable. Bounded
demo sessions receive valid suggestions; remounted morphology requires genuine exterior values
rather than application-invented defaults.

No path needs to be typed. Use `w` for the workspace root, `h` for the home directory,
`Backspace` for the parent, and `Enter` to open a selected folder. Snapshot and export actions show
their complete destination before execution and choose the next non-overwriting filename under:

```text
~/.local/share/holonics-workbench/SESSION/
```

### Keys

- `Up` / `Down`: select a resource, action, or event.
- `Enter`: open a directory, focus its actions, or execute the selected action.
- `Tab`, `Left`, `Right`: move between resources, actions, events, and exact detail.
- `Backspace`: move to the parent directory.
- `w`: return to the workspace root.
- `h`: open the home directory.
- `d`: run the zero-parameter Athena demonstration.
- `r`: refresh visible resources.
- `q`: exit when no operation is in flight.

Potentially slow Eros, Soulkiller, package, export, and CUDA operations run off the rendering thread.
Navigation and event inspection remain responsive while the operation owns the runtime. A second
mutation cannot begin until that runtime returns.

## Convenient CLI

The same zero-parameter demo is available without the TUI:

```bash
holonics demo
```

Discover supported resources without constructing paths manually:

```bash
holonics discover
holonics discover /another/root
```

Eros chooses the dominant Rust, Lean, or Markdown material automatically and defaults to the
current directory:

```bash
holonics eros atlas
holonics eros mouth
holonics eros atlas crates/holonic-engine
```

Soulkiller can classify a selected supported chart from its filename:

```bash
holonics soulkiller inspect /path/to/config.json
holonics soulkiller inspect /path/to/model.safetensors.index.json
holonics soulkiller inspect /path/to/model.onnx
```

The explicit Athena and engine subcommands remain available for scripts which already possess exact
addresses or paths. Run `holonics --help` or `holonics DOMAIN --help` for those expert surfaces.

## Standard input and output

Every structured request uses one versioned envelope:

```json
{
  "schema": "org.holonics.workbench.request.v1",
  "command": { "domain": "status" }
}
```

Execute it from a file or standard input:

```bash
holonics --format json run request.json
printf '%s' '{"schema":"org.holonics.workbench.request.v1","command":{"domain":"status"}}' \
  | holonics --format json run -
```

Output modes are:

- `--format human`: readable event summaries and payloads;
- `--format json`: one `org.holonics.workbench.response.v1` envelope with disposition and events;
- `--format jsonl`: one versioned event per line for streaming consumers.

Runtime refusal exits `1`. Invalid CLI or request input exits `2`. In JSON mode, success, runtime
refusal, malformed CLI input, and malformed request input all return the same response envelope on
standard output.

## Capability boundary

The Workbench exposes existing owners. It does not implement a second inference or training law.
The guided demo is bounded material, not a qualitative language capability claim. Soulkiller
inspection retains foreign charts without executing them. Resource discovery is an ephemeral
operator view over explicitly visited roots; it is not a repository catalog, semantic identity, or
model registry.

Still open:

- unrestricted dismantling of arbitrary foreign model directories;
- useful qualitative text, image, or audio generation;
- automatic discovery of every engine owner; and
- distributed multi-instance ecology control.
