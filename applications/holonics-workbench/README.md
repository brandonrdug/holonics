# Holonics Workbench

Holonics Workbench is the local session and receipt instrument for Athena, Eros, Soulkiller, and
the Holonic Engine. Version 0.3 is session-first: it renders returned causal structure and exact
domain receipts. It is not a file manager or a JSON viewer.

## Install and open

```bash
cargo install --path applications/holonics-workbench --locked
holonics
```

The default Athena surface starts with two actions. Press `Enter` on **Run bounded alpha cycle** to
open source-neutral demo morphology, conduct generation 0, commit one bounded return, and conduct
generation 1. No parameter is required.

## Surface anatomy

The header contains four functional modes:

- `1` Athena: mounted session, lifecycle, successors, exact return, fixed-morphology probes, and
  persistence.
- `2` Eros: typed incidence-atlas and exposure-mouth operations.
- `3` Soulkiller: typed foreign-chart inspection without foreign execution.
- `4` Engine: apparatus, package anatomy, and exact export operations.

Athena shows the current session and circulation stage:

```text
MOUNT → CONDUCT → EMIT → WORLD RETURN → COMMIT
```

The main receipt surface has three projections:

- **Summary**: the consequence, principal state, totals, open fibres, and state effect.
- **Structure**: domain-specific relations and exact tables.
- **Exact**: the complete serialized payload, available as a secondary cold view.

All three views scroll independently from event selection. Scrollbars appear when content exceeds
the viewport. The bottom timeline selects the causal occurrence whose receipt is displayed.

## Keys

- `1`–`4`: switch the actual Athena/Eros/Soulkiller/Engine action surface.
- `[` / `]`: switch mounted Athena sessions.
- `Tab` / `Shift-Tab`: move between actions, receipt, and event timeline.
- `Up` / `Down`: select or scroll one row.
- `PageUp` / `PageDown`: move ten rows.
- `Home` / `End`: first or last row.
- `Left` / `Right`: switch Summary, Structure, and Exact receipt projections.
- `s`, `v`, `x`: jump directly to Summary, Structure, or Exact.
- `Enter`: execute the selected action or open the selected event.
- `?`: contextual help.
- `q`: exit when no operation owns the runtime.

Paths are ordinary typed fields inside open, inspect, atlas, package, and export operations. They do
not occupy a permanent browser or trigger a workspace discovery scan.

## Diffusion presentation

The current diffusion action is deliberately named **Closed unit-law diffusion probe**. It is one
exact source-free fixed-morphology event with:

- the first native spool;
- unit capacity at every native state;
- unit conductance at every incidence occurrence;
- unit content at the first native state;
- the entire native population as the declared receiver boundary;
- empty source; and
- interval `1`.

It does not change the Athena session. Summary reports this explicitly and distinguishes total
incidence branches from nonzero currents. Structure renders oriented branch currents, integrated
transfers, node balances, standing before/after, exact residuals, and exact rational values. A
persistent configurable diffusion simulation is a separate construction, not implied by this
probe.

## CLI and structured I/O

The CLI remains the scriptable face:

```bash
holonics demo
holonics eros atlas .
holonics soulkiller inspect /path/to/config.json
holonics engine package /path/to/snapshot.json
holonics --format json status
```

Human output uses the same typed Summary projections as the TUI. Machine input uses:

```json
{
  "schema": "org.holonics.workbench.request.v2",
  "command": { "domain": "status" }
}
```

Execute it with:

```bash
holonics --format json run request.json
```

Output modes:

- `--format human`: typed domain summaries;
- `--format json`: one `org.holonics.workbench.response.v2` envelope;
- `--format jsonl`: ordered `org.holonics.workbench.event.v3` events.

Runtime refusal exits `1`. Invalid CLI or request input exits `2`. JSON success and refusal remain
the same response shape.

## Capability boundary

The Workbench presents existing owners. It does not implement a second inference, cultivation, or
diffusion law. The bounded alpha cycle and unit-law diffusion probe are apparatus demonstrations,
not qualitative generation or physical calibration claims.
