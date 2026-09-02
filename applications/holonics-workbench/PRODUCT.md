# Holonics Workbench product context

## Register

product

## Users

The primary operator is Brandon, working directly in a local terminal on consumer hardware. The
operator is technically capable but should not have to memorize command syntax, engine ownership,
filesystem paths, session addresses, or demo fixtures in order to inspect and exercise Holonics.

## Product Purpose

Holonics Workbench makes the existing Athena, Eros, Soulkiller, and Holonic Engine surfaces easy to
configure, run, compare, and inspect. Success means the terminal application removes
repetitive typing and parameter lookup, maintains useful working context, proposes valid choices
from live repository and runtime state, and returns uniform inspectable receipts. The CLI remains a
scriptable projection of the same operations rather than the interaction model imposed on the TUI.

## Brand Personality

Exact, instrument-like, and alive. The interface should feel like a well-made scientific workbench:
dense where the information is useful, quiet where it is not, and explicit about what will happen.

## Anti-references

- A command prompt embedded inside decorative panes.
- A thin wrapper that makes the operator retype paths, addresses, and parameters already available
  to the application.
- Dashboard chrome, ornamental telemetry, or categories that do not advance an operation.
- Wizard flows that conceal exact parameters or prevent expert inspection and editing.
- Demo labels attached to incomplete command templates which still require undocumented values.

## Design Principles

1. Start from the active holonic session and its returned causal state; request paths only inside a
   named operation that genuinely needs one.
2. Prefer selection, defaults, history, and completion over memorized syntax.
3. Keep exact values visible and editable without making raw syntax the primary interaction.
4. Return one consistent event/receipt envelope across CLI, TUI, success, refusal, and long work.
5. Make the first useful deed executable immediately from an empty state, then present its domain
   consequence before its serialized wire.

## Accessibility & Inclusion

The complete workflow is keyboard-operable, does not depend on color alone, remains legible in
common 80-column terminals, exposes plain-text status and errors, and supports noninteractive JSON
output for assistive and scripted use.
