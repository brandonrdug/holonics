# Worker context, ownership and verification

[definition] A worker receives enough mathematical and repository context to construct its part
of the actual consuming operation. It uses [THE_MACHINE](THE_MACHINE.md), its harness guide and
the specific source/record links supplied by the primary. The primary retains the full user
objective, roadmap and integration responsibility.

## The brief every worker starts with

[project-postulate] Name [AGENTS.md](../AGENTS.md) for a Codex worker or [CLAUDE.md](../CLAUDE.md)
for a Claude worker and the relevant machine/source sections. The worker reads them if they are
not already present at the current revision. Explicit context in the task is reliable across
harness differences; an assumed automatic load is not evidence that the needed material arrived.

The primary supplies:

- The requested object/consequence and how this subtask contributes to it.
- Known operands, inferred unknown, equation, hypotheses and retained residual.
- Exact owning paths, existing formal/native owners and the consuming call.
- Governing research records and applicable direct corrections, with useful content summarized.
- Issues advanced, current source revision and relevant verification receipts.
- The permitted checks and the concrete result to return.

[definition] For example, a normalized-section task starts with the scalar normalized owner,
its softmax differential, the row/grain/radius ABI and the field-session call that will use its
output. “Implement normalization” without those operands invites a duplicate algorithm.
A sealed packet's equal low/high carrier words can contain a nonzero radius; read the actual
representation before turning a comparison into a mathematical claim.

## Split by dependencies and owned paths

[project-postulate] Codex uses Luna workers. Claude uses at most three Opus 5 constructing workers
on disjoint paths, followed by one Sonnet 5 reviewer that spawns nothing. Use fewer when the work
does not split; make a join sequential when it consumes prior returns. A request to work without
agents takes precedence. Root owns source inspection and integration of every returned change.

[project-postulate] All workers share this checkout and Cargo's `target/`. Edit and format only
the named paths. Preserve every other diff and local file. A broad restore/reset/stash/clean is
not cleanup: it can remove another worker's or the user's work. Coordinate a needed shared-file
edit with the primary; do not assume absence from your assignment means absence from the task.

| Actor | Relevant checks |
|---|---|
| Constructing worker | Module tests and local compilation for owned paths; one changed Lean target and axiom prints when needed |
| Reviewer | Source/caller inspection; a distinguishing probe for a concrete unresolved suspicion; existing receipts supply unchanged measurements |
| Primary | Checks of the combined changed scope and actual consumer; coordinated device checks when native behavior changes; issue/state/source integration and commit |

[definition] GPU checks run under one coordinated device owner, with actual device usage checked;
a lock only coordinates processes taking it. Broad Cargo, device and complete formal runs are
assigned by the primary, rather than launched independently by every worker. A later isolated
correction needs its changed scope, not an automatic replay of all earlier checks.

<a id="before-writing-that-something-is-absent-and-before-founding-anything"></a>

## Use existing mathematics

[project-postulate] Search both the subject and its method before declaring an absence or
founding an owner:

```bash
.agents/bin/prior-art 'subject|LeanName|rust_name|classical term'
rg --files research/records | rg -i 'subject|alternate spelling'
rg -n '<operation>' docs/ARCHITECTURE_MAP.md
```

Read the returned record and actual owner/caller. A hit identifies construction to inspect; a
matching name alone neither supplies the map nor proves it missing. The
[research routes](../research/records/README.md) recover the positive source context. An
interpretation is developed through a derivation, counterexample or explicit failed equation.

[definition] Resolve routine choices from the mathematics and context and record their reason
as `agent-inferred`. Carry the source, frame, units, phase, supplied/inferred distinction and
relevant uncertainty through the implementation. Mathematical learning/inference does not need
an added qualitative test. Preserve the future-receiver equation for any compression claim and
the original producing material for its adjoint.

## Receipts

[definition] [VERIFICATION_RECEIPTS.tsv](VERIFICATION_RECEIPTS.tsv) records actual completed checks:
`when, tree, dirty, scope, command, result, secs, who, log`. A worker's measurement is reusable
for unchanged source; its judgement is checked against the owner and consumer. Record real
commands and distinguish source/reference inputs, runtime/device placement and omitted cases.

```bash
cargo test -p <crate> --lib <module>::
cargo check -p <crate> --lib
bash tools/lean_check.sh ElementaryHolonics.<ChangedOwner>
```

`lake build` and the helper's no-argument default build `ElementaryHolonics.Framework`.
`ElementaryHolonics` explicitly selects the complete research umbrella. A completed build
validates the chosen imports; a timeout is incomplete evidence. Do not turn a filename or
aggregate test count into a larger capability claim.

## Prompt and return shape

```text
Read: <harness guide, machine sections, research record and source owners>.
User's object and purpose: <requested consequence>.
Your paths: <exact owned set>; other workers' changes remain untouched.
Equation: <known operands, unknown, law, hypotheses, receiver, residual>.
Consumer: <actual call and required returned value>.
Issues: <numbers and concrete scope>.
Checks: <assigned commands>; existing receipts: <links/revisions>.
Return: changed paths, derived/implemented result, exact checked scope, remaining equation,
        receipt lines and issue disposition. Report any needed cross-owner edit to root.
```

[project-postulate] The primary integrates the returned source and its consumer, updates the
owning guide/research links and issue body, and records the next action in CONSTRUCTION_STATE.
This is the construction's ordinary follow-through, not another approval ceremony.
