# Rust boundary runner

> **HISTORICAL INSTRUMENTATION.** `life boundary` preserves application and observation campaigns,
> but it is not the production owner of Eros. The current transition is
> `current_world -> LiveCurrentMachine::receive_with -> host|CUDA executor -> successor -> radiation`.
> See the repository-root `LABORATORY_REVIEW.md` before treating any boundary mode as current.

`life boundary` is the reusable application/observation surface around the existing CUDA
continuation, SLEEP, compact radiation wire, and source provenance. It conducts every declared
edge in one Rust process. A successor body moves into the next edge without cloning; every edge is
also persisted create-new before continuation.

## Run a lifecycle

```text
life boundary plan.json
```

Plan schema (unchanged at v1; receipt/session schemas are v2 once native construction wires are
present):

```json
{
  "schema": "soma-boundary-plan-v1",
  "output": "results/session-01",
  "start": { "kind": "empty" },
  "edges": [
    { "kind": "material", "paths": ["light-a.txt", "light-b.txt"] },
    { "kind": "eye", "manifests": ["world.eye"] }
  ]
}
```

An existing canonical body may replace the empty start:

```json
"start": { "kind": "archive", "path": "prior.body" }
```

Relative paths resolve from the plan's directory. The output directory is create-new. Each edge
writes:

- `edge-NNN.body` — canonical successor SLEEP;
- `edge-NNN.radiation` — every exact raw radiation row;
- `edge-NNN.construction` — compact spans over Soma's native plural constructions, each pointing
  directly into the radiation wire by lineage, event, and row; CUT alone closes and open tails
  remain open;
- `edge-NNN.json` — source ranges, session lineage ordinals, axes, topology, term faces, phase
  timings, device, and artifact paths.

`session.json` names the ordered receipts and final body. The JSON receipt is listener provenance;
the complete body and radiation remain authoritative beside it.

## Active current versus durable record

Plan, manifest, journal, receipt, and observer JSON belong to the durable world/listener boundary.
They are not automatically active light. A world consequence crosses the code-workshop membrane
through `soma-abi::current::EventHeader`: one world-local event tag, exact payload-word extent, and
an explicit ordered value payload. Rust field names, enum names, schema keys, paths, labels, and
punctuation remain outside the current unless they are themselves the material value being
presented.

Raw source and candidate material remain byte-for-byte raw. Typed consequences retain the exact
values needed by their concrete receiver. A shared face may stand once while distinct physical
incidences remain separate current lineages. The corresponding durable journal must retain the
complete provenance and the typed surface must reconstruct the checked world consequence exactly.
World-local tags are I/O coordinates, never global Soma categories or an authored taxonomy.

Lineage ordinals are continuous within one boundary session. Starting from an archive begins a new
listener session at ordinal zero because historical Mail never entered the sleeping body; exact
source paths and source ranges remain in every edge receipt.

The current runner uses the exact-gated observed-sharded CUDA mouth. Whole lineage transactions
remain intact while card-derived cohorts cross allocation and descriptor-wire walls; every raw
radiation row and the one global receiving edge remain unchanged. Direct archive carriage remains
the known scale implementation seam; it will change body materialization, not this ownership or
receipt contract.

The streaming mouth reconstructs receiving-edge Mail by reopening one completed cohort at a time.
It validates each canonical lineage-local REGISTER, compacts its exact live cells, emits the
accepted landing letters, and dissipates that cohort before reading the next. No host-wide OWN
aggregate is rebuilt. The durable Mail retains repeated landings; its exact host/CUDA gauge sorts
each lineage's grip multiset only to remove container iteration order, never multiplicity.

The construction wire is a listener index, never another body or output phenotype. Its fixed
eight-`u64` record is:

```text
local lineage · session lineage ordinal · event start · event end
· radiation row start · radiation row count · STEP count · OPEN/CLOSED
```

Every referenced row remains verbatim in the radiation wire. A concrete world may stream these
spans through its own material contacts; no keyboard, text canvas, renderer, or simulation is
promoted to the universal mouth.

## Conduct a plural circuit world

```text
life boundary circuit plan.json
```

The strict `soma-circuit-boundary-plan-v1` schema declares one resting Soma body, one empty or
previously persisted circuit world, one plural material stimulus, and one or more world-return
edges:

```json
{
  "schema": "soma-circuit-boundary-plan-v1",
  "output": "results/session-i",
  "body": { "kind": "empty" },
  "world": { "kind": "empty" },
  "edges": [
    { "kind": "stimulus", "paths": ["theory.txt", "code.rs"] },
    { "kind": "return" }
  ]
}
```

For a Codex JSONL container, `kind: "dialogue"` invokes the exact text-dialogue organ instead of
feeding the container syntax. It presents each actual `user_message` and assistant `message` as
one complete current in record order. Developer scaffolding, tool receipts, reasoning records,
JSON syntax, and the duplicate response-item spelling of a user message remain world-side. The raw
container path and record range remain in listener provenance; no role label enters the light.

Dialogue and other material may cross as one genuinely co-present configuration without flattening
their source boundaries:

```json
{
  "kind": "configuration",
  "sources": [
    { "kind": "dialogue", "path": "conversation.jsonl" },
    {
      "kind": "dialogue_continuation",
      "path": "conversation-later.jsonl",
      "after": "conversation.jsonl"
    },
    { "kind": "material", "path": "boundary.rs" },
    { "kind": "material", "path": "arrow.rs" }
  ]
}
```

Each dialogue message and each non-JSONL file remains one complete current; directories retain
their complete file worldlines. Source declarations retain caller order, while the receiving
configuration fold remains permutation gauge. No concatenation, authored chunk, separator, role
label, or container syntax enters the light.

`dialogue_continuation` admits only records genuinely appended after one exact prior container.
`after` must be a newline-closed proper prefix of `path`; the organ verifies every prefix octet and
retains the later records' original ordinals and raw ranges. This is an append-only world edge, not
a message selector or an authored chunk.

A completed circuit edge can resume from its durable body, world state, and returned-current wire
without replaying its cause:

```json
{
  "body": { "kind": "archive", "path": "edge-001.body" },
  "world": { "kind": "state", "path": "world-001.state.json" },
  "edges": [
    { "kind": "current_wire", "path": "edge-001.return", "caused_by_edge": 1 }
  ]
}
```

The current wire is only a reversible boundary container. Its header and extents are removed before
delivery; every enclosed world return remains one complete later current. The declared cause fixes
the continued edge ordinal and enters the receipt, never the light.

A returned circuit field may also cross one ordered reversible world periplus before it returns to
Soma:

```text
life boundary circuit-periplus periplus-plan.json
```

The strict `soma-circuit-periplus-plan-v1` reopens one exact source edge and carries every acted
source→endpoint relation through every declared world contact. Each emitted current contains the
complete source, branch, and endpoint forms plus their relative displacement at every lived
contact. Absolute grips and transform names remain receipt-only. The receipt retains every
trajectory, checks the exact source field, reverses the whole passage, and reopens its current wire
exactly. `kind: "world_passage"` supplies that current and receipt to `circuit`; its
`caused_by_edge` fixes the genuinely later edge ordinal. No relation, route, or endpoint is chosen.

An archive may replace the empty body and a prior `world-NNN.state.json` may replace the empty
world. Every complete enclosure lands in the declared circuit world: its completion grip supplies
the incident pole and its grounded completed brick supplies the far contact. An absent branch
FOUNDs material; a standing branch RIDEs it. Only each changed far-port regional form becomes the
next current. Receipt metadata never enters that light.

Each edge writes the canonical body, raw radiation, native construction wire, complete completion
wire, circuit-return wire, successor world state, and one receipt joining the causal extents. The
world transition is reversed and compared to its exact input state before the successor stands.
The measured construction and authoritative plans are under
`observations/circuit-medium-01/`.

A completed card edge may cross the same receiving seam from its durable radiation and completion
apertures without replaying the body:

```text
life boundary circuit-receive receive-plan.json
```

The strict `soma-circuit-receive-plan-v1` plan names the prior world state, matching radiation and
completion wires, later edge ordinal, and a create-new output. The radiation header supplies the
receiving axis; the completion header supplies the lineage frame. The command performs the same
world receive, exact inverse gate, return-current emission, and successor-state persistence as the
closed runner. It is the durable boundary seam, not a second world mechanism.

The exact circuit state may be read structurally without changing or re-feeding it:

```text
life boundary circuit-observe world-NNN.state.json topology.json
```

The observer retains the state as authority and reports the complete directed-degree,
`RegionalForm`-face, connected-region, closed-directed-region, and branch-pole distance
histograms. These are listener reads only; no graph, component, distance, or category enters Soma
or the circuit transition.

The causal source ecology of one or more already-completed circuit edges can be read without
replaying either Soma or the world:

```text
life boundary circuit-ecology-observe ecology-plan.json ecology.json
```

The strict `soma-circuit-ecology-observer-plan-v2` names one or more causally continuous passages.
Each passage names its external-light source plan and every exact prior/successor world, radiation,
and completion artifact. The first passage begins from an empty world; each later passage must begin
from the byte-exact world completed by its predecessor. The observer reconstructs a causal material
net across that whole history, propagates it through returned fields, and reports arriving,
already-standing, and successor material separately for exact FOUND/RIDE witnesses. Thus a RIDE can
name both the new event and the older source-current/event material responsible for the branch it
traversed. Declared excerpts and witnesses are bounded listener grains. Event windows point into
the delivered current after the passage; they do not divide staging. Source kinds, paths, text,
causal ancestry, and taxonomic names remain listener provenance and never enter Soma or the circuit
world.

`circuit-contact-observe` also accepts a periplus as the first edge of a causally continued
passage. A top-level `"trace": "summary"` retains the complete reconstruction, inverse, return,
and causal counts while omitting the per-segment JSON repetition from the listener artifact. The
default remains `"complete"`. This changes only observer retention; every transition and ancestry
mask is still visited.

The native construction stream of a heterogeneous first edge can be articulated against the exact
source plan which staged it:

```text
life boundary circuit-articulate source-plan.json edge.construction output.txt
```

Every OPEN/CLOSED construction remains in lineage/event order with its exact radiation extent and
STEP count. The listener prints the complete source interval with reversible ASCII escaping. It
does not reduce the stream to a keybar, choose one construction, or manufacture text; source and
construction provenance remain beside the presentation. Returned circuit currents are transported
regional forms rather than source text, so their lawful human read is the causal ecology observer
above, which follows their origin ancestry through the changed world.

## Conduct an exact mathematical derivation world

```text
life boundary proof plan.json       # exact host/CUDA validation grade
life boundary proof-cuda plan.json  # immutable-source gate, then CUDA-forward
```

Both commands enact the same proof-world law and write the same mathematical listener species.
Their receipts distinguish `host_cuda_gate` from `cuda_forward`. The validation grade constructs
the complete host sibling and owes host/CUDA identity. The forward grade does not duplicate every
edge on the CPU and never claims unmeasured host equality. Use the former to establish or re-gate
an apparatus seam; use the latter to continue an already-gated world.

The strict `soma-proof-boundary-plan-v1` runs one persistent mathematical world through the same
owned CUDA body lifecycle. Its first calibration species is exact Möbius cross-ratio invariance over
normalized complex rationals and the projective point at infinity. The world may expose a direct
difference-factor construction, translation/scale/inversion generator constructions, closing
operations, and explicit controls. These are world affordances, not answers installed in Soma.

The original `ports` edge is a calibration aperture: one generated branch/candidate port is one
complete staged lineage, and every enclosure completion emitted by it contacts that port. It is
retained for exact comparison, but its branch-by-candidate source expansion is not the active scale
species.

`natural_ports` presents the theorem once, every standing branch once, and every admitted gear
once. After Soma conducts those intact plural currents, the listener reads their actual Mail. One
world relation exists only at a grip occupied by all three lineages—**theorem ⊕ branch ⊕ gear**—and
the journal retains the complete common grip field and all three causal lineages. Mail multiplicity
remains authoritative beside this receiver; the relation currently takes the occupied-grip set as
its declared contact grain. No product is staged, no completion is crowned, and no score, hash,
address lookup, or selected endpoint chooses a relation.

The exact world checker then applies each contacted affordance once, recording an accepted exact
transition or typed refusal. This is proof-world physics, not evidence that Soma internally chose
the rule or performed the check; proof-world `FOUND`/`RIDE` names world support bookkeeping only.
Distinct common fields remain distinct in the journal and returned material even when the current
world physics uses only their nonempty contact face. Identical successor values retain their
distinct causal paths.

Every port edge persists the complete canonical port manifest, world-before, raw radiation,
completion wire, native construction wire, transition journal, world-after, and exact world-return
wire. The journal must retreat byte-exactly to the world-before before the successor stands. The
complete journal is the laboratory witness; durable proof-return wire v2 carries the world's
material consequence as genuinely later light:

- one accepted current carries the complete successor branch, its support aftermath, and its
  `FOUND`/`RIDE` deed;
- one refused current carries the complete source branch, attempted gear, and typed reason; and
- an uncontacted relation emits no current.

State-root and journal commitments, complete frontier/support enumerations, completion summaries,
contact lineages, and grip arrays remain in the exact listener record rather than crossing again as
semantic light. The framing reader retains exact v1 readability while new writes use v2. It never
splits one delivered source, and the plural mouth refuses fewer than two real consequences instead
of manufacturing filler. The return must cross before another port aperture may open; a session
cannot end with that return pending.

The deterministic observer joins an existing v2 wire to the exact return-edge receipt without
entering Soma or the proof world:

```text
life boundary proof-consequence-observe edge.return return-edge.json consequence-report.json
```

It validates ordered source/light correspondence and the lineage-local completion cover, then
retains every current while grouping accepted faces by deed/support/successor stage and refused
faces by reason/source stage/attempted gear. The report is create-new observer testimony; it does
not drive a transition or choose a consequence.

No resource forecast is authored in the plan. Before either execution grade conducts, an
immutable-source gate derives checked lower bounds directly from the actual complete currents,
prior standing axis, contemporary host memory, device memory/allocation grain, and disk. A refusal
lands there before construction and does not shrink, split, retry, or substitute the passage.

Under `proof`, the engine next derives the exact host successor and every completion row. From
those exact surfaces it forecasts the world transition, listener artifacts, return wire, receipt
envelopes, and complete host/device/disk overlap. The host forecast is dissipated before CUDA. The
full preflight then either admits the intact edge or names every exceeded boundary, and a passing
edge owes host/CUDA identity. Under `proof-cuda`, the admitted intact passage conducts directly on
CUDA and owes its CUDA body, completion cover, world transition, return, listener extents, and
SLEEP archive exactly; host-forecast fields remain absent. These receipts describe their actual
apparatus cuts, not engine-wide caps.

The theorem and candidate fields are exact tagged values. A complete port edge contains only the
mathematical problem and the world affordances to present:

```json
{
  "kind": "ports",
  "label": "direct and generator relations",
  "problem": {
    "id": "mobius-a",
    "notation": "CR(Tp,Tq;Tr,Ts)=CR(p,q;r,s)",
    "transform": {
      "a": { "real": { "numerator": 2, "denominator": 1 }, "imaginary": { "numerator": 0, "denominator": 1 } },
      "b": { "real": { "numerator": 1, "denominator": 1 }, "imaginary": { "numerator": 0, "denominator": 1 } },
      "c": { "real": { "numerator": 1, "denominator": 1 }, "imaginary": { "numerator": 0, "denominator": 1 } },
      "d": { "real": { "numerator": 1, "denominator": 1 }, "imaginary": { "numerator": 0, "denominator": 1 } }
    },
    "points": [
      { "kind": "finite", "value": { "real": { "numerator": 0, "denominator": 1 }, "imaginary": { "numerator": 0, "denominator": 1 } } },
      { "kind": "finite", "value": { "real": { "numerator": 1, "denominator": 1 }, "imaginary": { "numerator": 0, "denominator": 1 } } },
      { "kind": "finite", "value": { "real": { "numerator": 2, "denominator": 1 }, "imaginary": { "numerator": 0, "denominator": 1 } } },
      { "kind": "finite", "value": { "real": { "numerator": 3, "denominator": 1 }, "imaginary": { "numerator": 0, "denominator": 1 } } }
    ]
  },
  "candidates": [
    { "kind": "direct_difference_factor" },
    { "kind": "translate", "offset": { "real": { "numerator": 1, "denominator": 1 }, "imaginary": { "numerator": 0, "denominator": 1 } } },
    { "kind": "transform_left_only" }
  ]
}
```

The complete observation plan and its engine-derived `edge-NNN.source-gate.json` and
`edge-NNN.preflight.json` receipts remain the authoritative schema and resource examples.

## Conduct an exact lineaged re-base world

```text
life boundary lemniscate plan.json
```

The strict `soma-lemniscate-boundary-plan-v1` is a CUDA-forward world adapter around the unchanged
Soma/SLEEP body. It accepts an empty or canonical archived body, an empty or exact prior
lemniscate-world state, and ordered witness, testimony-return, or later-probe edges. Every edge
passes an immutable-source gate and its receipt explicitly declares `cuda_forward`; this command
does not construct a duplicate host sibling or claim unmeasured host identity.

A witness edge presents four intact currents: the Bernoulli curve/normalization law, one complete
exact-rational normalized lineage, common `retain_curve_constraint`, and one tested deed:
`rebase_at_neck`, `collapse_origin`, or `reverse_hand`. Actual theorem⊕lineage⊕deed Mail
intersection is the only world contact. The deterministic world checker returns the common curve
consequence plus the contacted neck consequence, writes the whole journal beside the compact
testimony, and exact-gates the inverse before the successor stands.

`rebase_at_neck` carries chart, neck preimage, ordered samples, hand, tangent, and ancestry.
`collapse_origin` carries only the shared coordinate face; its witness journal still retains the
omitted interior. A return edge may consume the live testimony immediately or an exact durable
testimony wire in a fresh receiver. A probe edge presents two complete neck currents without
reading or choosing a prior branch.

Each edge writes its canonical body, radiation, completion and construction wires, world state,
source gate, and receipt. Witness edges additionally write manifest, exact landing Mail, reversible
journal, world-before/world-after, and create-new testimony wire. The first measured plans and
fresh-receiver controls are under `observations/lemniscate-rebase-01/`.

## Conduct an executable code workshop

```text
life boundary code-workshop plan.json
life boundary code-workshop-forest-census census-plan.json forest.manifest.json
life boundary code-workshop-field-preflight world.json problem forest.manifest.json preflight.json
life boundary code-workshop-field-incidence field-world.json incidence.json
life boundary code-workshop-observe observer-plan.json output.json
life boundary code-workshop-compact-world input.world.json output.world.json
life boundary code-workshop-causal-taxonomy-observe taxonomy-plan.json output/
```

The code-workshop carries whole source, tests, prose, symbolic traces, native constructions, and
real compiler/test consequences around the unchanged Soma/SLEEP body. Witness roles are provenance
only. An optional executable-witness specification must name one exact presented Rust-source
current and one declared test; its compiler/test receipt returns beside the ordinary construction
archive.

A forest census freezes every delivered, non-ignored source once and groups only boundaries already
supplied by the world: a direct dialogue container, exported conversation, or repository directory.
Mounting this descriptor does not present the forest. Complete recurrent path faces induce exact
contiguous incidence with charged source currents; all contacted currents enter one co-present
field passage. That receiving transition archives spans, grows the path arena, and leaves relative
construction blueprints directly. The unchanged source face is then discharged but remains
available. A real edit, gaze, or action may contact it later; descendant paths alone may not create
automatic echo. Empty charged incidence is rest.

The field preflight mounts no state and changes no body or world. It reports the exact complete-face
and contacted-current population which the live receiver would admit. Directory-shaped scans stream
one intact source at a time, while a passage reopens only the exact contacted sources. Neither the
incidence index, manifest order, nor the charged/discharged receipt enters Soma or decides a Swing
deed.

Every archived native span retains the exact internal STEP grips and the corresponding positions
on its intact source worldline. Every arriving CLOSED span deposits a one-segment path root. A
genuinely later span extends every path standing before that edge when a STEP meets the prior distal
endpoint at the same exact source coordinate or after exact zero-extension into one common dyadic
chart. Same-edge arrivals cannot parent one another. Repeated contacts and branches remain plural.
The path's source face is the exact ordered concatenation of its segment bytes.

World v2 retains those paths as one active append-only holonic arena rather than owned complete
records. A root stores one native-span reference. An extension stores its parent identity, arriving
span reference, enacted joint, terminal incidence, accumulated extent, and digest. Native spans
stand once in their edge archives. Complete `LimbRecord` faces are reconstructed only when an
output, compiler, or observer boundary asks for them. Exact material-coordinate, chart-port, and
completed-well indexes are rebuilt in memory when the world opens; they locate possible contacts
but never decide RIDE/FOUND or enter Soma. Existing v1 worlds deserialize and migrate exactly.

Every carried construction crosses the return membrane once as typed `produced_construction`
material using that complete ordered byte face. A continuous section which is also an exact
quotation from one source coordinate crosses separately as typed `world_material`; quotation is
not a precondition for expression. Equal byte faces remain plural currents when their path
lineages differ. The journal, rather than the light, retains the complete segments and joints.

`code-workshop-compact-world` migrates one v1 or v2 world into the v2 holonic spelling, writes it
create-new, reopens it, and refuses unless the complete `World` is exact. This is a checkpoint
operation, not a curriculum, pruning pass, or lossy compressor.

An action retains the legacy `native_spans` candidate material: its hole must be one CLOSED
standing native span. An occupied-world joint declares the exact bytes already present at the
target half-open range, and those bytes must match before any candidate is produced. Declaring
`"candidate_material": "recurrent_paths"` instead carries every standing path of at least two
segments; one-segment roots do not actuate. Every complete candidate meets the same compiler/test
world, and every refusal or consequence returns. Independent compiler jobs use runtime-discovered
host parallelism, while indexed assembly restores causal candidate order before any result becomes
material.

The observer dispatches by strict plan schema. Population v1 reads exact later material, geometry,
conduct, response, coverage, execution, inverse, and repeat faces. Production v2 additionally
indexes the executable witness, every native span and recurrent-path ancestry, every generated
whole program and artifact, every compiler/test consequence, strict objective-residual hands, and
the exact later-population record. The contextual ecology v1 plan names one
or more exact code-workshop world snapshots and emits every literal span, complete path interior,
root lifecycle, direct path parent/child relation, contextual source population, material/chart/
Swing joint, dormancy/reactivation interval, cross-context exact-surface family, and
boundary-indexed support/difference quotient, and every nearest same-surface occurrence arc. Each
arc retains witness-edge distance, role/source continuity, signed source displacement, shared
complete paths, and direct threading. Its distinction depths remain symbolic
(`-log2(n/d)`); no float, score, selection, inferred semantic category, or returned observer value
enters the world. Its strict schema is `soma-code-workshop-context-observer-plan-v1`:

```json
{
  "schema": "soma-code-workshop-context-observer-plan-v1",
  "problem": "carried-gear",
  "worlds": [
    {"name": "clean-edge-13", "path": "edge-013.world-after.json"}
  ]
}
```

Each world path is relative to the observer plan. Multiple snapshots additionally produce exact
same-surface cross-world conduct faces without manufacturing a shared context. No observer drives
the body or selects candidates. Reports use schema `soma-code-workshop-context-observer-v2`. The
one-span predecessor is under
`observations/code-language-transformation-workshop-01/`; sustained
multi-span construction is measured under `observations/code-language-limb-workshop-01/`.

The strict `soma-holonic-incidence-observer-plan-v1` names one problem and an ordered series of
already-enacted world checkpoints. Its `soma-holonic-incidence-observer-v2` report reads the compact
parent/joint fabric directly and carries root/depth/edge growth, material/chart/well port widths,
ordered joint motifs, branching and fan-out, plural visible faces, exact adjacent-transition
support and symbolic `-log2(support/total)`, longitudinal motif birth/dormancy, and structural
storage accounting. Source checkpoint extent, minified holonic extent, and durable pretty-JSON
extent remain three typed gauges. These pattern statistics are observer quotients and never drive
later contact. The first longitudinal report is under
`observations/chronological-language-taxonomy-world-01/results/incidence-observer-v2.json`.

The strict `soma-code-workshop-causal-taxonomy-plan-v1` listener names one or more already-measured
CUDA-forward mathematical-deed edge receipts. It validates each exact inverse, full deed journal,
and emitted consequence surface; pairs every complete native-path candidate with its receipt; and
carries `before -> meeting -> deed -> consequence -> return -> after` as one sparse Holon arc.
Histories share a situated class only where the admitted question and complete ordered objective
consequence are exact. Source label, path bytes, role, depth, and class support remain provenance.
The listener writes and strictly reopens durable presentation/Holon wires, retains typed residuals,
and compares exact class partitions beside finer CUDA conduct. It does not enter Soma, drive a
world, or assign a taxonomy from similarity. The first measured receiver is under
`observations/causal-taxonomy-world-01/`.

## Conduct a sustained elastic world

```text
life boundary elastic plan.json
```

The strict `soma-elastic-boundary-plan-v1` schema declares a resting body, rooted integer-world
state, familiar PGM pigment, material paths, aperture/gaze geometry, deposited shade, output root,
and passage count. One process repeatedly renders the current world, conducts it through CUDA,
retains the body and complete radiation, applies literal STEP/CUT contacts to the reversible world,
exact-gates the inverse, and supplies the changed raster as the next edge.

The simulation interior is exact `i128`. Its PGM eye presents the low-octet residue of the signed
zig-zag displacement/deposit code over the pigment; every receipt retains the complete code and
quotient. The surface may wrap, but its display width does not clip, saturate, globally re-base, or
otherwise alter the world state. A failed world transform occurs only after the already-produced
body and raw radiation have been persisted.

The first concrete plan and measured lifecycle are
`observations/elastic-circulation-01/plan.json` and its `RESULTS.md`.

## Conduct a persistent text world

```text
life boundary text plan.json
```

The strict `soma-text-boundary-plan-v1` schema declares a resting Soma body, a physical typebar
geometry and optional prior world state, an outline font, a source-horizon extent, and one or more
genuinely later source views. Each view may choose a different UTF-8 source, row/column origin,
wrapping face, and supplemental co-present material paths.

Every edge presents the readable source field, the independently writable typebar field, and the
exact visible UTF-8 material co-presently. The application reads only the typebar visual lineage
range from the complete raw radiation, deposits completed paths/joints, articulates later paths
through prior joints, and renders every physical key configuration literally. Source text/field,
world before/after, action wire, literal score, body, radiation, and receipt remain separate
create-new artifacts. The exact world transition is inverted before the successor stands.

This text client also writes the complete native construction index over every source, typebar, and
material lineage before the typebar acts. The fixed printable-ASCII result is therefore labeled a
bounded typebar-world consequence; it neither replaces nor defines Soma's production.

The measured plan, five-edge results, and browser observer are under
`observations/text-world-01/`.

## Read literal inscription

```text
life boundary inscription geometry.json state.json view.json score.txt
```

This restores every event position, including silence, and preserves literal singleton, chord,
and multiplicity faces from a declared key world.

## Articulate native material constructions

```text
life boundary articulate edge-NNN.json edge-NNN.articulation.txt
```

For an ordinary material edge, this streaming listener validates the construction wire and joins
each OPEN/CLOSED span to the exact source range already carried by the edge receipt. It prints the
literal escaped bytes that the construction traverses, including fold-only gaps inside the span.
This is a material-world presentation of Soma's pointing, not a universal text phenotype; the
construction and radiation wires remain authoritative beside it.

## Compare exact radiation

```text
life boundary compare-radiation left.radiation right.radiation
```

The comparison streams both payloads and requires every construction-bearing header field,
lineage extent, and radiation word to agree. Launch count, carriage/integration durations,
compatible SLEEP provenance, and the archive serialization extent implied by that provenance are
boundary measurements and are omitted. The standing body extent and every transported topology,
term, breath, lineage, and payload face still have to agree.

## Build and observe exact arc worlds

```text
life boundary arc-spectral-build arc-plan.json
life boundary arc-return-build rational-return-plan.json
life boundary explicit-formula-build explicit-formula-plan.json
life boundary explicit-formula-observe SNAPSHOT.json passage/ observer/
life boundary explicit-aperture-build aperture-plan.json
life boundary explicit-aperture-observe SNAPSHOT.json passage/ observer/
life boundary explicit-aperture-continue-build continuation-plan.json
life boundary explicit-aperture-continue-observe SNAPSHOT.json passage/ observer/
life boundary poincare-build poincare-plan.json
life boundary poincare-report poincare-plan.json mechanical-read/
life boundary poincare-actuation-preflight experiment.json preflight.json
life boundary poincare-actuation actuation-plan.json
life boundary poincare-actuation-observe session/ observer/
life boundary arc-spectral-observe SNAPSHOT.json passage/ observer/
```

`arc-spectral-build` emits the exact projective-word and Gaussian-integer quadratic control.
`arc-return-build` accepts the strict `soma-arc-return-plan-v1` schema and emits exact unbounded
rational-complex quadratic passages, closed rational-box section residuals and contacts, complete
return arcs, invertible affine state/section/return re-bases, and complete shared-state
changed-parameter foils. Ratios are decimal integer or `numerator/denominator` strings; floats are
not admitted. Every generated current uses `soma-abi::current::EventHeader`; labels, schemas, and
human statements remain listener provenance.

The builder validates every recurrence, section incidence, affine commutation, and foil successor
before atomically creating the event population, snapshot, catalog, passage plan, and durable human
world record. It does not run Soma. The ordinary boundary runner conducts the generated passage.

`explicit-formula-build` accepts the strict `soma-interval-explicit-formula-plan-v1` schema. It
emits the exact prime-power current for `psi(x)`, certified critical-line zero ordinates with their
declared uncertainty, every conjugate-pair phase and contribution, nested finite zero-wave
reconstructions, complete oriented residuals, and the transport between consecutive zero horizons.
All transcendental arithmetic uses directed MPFR interval endpoints at the declared precision; the
exact binary endpoints enter active light while decimal renderings remain listener provenance. A
finite residual is the measured difference between the exact prime current and the declared finite
reconstruction. It is not silently promoted into a theorem bound for the omitted zero population.

`explicit-formula-observe` validates the complete snapshot and both CUDA-forward edges, reads every
returned path, and separates grain-zero coincidence from shared higher-order constructed bricks. It
records every positive residual-to-population relation and the complete cross-family standing-region
table. These family names are observer provenance and never become Soma categories.

`explicit-aperture-build` carries one exact prime/zero body through a declared sequence of
positive-type logarithmic tent receivers. Shared arithmetic currents retain their physical source
coordinates; aperture-local faces and exact receiver transport remain separate currents. The
observer reads every complete path across adjacent edges and across a later return to the same
receiver.

`explicit-aperture-continue-build` accepts one genuinely absent aperture, validates and reuses the
exact material currents catalogued by the founding aperture world, creates only new receiver and
transport currents, and starts one ordinary boundary edge from the named prior SLEEP archive. It
refuses an already-declared receiver, a nonterminal prior edge, changed arithmetic provenance, or
any regenerated current that differs from its original file. The continuation observer compares
that causal edge, distinguishes immediate recurrence, older material reactivation, receiver-local
re-expression, and first-time growth, and retains every returned row. None of those listener reads
enters Soma or chooses a current.

`poincare-build` accepts the strict `soma-poincare-world-plan-v1` schema. It emits one reversible
dyadic-lattice Hénon–Heiles **trajectory current** per lived worldline, oriented crossings of one
declared linear Poincaré section, complete consecutive returns, exact discrete action, ordinary
closed-box objective residuals, recurrent receiver cells, and overlapping exact affine canonical
charts. One trajectory current carries every exact lattice state in lived order. Adjacent states
plus the declared kick/drift/kick law reproduce all six applied displacements, every exact rational
quantization residual, the exact local unquantized shadow Jacobian, energy difference, and action
increment. Time slices are not manufactured as co-present currents.

Return transport composes those reproducible Jacobians at a declared dyadic gauge. The active
return carries the final rebased matrix, projected section matrix, composition count, and maximum
exact re-base residual beside its whole state interior. `poincare-report` reconstructs every local
matrix and every discarded matrix residual from that interior and law. Thus an unbounded rational
receiver product cannot silently become a scale wall, while neither a second copy of the residual
sequence nor thousands of simultaneous step organisms enter the passage.

The Poincaré face is a receiver quotient over the complete trajectory. A chart is admitted only
inside its supplied domain; every simultaneously admitted chart is retained and no chart is
selected globally. Objectives return oriented difference and contact only. They are not scores,
rewards, route selectors, or stopping conditions. The builder validates fixed initial energy,
every exact inverse lattice deed, canonical chart/inverse laws, bracketed crossing incidence,
same-state and same-face foils, and deed-by-deed chart dualities before creating any output.

`arc-spectral-observe` validates the snapshot instrument, event order, local tags, extents, hashes,
both edge receipts, and complete path cover before writing `PATHS.md` and `PATHS.tsv`. The observer
retains every exact construction row beside its source statement. It neither classifies, selects,
scores, nor returns anything to Soma.

The measured rational and continuous plans and qualitative results are under
`observations/arc-return-rebase-world-01/` and
`observations/hamiltonian-poincare-world-01/`.

`poincare-actuation` is the reusable causal successor. A strict experiment supplies one changed
Hamiltonian preparation, a declared physical aperture, an oriented section and objective faces,
an exact prior Poincaré snapshot, and any finite population of explicit affine canonical maps with
their exact inverses. The complete prior return currents enter verbatim. Preparation, every prior
return, and every action remain separate co-present light; no return×action source product is
manufactured.

After CUDA conduct, actual Mail incidence forms every connected preparation⊕return⊕action
relation. Every connected relation acts. Since a deterministic action has one physical result,
the returned surface carries its full lattice trajectory or typed physical refusal once and a
separate compact incidence for every contacting prior return. Thus causal ancestry remains plural
without duplicating identical physics. An enacted outcome retains every lattice state, oriented
crossing, objective residual vector, exact half-squared difference, maximum energy residual,
action integral, final state, and whole inverse. Action labels and contact grips stay listener
provenance.

`poincare-actuation-preflight` derives the complete potential action population at runtime-derived
host width and writes the exact maximum returned current/octet forecast before a body is mounted.
The ordinary causal source gate then accounts for the complete body plus intact input population.
Neither stage shrinks, samples, batches, or substitutes the declared construction.

`poincare-actuation-observe` reads every path on every edge, every tested relation, every
trajectory/refusal, and every crossing⊕objective difference into exhaustive TSVs and a human
summary. It is a listener only. The measured experiment lives under
`observations/poincare-return-actuation-world-01/`.
