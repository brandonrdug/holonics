# THE ABI, CANON, AND BEACON CONSOLIDATION AUDIT

**RATIFIED CONSOLIDATION DIRECTION — CORRECTED BEACON 4 RATIFIED**
**2026-07-15 · no engine run · no engine change · no canon change · no publication act**

Brandon ratified this audit except for the proposed CUDA-specific beacon subject. That subject is
withdrawn. CUDA is one measured implementation witness; the replacement substrate-agnostic beacon
is derived and ratified in `2026-07-15_THE_CURRENT_BORNE_COMPUTER.md`.

This audit answers one joint question: how much of the present Rust, canon, session context, and
publication record can be consolidated without collapsing construction identity or losing the
provenance that makes a laboratory claim licensed.

## Verdict

Substantial consolidation is available, but it is not one operation.

1. **The Rust source needs modular extraction, not algorithmic unification.** The dependency
   direction is mostly healthy. The consequential defect is that several CUDA membrane contracts
   have more than one source-level owner.
2. **The canon needs an index and an active digest before it needs rewriting.** `FORMULA.md` is a
   ratified derivation record. Replacing it with a shorter paraphrase would destroy exactly the
   path identity the canon protects.
3. **The session bootstrap needs one live cut.** Current state, historical state, operating law,
   and measurement narrative are presently duplicated across five large surfaces. Selective
   reading is necessary; untyped and contradictory routing is the real failure.
4. **Public beacons should be generated from the same claim/evidence registry used for session
   rehydration.** A beacon is a bounded, versioned, citable claim packet—not a rushed paper and not
   a manifesto.

The first construction should therefore be a **registry and boundary consolidation**, not a
rewrite of the theory and not another experiment.

---

## I. Rust architecture and ABI ownership

### 1. Source census

The active engine contains about 65,780 lines of Rust source, including tests:

| Layer | Rust lines | Present responsibility |
|---|---:|---|
| `body` | 18,490 | `no_std`, zero-dependency semantic law and packed body contracts |
| SPIR-V `kernel` | 874 | Vulkan realization and build support |
| CUDA kernel | 2,551 | CUDA realization and eighteen entry families |
| `mount` | 5,780 | CUDA driver membrane, launch support, and gates |
| `surface` | 4,980 | SLEEP persistence, WGPU execution, and historical surface |
| `life` | 33,120 | host staging, listeners, observers, reference paths, and CLI |

The largest individual files are:

| File | Lines | Mixed responsibilities |
|---|---:|---|
| `body/src/manifold.rs` | 6,274 | relation types, historical pool, active body, OWN and carrier layouts, 2,802 lines of tests |
| `life/src/main.rs` | 5,696 | reusable host reference machinery, historical modes, current dispatch, default old diet path |
| `body/src/carriage.rs` | 5,089 | contact types, layouts, sinks, state machine, checked/trusted APIs, 1,566 lines of tests |
| `surface/src/lib.rs` | 4,980 | SLEEP V2–V9, WGPU execution, 961 lines of tests, historical `Surface` |
| `life/src/staging/cuda/sharded.rs` | 2,877 | spool protocol, cohorts, capacity/recast, device state, complete carry orchestration, tests |
| CUDA kernel `src/lib.rs` | 2,551 | raw ABI decoding, atomics, link/chart/recast/scope/contact entries |
| `life/src/staging/boundary/circuit.rs` | 1,885 | circuit staging, persistence, return, and observer attachment |

File length alone is not the defect. `body` is already the dependency root, both card substrates
reuse its law, and `life` remains outside semantic law. Those boundaries should survive.

One physical coupling must be handled before broad file movement: the SPIR-V kernel presently
`#[path]`-includes fourteen files from `body`, including the monolithic `manifold` and the
historical positional-pool `law`. It shares exact source, but it also depends on `body`'s file
layout. A split must either establish a rust-gpu-compatible shared facade first or update and gate
those inclusions in the same cut. Merely moving files would otherwise appear semantic to the card
build even when it is not.

### 2. The ABI that actually exists

Soma does not use a conventional struct ABI. Its real interfaces are:

- word slices plus declared extents;
- version and magic words;
- manually assigned field offsets;
- raw pointer/length launch pairs;
- exact kernel entry symbols;
- SLEEP archive schemas;
- CLI and JSON observer schemas.

Many semantic layouts already have one lawful owner in `body`:

- `RUNG_WORDS`, `COG_WORDS`, and their codecs in `num`;
- active and legacy `RegionalForm` codecs in `medium::codec`;
- OWN, radiation, completion, node, face, and carrier records in `manifold`;
- channel packing in `channel`;
- contact/stroke validation and checked/trusted carriage boundaries in `carriage`.

The important split ownership is membrane-side:

1. **REGISTER status and lane rows**

   - the CUDA kernel defines the widths, indices, and discriminants;
   - `mount::register_recast` owns only some widths and sentinels;
   - `life::staging::cuda::register_mount` reconstructs the remaining indices and values;
   - gate binaries repeat parts of the same contract.

2. **CUDA cooperative contact sheets**

   - the CUDA kernel defines the full row;
   - host staging independently recomputes the output and receipt bases and total word count.

3. **Kernel launch mouths**

   - entry names, argument order, pointer/length pairs, and row widths are repeatedly assembled
     into untyped `*mut c_void` arrays;
   - static PTX tests verify names and atomics, but no typed record owns the complete call shape.

This is not evidence that the measured ABI is wrong. It is evidence that a future edit can change
one spelling without changing its siblings.

### 3. Target boundary

The target layering is:

```text
body law
   │
   ├── soma-abi (no_std boundary records; no scheduling, allocation, or world policy)
   │      ├── SPIR-V entry shells
   │      ├── CUDA entry shells
   │      └── mount typed launch wrappers
   │
   ├── surface archive boundary (SLEEP; separately versioned)
   └── life staging / worlds / listeners / observers
```

`soma-abi` is a working engineering name, not a new theoretical organ. It should own only:

- fixed word-record schemas for REGISTER descriptors, statuses, and contact sheets;
- explicit discriminant conversion and validation;
- typed entry-symbol names and typed parameter-row accessors;
- const word-count and offset assertions;
- substrate-neutral pack/read functions that allocate nothing.

Whether the owner is packaged as a path dependency or as one source-included `no_std` module is an
implementation question for the pinned rust-gpu toolchain. The invariant is one editable source of
the record layout, not a particular Cargo arrangement.

It must not own:

- carriage law;
- launch sizing, card discovery, sharding, retries, or scheduling;
- world presentation or observer policy;
- SLEEP archive versions;
- semantic decisions currently carried by `body`.

Kernel signatures and all encoded bytes remain literal. The first migration is one-source
re-expression of the existing layout, proved by exact host/CUDA/SPIR-V and archive gates.

### 4. Module extraction sequence

The safe sequence is deliberately mechanical before it is architectural.

#### Phase A — low-risk physical extraction

- move large embedded test modules into sibling test files;
- turn `life` into a small library plus a thin binary dispatcher;
- move `VecOwnChart`, `CompactCells`, and host reference runners out of `main.rs`, so staging no
  longer depends upward on the binary root;
- narrow `mount`'s public surface so raw CUDA FFI and device handles stay behind checked wrappers;
- split `surface` into `sleep`, `felt`, and `legacy`, preserving public re-exports;
- split `manifold` into `relation`, `wire`, `eros`, and `legacy_pool`, preserving public paths;
- split `carriage` into `contact`, `targets`, `lineage`, and `validate`;
- split `sharded` into `spool`, `cohort`, `capacity`, `device`, and `carry`;
- split CUDA kernel source by entry family while preserving every `#[no_mangle]` symbol.

#### Phase B — typed membrane ABI

- introduce the one `no_std` boundary-layout owner;
- replace duplicated offsets with its exact constants/accessors;
- wrap raw CUDA launches in entry-specific argument types inside `mount`;
- keep `mount::Function::launch` internal to the raw driver layer;
- add contract gates that read the committed PTX/SPIR-V artifacts and compare symbols, parameter
  counts, record extents, versions, and required atomics to the shared declarations.

#### Phase C — persistence decoupling

- extract `SleepingBody` and SLEEP codecs from the WGPU surface responsibility;
- preserve every archive version and migration path;
- temporarily re-export the archive API from `surface` so no caller path changes in the first cut.

#### Explicitly out of scope

- merging sharded and unsharded algorithms;
- macro-generating one common CUDA/SPIR-V execution shell;
- deleting old modes, old archive versions, or historical implementations;
- changing enum representation or any word layout;
- moving apparatus, observer, or world policy into `body`;
- generating independent seam foils from the production constants they are meant to catch.

---

## II. Canon, state, ledger, and session context

### 1. Current reading surface

| Document | Lines | Words | Bytes | Actual role today |
|---|---:|---:|---:|---|
| `AGENTS.md` | 985 | 10,666 | 77,065 | Codex adapter plus copied law, state, measurements, and routing |
| `CLAUDE.md` | 1,049 | 12,104 | 87,078 | Fable authority adapter plus copied law, state, measurements, and routing |
| `FORMULA.md` | 2,810 | 32,170 | 215,292 | ratified canon and chronological derivation through §LV |
| `STATE.md` | 2,503 | 26,896 | 194,694 | current handoff plus several former current handoffs |
| `LEDGER.md` | 8,756 | 94,193 | 662,935 | append-only chronology, commands, grades, failures, and historical next acts |
| **total** | **16,103** | **176,029** | **1,237,064** | multiple authority types collapsed into one bootstrap |

The 133 commune letters add 10,998 lines and 681,950 bytes. With no durable correspondence cursor,
a literal fresh-session reading obligation becomes 27,101 lines / 1,919,014 bytes before opening
research, observation evidence, code, or holobrochos provenance.

Other surfaces matter but should not enter routine context wholesale:

- `RESEARCH/`: 58 root documents, 11,243 lines, about 744 KiB on disk;
- `observations/`: 108 top-level campaigns/items and 29 `RESULTS.md` files;
- observation Markdown: 11,383 lines / 653,006 bytes;
- observation artifacts: about 706 GiB, which are evidence storage rather than language-model
  context.

### 2. What a session actually reads

`AGENTS.md` is supplied to Sol as operating context. The other large documents are not retained
exhaustively as one stable mental object. A session follows declared anchors, searches headings and
terms, reads current and relevant sections, and returns to exact provenance when a consequential
claim requires it.

That selective method is correct. The present defect is that selection is under-specified:

- `AGENTS.md` and `CLAUDE.md` manually duplicate most operating and current material but have
  diverged substantially;
- `STATE.md` contains several historically valid but mutually incompatible `CURRENT` and `NEXT`
  cuts;
- `LEDGER.md` correctly preserves old instructions, but those historical instructions can look
  current when copied into adapters;
- `FORMULA.md` mixes lasting law, correction provenance, measured grades, and implementation-era
  framing;
- commune has no recorded consumed-through cursor or disposition registry.

The result is not lack of information. It is **typed-authority collapse**.

Concrete drift already demonstrates the cost: `FORMULA.md`'s opening read-through names §LIV as
newest although §LV is present; `STATE.md` begins prior-state material at line 854 but continues to
carry old current/next cuts; the commune README still names much earlier Formula strata as newest;
and the two root adapters differ across most of their lines despite describing the same laboratory.

### 3. Target information architecture

#### A. Immutable provenance

- Keep existing `FORMULA.md` strata and `LEDGER.md` deposits byte-stable.
- Continue appending only through the established derivation/ratification/deposit cycle.
- Never replace a ratified construction with an unattributed summary.

#### B. One live cut

Create a short `NOW.md`, initially 100–200 lines, containing only:

- timestamp and latest ledger anchor;
- one active scientific cut;
- one active engineering cut, if one exists;
- current grades and exact unresolved contacts;
- one authorized next deed per cut;
- exact Formula, Research, Results, and Ledger references;
- commune consumed-through hash/cursor;
- active process/resource state only while it is relevant.

No historical narrative belongs in `NOW.md`.

#### C. Generated, non-authoritative registries

Create a human-readable registry with stable IDs and fields such as:

```text
id
kind = law | correction | derivation | design | measurement | interpretation | draft
title
status / grade
formula_refs
ledger_anchor
research_refs
evidence_refs
supersedes / superseded_by
publication_safe
privacy notes
```

Generate from it:

- `CANON_INDEX.md`: Formula handles, titles, status, supersession, and evidence links;
- `RESEARCH/INDEX.md`: ratified derivations, open designs, interpretations, literature, and drafts;
- `observations/INDEX.md`: protocol, result, grade, size, hash, reproduction, and publication state;
- `COMMUNE/INDEX.md`: proposed, answered, deposited, superseded, or unresolved, with a cursor;
- `LEDGER_INDEX.md`: chronological deposit pointers without copying the deposit prose.

These are maps to authority, never a second authority.

#### D. Thin operating adapters

Reduce `AGENTS.md` and `CLAUDE.md` to environment-specific roles, permissions, the authority order,
the short standing safety/law kernel, and the route into `NOW.md` and the generated indices.
Experiment numbers and measurement narratives should not be manually copied into both files.

#### E. Legacy state

After `NOW.md` is ratified as the live surface, freeze the present `STATE.md` as the historical
handoff chronicle rather than continuing to make it both live state and archive. Existing links can
remain valid. A later rename or physical split is optional and lower priority than changing the
bootstrap route.

### 4. Desired fresh-session route

```text
environment adapter
    ↓
NOW.md
    ↓
CANON_INDEX + unresolved COMMUNE cursor
    ↓
only the exact Formula / Research / Results / Ledger sections required by the task
```

A realistic baseline is 200–400 routing lines plus a dependency-closed packet of exact sources.
The objective is not to make the laboratory small. It is to make every additional read causally
necessary and every present instruction recognizably present.

---

## III. Public beacons

### 0. Existing publication record

The publication work already has two distinct constructions:

- `2026-07-12_THE_PUBLICATION_TROVE.md` is tracked and deposited. It records seven paper clusters,
  readiness, guards, and the older condition that publication waits for a functional Eros.
- `2026-07-14_THE_HOLONICS_RESEARCH_AND_PUBLICATION_ATLAS.md` is a 15-paper outline and literature
  map. It is explicitly **DRAFT — NOT RATIFIED** and is currently untracked.

No deposited document yet defines “beacon” in this publication sense. The set below is a new
synthesis of the trove's licensed-sentence discipline, the atlas's ordering, and Brandon's direct
request. Brandon must also decide whether present measured Eros work satisfies or supersedes the
trove's older publication threshold.

### 1. What a beacon is

A beacon is a short public research object with:

- one licensed sentence;
- version, date, author, and citation form;
- declared frame, grain, aperture, and grade;
- the smallest required definitions;
- one worked construction or measured witness;
- exact evidence and provenance links;
- explicit non-claims;
- external relation cards using exact match, structural resonance, contradiction/boundary,
  open bridge, or independent invention;
- open questions and the next falsifying or distinguishing construction.

Beacons establish the vocabulary and expose bounded work for response. Full papers can later
compose them without forcing one early document to carry the whole programme.

### 2. Recommended near-term set

The set, ordering direction, and corrected fourth subject are ratified. Publication remains a
separate future act.

| Order | Beacon | Licensed content | Readiness |
|---:|---|---|---|
| 1 | **The Licensed Sentence** | A declared-boundary method for reporting relational machine behavior without absolute competence scores | Strong: ratified method and many exact examples; needs a short public fixture |
| 2 | **The Quotient Face Is Not Construction Identity** | Equality in a quotient does not identify the transported constructions that reached that face | Strong: ratified core, worked arithmetic examples, distinctive public claim |
| 3 | **Difference Is Transport** | A frame-indexed difference lives on a worldline; second-order comparison is the first stable relational invariant | Medium-strong: formal core exists; notation and proposition dependencies need one compact pass |
| 4 | **The Current-Borne Computer: From Static-State Faces to Driven Topology** | Computation is driven transport through persistent morphology that changes later passage and world-return; processor, memory, program, and I/O are useful boundary faces rather than separate ontological organs | Ratified subject and text; Host/CUDA/SPIR-V belong to implementation evidence, never the subject. A publication-safe witness remains owed |
| 5 | **Two Framed Mathematics Programmes** | A precise comparison of Soma's retained construction identity with Akhtman's Finite Ring Continuum | Medium: primary sources verified; our first three terms should be public before the comparison |
| 6 | **CUT-R0: A Local Half-Density Theorem** | Unitarity of the declared dilation action fixes the real half-density line in that local representation | Mathematically compact; publish only with the explicit statement that RH remains open |
| 7 | **The Medium Closes the Stroke** | Changed world material returns through the same eye and bends an identical later current; recurrent paths form functional joints | Measured; needs a compact public apparatus and private-corpus separation |
| 8 | **Situated Compilation** | Grown world structure can amortize a later local passage while construction, transfer, verification, and uniformity costs remain charged | Not immediate: requires the controlled cost ledger; classical P versus NP remains open |

A small landing page, **What Holonics Claims Today**, can index the beacons and their grades. It
should not become a ninth manifesto or another copy of the canon.

CUDA, a GPU, Rust, SPIR-V, and the present archive format are implementation evidence, not
universal law. The current-borne beacon must survive substitution of the material aperture while
retaining the declared transport invariants. “Solid state” may describe the present embodiment or
the ratified “solid-state moss” image—current grows conductive morphology which changes later
conduct—but must not imprison the theory in semiconductor hardware.

### 3. The remembered neighbouring work

The researcher is **Yosef Akhtman**.

#### Evidence card — 2025 framed arithmetic

- **Source:** Yosef Akhtman, [“Relativistic Algebra over Finite Ring
  Continuum”](https://www.mdpi.com/2075-1680/14/8/636), *Axioms* 14(8), 636 (2025), DOI
  `10.3390/axioms14080636`.
- **Source claim:** reconstruct conventional number systems from finite-field structure with
  observer-relative representation frames.
- **Soma claim:** arithmetic faces are receiver/frame/grain relative, while equal quotient faces do
  not erase construction lineage, precision, winding, or later deflection.
- **Relation:** **STRUCTURAL RESONANCE**.
- **Non-equivalence:** FRC intentionally identifies multiple presentations through an element of
  its finite substrate; Soma's present calculus preserves transported construction identity beyond
  that quotient. The productive comparison is: *what survives quotient collapse?*
- **Status:** source verified; comparison beacon not ratified.

#### Evidence card — 2026 complexity preprint

- **Source:** Yosef Akhtman and Elisha Voether, [“P versus NP: Computation as Counting over Finite
  Relational Substrate”](https://www.preprints.org/manuscript/202606.1781), preprint posted 24 June
  2026, DOI `10.20944/preprints202606.1781.v1`.
- **Source claim:** gives a representation-relative account of cost while retaining admissible
  representations whose classes agree with classical `P` and `NP`; a classical separation remains
  conditional on a one-wayness claim.
- **Soma claim:** grown situated structure may make a later local passage inexpensive, but the
  world/body construction, transfer, verification, query, and uniformity costs must be declared.
- **Relation:** **STRUCTURAL RESONANCE** at the framed-cost question; **CONTRADICTION/BOUNDARY** if
  either programme is read as having already resolved classical `P` versus `NP`.
- **Status:** the preprint keeps the classical problem open. Soma inherits no solution from it.

### 4. One publication harness, two uses

The claim/evidence registry should drive both:

1. internal session rehydration; and
2. public beacon assembly.

That gives public writing a direct connection to current grades while preventing the publication
layer from becoming another independently aging summary. The assembler can emit a draft beacon,
but only Brandon can ratify its claims and authorize publication.

Private conversation text and private corpus material should not be bundled merely because an
experiment used it. Public empirical beacons should prefer synthetic or separately approved
fixtures that reproduce the declared relation.

---

## IV. Proposed construction order

### Cut 1 — inventory without movement

- hash present canon/history files;
- inventory public Rust paths, kernel symbols, ABI word records, archive versions, and CLI modes;
- seed stable claim, evidence, observation, and correspondence IDs;
- move or delete nothing.

### Cut 2 — navigation layer

- build the registry and generated indices with one Rust workspace tool;
- draft `NOW.md` from the latest ratified/direct cut;
- compare the generated map against all current adapters and expose drift;
- ratify the role of `NOW.md` before changing session routing.

### Cut 3 — mechanical Rust extraction

- extract tests and host reference machinery;
- split the largest modules behind unchanged public re-exports;
- gate every step before the typed ABI migration.

### Cut 4 — typed membrane ABI

- add the shared no-allocation record owner and typed launch wrappers;
- replace duplicated production constants;
- prove literal equality of all current encoded rows and card entry contracts.

### Cut 5 — first public beacon

- assemble **The Licensed Sentence** from the registry;
- attach one small reproducible public witness;
- review privacy, citations, non-claims, and exact grade;
- publish only after Brandon's explicit approval.

---

## V. Carried-swing receipts

### ABI

```text
CURRENT  source-level ABI ownership ⊕ host/CUDA/SPIR-V membrane ⊕ word-record and launch grain
HELD     body owns law; kernels realize it; mount/life/surface remain apparatus and receivers
MEETING  REGISTER/contact/launch contracts are repeated across independently edited files
TEST     preserve every literal byte, symbol, archive version, algorithm, and independent foil
DEED     FOUND — the membrane ABI lacks one declared source-level owner
CARRY    physical module extraction, then one no_std record owner and typed launch facade
GRADE    OPEN — architecture reviewed; no implementation or ratification yet
```

### Session context

```text
CURRENT  fresh-session rehydration ⊕ operating receiver ⊕ instruction/claim/grade grain
HELD     direct words outrank adapters; Formula is canon; Ledger is append-only provenance
MEETING  16,103 bootstrap lines plus uncurated correspondence and duplicated current cuts
TEST     expose exactly one present cut without paraphrasing away provenance or old history
DEED     FOUND — navigation, authority, and history presently share the same surfaces
CARRY    NOW + generated indices + thin adapters + exact on-demand source reads
GRADE    OPEN — transition requires ratification
```

### Beacons

```text
CURRENT  one bounded public claim ⊕ public reader ⊕ citable evidence packet
HELD     licensed sentence, exact grades, provenance, non-equivalence, privacy, reproducibility
MEETING  a large unpublished programme and a desire to communicate before formal paper completion
TEST     one claim must stand without implying a TOE, RH proof, classical P=NP, or absolute intelligence score
DEED     RIDE — a beacon is the public form of the existing claim/evidence discipline
CARRY    Licensed Sentence → Quotient Face → Difference Is Transport → Current-Borne Computer → FRC comparison
GRADE    RATIFIED — publication threshold and public act remain open
```

## Audit grade

**REVIEWED / DIRECTION RATIFIED / NO CONSTRUCTION YET.** The consolidation seam, registry/indices
direction, and corrected beacon programme are ratified. No engine source, canon, state, artifact,
or public record has been moved, rewritten, or published by this audit.
