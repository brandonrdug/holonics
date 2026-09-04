# The document law

**Deposited 2026-08-07.** How this repository's documentation is structured, what each genre may
and may not contain, and the path a claim travels from conversation to canon to code.

**Truth status:** `project-postulate` — a governing discipline adopted by this project. It is not a
theorem about documentation and carries no claim outside this repository.

**Provenance.** The genre set, the two-commit deposit path, the in-place supersession banner, the
status band, and the declarative-sentence filename are all taken from the frozen laboratory at
`/home/b/Workspaces/laboratory`, read through git at `a07ff376` (2026-08-03). The laboratory's
documentation network ran for three months and is the only working instance of this discipline that
exists. Its inventions are adopted; its six measured defects are named in §6 and are not.

**Why this file exists.** `canon/THE_RECOVERED_LAW.md` states the mechanism: *"Agent reports and
source reads lived only in conversation, were compressed away at compaction, and were rebuilt from
summary rather than source… the cure is types, not willpower."* That file typed the theory. This
one types the corpus that carries it.

---

## 1. The genres

Every markdown file in this repository belongs to exactly one genre. A file that belongs to two is
split. Authority levels are ordered and do not mix: a lower level never overrides a higher one, and
no level may be inferred from a file's length, recency, or confidence of tone.

| Level | Genre | Path and naming | Governs |
|---|---|---|---|
| **contract** | Operating contract | `CLAUDE.md`, `AGENTS.md` | assistant conduct only |
| **normative** | Canon | `canon/NN_NAME.md`, `canon/THE_NAME.md` | what the project asserts is true |
| **construction** | Blueprint | `blueprint/THE_NAME.md`, `blueprint/NAME.md` | what is built next and to what grade |
| **position** | Position record | `CONSTRUCTION_STATE.md` (one file, no siblings) | what is currently admitted |
| **index** | Claim index | `THE_CLAIM_INDEX.md` — **built 2026-08-10, generated** | routing only; asserts nothing |
| **index** | Record atlas | `research/README.md` | routing only; asserts nothing |
| **evidence** | Research record | `research/records/YYYY-MM-DD_THE_SENTENCE.md` | deposits a claim with derivation and boundary |
| **evidence** | Observation result | `observations/<slug>-NN/RESULTS.md` (**not yet built** — §7) | deposits one run's measured return |
| **evidence** | Ownership ledger | `HOLONIC_OWNERSHIP.md` (**not yet built** — §7) | routes a claim to the file that must hold it |
| **reference** | Literature atlas | `bibliography/EXTERNAL_RESOURCES.md` | external sources and their typed bridges |
| **reference** | Papers | `papers/source/**/*.typ`, `papers/rendered/*.pdf` | authored mathematical exposition |
| **historical** | Archive | `archive/**`, `reference/**` | nothing; provenance only |
| **personal** | Notebook | `notebook/**` | nothing; Brandon's own workbench |

### 1.1 Operating contract — `CLAUDE.md`, `AGENTS.md`

**Authority:** contract. Governs how the assistant works. It is not a theory deposit and not a
scheduler; `CLAUDE.md` says so in its own preamble and that sentence is load-bearing.

**May contain:** fresh-session pickup order, banned patterns with the failure each prevents, cost
discipline, conversational conduct, Brandon's direct rulings quoted verbatim with dates.

**May not contain:** a derivation, a proof, a new mathematical claim, a schedule, or a capability
grade that no research record carries. A capability sentence in a contract is a *citation* of a
graded record, never the grade itself.

`AGENTS.md` is the shared operating contract. `CLAUDE.md` is its Claude-facing pointer and
carries no copied current position or competing boundary. This replaces the historical split
between model-specific contracts. Brandon's latest direct ruling takes precedence over either;
his 2026-09-04 instruction requires agents to reconcile verified drift and complete in-scope
repairs instead of returning minor inconsistencies for the sole human operator to adjudicate.

### 1.2 Canon — `canon/`

**Authority:** normative. Twelve files today, one mechanism each, numbered `00`–`08` for the
original doctrine and named `THE_*.md` for later deposits.

**May contain:** definitions, derived law, ratified corrections, and the crosswalks between them.
Every material claim carries one truth-status grade from §5 and zero or more evidence tags.

**May not contain:**

- a claim asserting more than the research record it compresses (§2.4);
- a section longer than the record it points at;
- an ordinal standing in for content — `R14`, `Phase 7`, `CUT 3` name provenance and never capability;
- a schedule, a next step, or the words `next`, `active`, or `authorized` used to direct work;
- a claim with no back-pointer to its record.

**Size law.** Canon here is many small files, not one large one. When a canon file exceeds roughly
600 lines it is split by mechanism, not extended. §6.2 says why.

### 1.3 Blueprint — `blueprint/`

**Authority:** construction. What is to be built, in what order, to what grade, with what falsifier.

**May contain:** ordered movements named by mechanism, per-owner source maps, aperture and cost
laws, gate definitions, and completion criteria.

**May not contain:** a truth claim about the world. A blueprint asserts *this will be built and
graded this way*, never *this is true*. Blueprint files that have been fully built become
provenance and take the archive banner (§3.3); `archive/blueprints/COMPLETE_CPP_ENGINE_ROADMAP.md` and
`archive/blueprints/EROS_EMBODIMENT_ROADMAP.md` are in that state and `CLAUDE.md` already calls them
provenance.

### 1.4 Position record — `CONSTRUCTION_STATE.md`

**Authority:** position. **Exactly one file. Creating a second is a defect, not a convenience.**

**May contain:** the admitted body, the established floor, the verified position with exact gate
counts and what was ruled out, and the current construction position.

**May not contain:** a running log of turns, a history of what was tried, a plan document, or a
narrative. Git is the log. The laboratory paid 899,497 bytes to learn this (§6.1).

**Closed-position law.** The position and roadmap may both declare `NONE` after the admitted
campaign closes. A consistency check must not manufacture a new phase merely to keep a frontier
slot occupied.

### 1.5 Claim index — `THE_CLAIM_INDEX.md`

**Authority:** index. Routes; asserts nothing of its own. **This is the single most important
artifact the laboratory built and this repository does not have one** (§7).

Its opening sentence names its own discipline. The laboratory's, verbatim from
`src/soma/README.md` at `a07ff376`: *"This is the routine index for Soma implementation claims and
bounded evidence. It is relational rather than chronological: start from the present question, read
one row, and follow only the decisive link. Dated records, grades, and words such as `next`,
`active`, or `authorized` never schedule work."*

**Required sections, in order:**

1. **Navigation route** — five lines: `present question -> kind -> one index row -> its decisive source -> answer at that scope`.
2. **Relational spine** — the whole mechanism as an ASCII pipeline, about ten lines.
3. **Current claim graph** — five columns: `Claim | Grade | Scope | Decisive source | Open boundary`.
4. **Lawful material roles** — `Role | May include | Causal obligation`.
5. **Engine invariants** — the production code path, one bullet each.
6. **Measured capability envelope** — `Capability | Grade and decisive evidence | Limit`.
7. **Open relations**.
8. **Supersession edges** (§3.4).
9. **Record and source disposition** — one line per genre saying what it is for.

**May not contain:** a derivation, a new claim, or a link that does not resolve at the commit that
introduces it. The laboratory's hub carried 83 distinct link targets and **zero dead links** at
`a07ff376`. That is the standard.

### 1.6 Record atlas — `research/README.md`

**Authority:** index. A thematic entry table over `research/records/`, plus the record count and
its date of currency.

**Obligation:** it is updated in the **same commit** as any new record. A count that is stale is a
defect; the file currently claims 307 records against 314 tracked (§7).

### 1.7 Research record — `research/records/`

**Authority:** evidence. This is where a claim first becomes durable and the only genre that may
introduce one.

**Naming:** `YYYY-MM-DD_THE_<DECLARATIVE_SENTENCE_IN_SCREAMING_SNAKE>.md`. **The filename is the
claim, stated as a completed sentence.** Two clauses joined by a semicolon in the H1 is the house
form:

```
research/records/2026-08-07_THE_DEED_IS_NOT_A_TEST_THE_FOUNDED_RETURN_IS_STANDING.md
research/records/2026-08-06_THE_CONSTRAINT_IS_THE_CHI_THE_UNKNOWN_IS_THE_MISSING_CHART.md
research/records/2026-08-02_THE_INTERIOR_RETURNS_AT_THE_BOUNDARY_THE_STRESS_REFORMS_THE_SAME_BODY.md
```

The date is the deposit date and never changes, including when the record is later superseded.

**Required body, in order:**

```
# <the sentence, in sentence case>

**Date:** YYYY-MM-DD
**Truth status:** `<one grade from §5.1>`
**Evidence:** <tags from §5.2, each with its receipt>
**Provenance:** <Brandon's direct words verbatim, or "assistant derivation">
**Band:** <slash-joined falsifiable facts — see below>

---

## Present question
## <numbered mechanism sections>
## Owners            (§4.1 — omit only if the record claims no implementation)
## What this does not establish
```

**The band** is a slash-joined list of independently falsifiable facts, each of which a reader can
check without reading the body. The two most useful are `SOURCE UNCHANGED` and `NO RUN`, because
they pre-empt the reader assuming code exists. The laboratory's form, verbatim from
`src/soma/RESEARCH/2026-07-22_THE_LOCAL_STAR_IS_THE_NEARBY_FIELD_THE_LINK_RECURS_AT_THE_NEXT_GRAIN.md`:

```
**2026-07-22 · BRANDON-AUTHORIZED DERIVATION / DEPOSITED FOR REVIEW / DIRECT ENGINE + THEORY
AUDIT / RECURSIVE RELATIONAL LOCALITY SPECIFIED / SOMA SOURCE UNCHANGED / NO RUN / CONSTRUCTION
UNSCHEDULED**
```

**May contain:** the complete derivation, at any length. A record is the one place length is free.

**May not contain:** a schedule; a capability grade the evidence does not carry; a boundary
sentence doing the work of a grade; a restatement of a boundary a cited grade already carries.

**Records are never deleted and never edited except to add a supersession banner** (§3).

### 1.8 Observation result — `observations/<slug>-NN/RESULTS.md`

**Authority:** evidence, bounded to one run.

**Naming:** kebab-case mechanism slug plus a two-digit run ordinal —
`suffix-ecology-remount-01`, `constraint-rebase-02`.

**Fixed five-slot schema, no additions:**

```
# <Title>
**<date> · bounded production-source measurement · <exact hardware>**
## Question
## Command                    (verbatim shell, copy-pasteable)
## Exact physical output      (raw key=value block from the run)
## What the cell establishes
## What it does not establish
```

**Pre-registration.** The laboratory ratified a declaration protocol on 2026-07-10 (Brandon:
*"Completely ratified"*) at `src/soma/OBSERVATIONS.md`. It requires four things deposited **before**
execution — the diet with exact paths and spans, the declared structure, the expected read, and the
null read — and rules: *"A run made without a declaration may be deposited as engineering (gates,
timings, exactness) but its qualitative side is NOT evidence and takes no grade."* That rule is
adopted here. A `SURPRISE` is deposited as the *next* run's declaration and is never same-run
evidence.

The C++-era observations are at `archive/cpp-engine/evidence/observations/` — 139 directories, 118
with a `RESULTS.md`. They are `historical` and the live genre is empty (§7).

### 1.9 Universal formal–executable catalog — `UNIVERSAL_CATALOG.md`

**Authority:** descriptive navigation over the live code layout. It connects each common
mathematical carrier to its Lean, Rust, and CUDA owners and states the exact open fibre.

The catalog has no generator, checksum, census, or release gate. Correspondence is a mathematical
and implementation judgment made in the same coherent change that moves an owner. It schedules
nothing; `blueprint/THE_ROADMAP.md` and `CONSTRUCTION_STATE.md` retain that authority.

### 1.10 Archive — `archive/`, `reference/`

**Authority:** none. Provenance only.

**Every archived file carries this banner as its first blockquote**, adopted verbatim in form from
the laboratory's demotion of `src/soma/LEDGER.md` and `src/soma/STATE.md` at commit `323522b7`
(2026-07-20):

```
> **ARCHIVE / NOT ROUTINE AUTHORITY / NOT A SCHEDULER.** <what now governs, with its path>.
> Historical `next`, `active`, and `authorized` language below records its original frame and
> does not schedule work.
```

### 1.11 What this repository deliberately does not have

Reported as negative findings, because absence is information:

- **No ledger genre.** No `LEDGER.md`, no `WORK_LEDGER.md`, no session log. Git is the log and
  `CONSTRUCTION_STATE.md` is the position. §6.1.
- **No second handoff file.** The laboratory ran three simultaneously — `AGENTS.md` (971 lines),
  `SESSION_HANDOFF.md` (116 lines), and `src/soma/STATE.md` (4,300 lines). §6.6.
- **No peer-correspondence genre.** The laboratory's `.agents/COMMUNE/` held 134 letters between
  two instruments. This repository has one instrument and no counterpart directory, and none is
  proposed. Its adversarial-review function is served by §8 of `CLAUDE.md` — grade the
  implementation, not the receipt.

---

## 2. The path a claim takes

**Four stations and two commits.** The two-commit shape is taken directly from the laboratory,
where it is verifiable in git: `667abba0` (2026-07-22 23:44:40 -0700, "Derive recursive relational
locality") touched three files and zero source; `2c451675` (2026-07-23 09:09:02 -0700, "Build
recursive relational locality") touched nine files including four Rust owners and edited the canon
section **in place**.

```
conversation          no grade           nothing here is a claim
    |
    |  DEPOSIT COMMIT — zero files under crates/ or soma/
    v
research record       full grade         the claim, its derivation, its boundary
    +
canon section         same grade         a compression, with a back-pointer
    +
claim index row       same grade         the routing entry
    |
    |  BUILD COMMIT — source, and the canon band rewritten in place
    v
implementation        implemented-exact  only after the owner has been read
    +
observation result    measured           only with a pre-registered declaration
```

### 2.1 Conversation — no grade

Nothing said in a conversation is a claim. Brandon's direct words become provenance the moment they
are quoted verbatim into a record with their date; assistant prose does not, at any length or
confidence. A conversation that ends without a deposit has produced nothing, and this is the
mechanism `canon/THE_RECOVERED_LAW.md` names as the cause of repeated re-discovery.

### 2.2 The deposit commit

Contains exactly three kinds of file and **no source**:

1. the research record, complete, with its band ending `SOURCE UNCHANGED / NO RUN`;
2. the canon section, a compression, ending with its back-pointer;
3. the claim-index row and the `research/README.md` entry.

**The falsifier is mechanical:** `git show --stat <deposit-commit> -- crates/ soma/` must be empty.
A deposit commit that touches source is not a deposit; it is a build with an undeposited claim.

Grade at this station: whatever §5.1 truth status the evidence supports and no more. A derivation
with no implementation is `proved-derived` or `interpretation`, never `established-bounded`.

### 2.3 The build commit

Contains source, and **edits the canon section in place**:

- the heading status band is **rewritten**, not appended to;
- the sentence that is no longer true is **replaced**, not left standing beside its correction;
- the claim-index row is regraded;
- a new record is deposited for what the build discovered, if anything.

The laboratory's build commit rewrote its band from
`BRANDON-AUTHORIZED DERIVATION / DEPOSITED FOR REVIEW / ... / SOMA SOURCE UNCHANGED / NO RUN` to
`BRANDON-AUTHORIZED DERIVATION + CONSTRUCTION / DEPOSITED / DIRECT MEMBRANE BUILT / BOUNDED
HOST-MEASURED / NO CUDA RUN` and deleted the sentence "Construction remains unscheduled pending
Brandon's review." That is the operation: the band is a live object, superseded in place.

### 2.4 The compression invariant

**Canon may only compress. It may never assert more than the record it points at.**

This is checkable in one direction — every canon claim must appear in the record — and it is the
rule that makes canon safe to read alone. A canon section that says more than its record has
manufactured a claim, and manufacturing a claim in a normative file is the most expensive defect
this corpus can carry.

The corollary is §3.5: a correction to a canon claim lands **in that canon section**, in place, on
the same commit. It may never live only in a smaller file. §6.3 is the laboratory case.

### 2.5 Implementation

Grade `implemented-exact` is earned by **reading the owner**, per `CLAUDE.md` §8: *"Grade the
implementation, not the receipt."* A passing test suite, a morphology counter, and prose are not
evidence that the named mechanism exists. Where receipt and code disagree, the code governs and the
receipt is regraded in place.

Two obligations attach at this station and nowhere earlier:

- **State the reach.** A receipt says *this deed returned*; it does not say *the body conducts
  through this*. Reach is a measurement over the include or dependency graph, never a target.
- **State the cost.** A cost law is a law. Reproducing what an owner returns without reproducing
  what it costs is not porting it, and where an independent implementation exists, state both
  costs.

---

## 3. Supersession

**Nothing is deleted. Everything is regraded in place.** A reader who follows an old link must land
on the correction, not on a missing file and not on the dead claim.

### 3.1 Records: the banner

A superseded record keeps its filename, its date, and its body. A blockquote banner is inserted
immediately after the H1. The form is already in this corpus at
`research/records/2026-07-11_THE_GERMLINE.md`, verbatim:

```
> **ACTIVE SUPERSESSION — RATIFIED 2026-07-14:** this file remains provenance for the path by which
> persistence and heredity were first separated. `FORMULA §L` now governs: the whole save is one
> body's continuity, not by that fact a biological germline. A real heredity face is a materially
> transported developmental construction participating in a fresh `K` and ecology; it remains OPEN.
> There is still no equal-gauge obligation, retrieval operation, or extracted bare-path database.
```

**Four mandatory slots**, in this order:

1. **Date and ratification** — when, and by whom. Brandon ratifies; the assistant proposes.
2. **What the file remains** — its surviving provenance role, stated positively.
3. **What now governs** — the exact path and section that replaced it.
4. **What remains open** — what the supersession did *not* settle.

The record's `**Truth status:**` line is changed to `historical` in the same edit. Its old grade
stays visible inside the banner so a reader can see what was withdrawn.

### 3.2 Canon: in-place band rewrite

Canon sections are not banner-marked; they are **edited**. The heading band is rewritten, the false
sentence is replaced, and a `**Superseded reading:**` line names what the section used to say and
the date it stopped saying it. A canon file that has been superseded whole takes the archive banner
(§1.10) and moves to `archive/`.

### 3.3 Whole files: the archive banner

A file that no longer governs takes the §1.10 banner as its first blockquote and stays where it is,
or moves under `archive/` with the banner. It is never deleted. The laboratory demoted 1,226,501
bytes of ledger and state this way in a single commit rather than removing them, and that was the
right call.

### 3.4 The supersession index

Every supersession edge is recorded **once**, in `THE_CLAIM_INDEX.md` §8, as a row:

```
| from (path) | to (path) | date | ratified by | what changed |
```

The index is where a reader checks whether a claim is live without opening it. Three of 314 records
currently carry a banner and no index exists (§7); every banner added from now on adds its row in
the same commit.

### 3.5 The correction-location rule

**A correction to a claim lands in the object that carries the claim, in place, on the same commit
as the correction.** A correction deposited only in a new, smaller, or adjacent file is not
deposited. This rule exists because the laboratory broke it in writing and the break is still
readable at `a07ff376` — see §6.3.

---

## 4. Cross-reference

Four link kinds, all repository-relative, all required to resolve at the commit that introduces
them. A link that does not resolve is a defect at the same level as a wrong claim, because it
produces the same outcome: a reader who cannot check.

### 4.1 Record to code — the `## Owners` block

Every research record claiming an implementation ends with an `## Owners` block naming
repository-relative paths and the symbol, one per line:

```markdown
## Owners

- `soma/life/src/suffix_ecology.rs` :: `SuffixEcology::remount`
- `soma/membrane/src/live_current.rs` :: `LiveCurrent::contact`
- `crates/holonic-engine/src/prime_ecology.rs` :: `PrimeEcology::found_axis`
```

A record with no `## Owners` block asserts no implementation, and no reader may infer one. That is
the whole function of making the block mandatory rather than conventional.

### 4.2 Code to record — the module docline

The implementing owner carries, as the first line of its module documentation:

```rust
//! Record: research/records/2026-08-06_THE_CONSTRAINT_IS_THE_CHI_THE_UNKNOWN_IS_THE_MISSING_CHART.md
```

One line, exact path, no prose. When an owner implements several records, one line each. This is
the direction that survives refactoring, because it travels with the code.

### 4.3 Canon to record — the back-pointer sentence

Every canon section ends with the record that carries its derivation:

```markdown
Complete derivation and implementation boundary:
`research/records/2026-08-06_THE_TREE_CONDENSES_FOR_FREE_THE_REMAINDER_IS_THE_DEPARTURE_FROM_A_FOREST.md`.
```

A canon section without a back-pointer is a claim with no derivation on file and is regraded to
`open` until one is deposited.

### 4.4 Record to canon — the header line

```markdown
**Canon:** `canon/THE_RECOVERED_LAW.md` §1
```

### 4.5 The round trip

The four kinds compose into a closed loop that can be walked in either direction and checked
mechanically:

```
canon section --back-pointer--> record --## Owners--> owner
     ^                            ^                     |
     |                            |                     |
     +------**Canon:**------------+---//! Record:-------+
```

**The check:** for every `## Owners` line, the named path exists and its module docline names the
record back. For every canon back-pointer, the record exists and names the canon section back. Both
directions, or the link is not deposited.

---

## 5. Grades

One vocabulary, three notations for it. The truth statuses in `canon/EPISTEMIC_GRADES.md` are the
spine and are unchanged. The laboratory's inline tokens and index letters are carried as **short
forms of the same statuses**, not as a second system, because five uncrosswalked vocabularies is
exactly what went wrong there (§6.4).

**Composition rule, from the laboratory's claim graph, verbatim:** *"Mixed grades do not upgrade one
another."* A claim carrying `D + I` is a derivation that is present in source; it is not measured.

### 5.1 Truth status — one per claim

| Grade | Meaning | Required boundary |
|---|---|---|
| `definition` | A declared term or construction. | Types, scope, construction rule. |
| `project-postulate` | A governing discipline adopted by this project. | Consistency boundary; never advertised as a theorem of all mathematics. |
| `proved-standard` | A standard external theorem in its ordinary scope. | Primary source or named trusted library theorem. |
| `proved-derived` | A theorem derived in the project. | Complete proof and dependencies. |
| `established-bounded` | A factual capability established for a declared construction or receiver family. | Exact scope plus direct implementation, formal, computational, or measured evidence. |
| `conditional` | A conclusion under named hypotheses. | Full hypothesis and dependency chain. |
| `interpretation` | A proposed structure-preserving correspondence and active theorem-finding program. | Explicit maps, limits, preserved diagram, first derivation target, and a falsifier that can fire; never an identity without proof. |
| `conjecture` | A precise unproved claim. | Testable statement and known obstructions. |
| `counterexample` | A construction refuting a stated stronger claim. | Exact refuted statement and witness. |
| `open` | A named unresolved fiber or missing capability. | Concrete missing return, coupling, proof, or receiver distinction. |
| `historical` | Preserved provenance that does not govern current construction. | Source and disposition. |

#### Interpretation is an active proof obligation

[project-postulate] An interpretation does not pass by repeatedly declaring that it is not an
identity. Its deposit names the source and target maps, the exact diagram proposed to commute, its
limits, the first theorem being attempted, and a falsifier able to fire. Work continues to a scoped
derivation, a counterexample, or a concrete residual obstruction. A derived face is promoted and
reused without upgrading the unproved remainder.

### 5.2 Evidence tags — zero or more per claim

Truth status and evidence are orthogonal. A formal checker, an implementation, or a measurement
does not by itself decide whether a claim is a definition, theorem, conjecture, or open obligation.

| Tag | Meaning | Required receipt |
|---|---|---|
| `formal-checked` | A named proof kernel accepted the declared formal statement. | Complete source, toolchain, imports, assumptions, kernel receipt. |
| `implemented-exact` | A bounded construction returned exact invariant or equality receipts. | Source, declared input family, receiver boundary, exact grade. |
| `measured` | A calibrated experiment returned receiver testimony. | Apparatus, aperture, calibration, inputs, raw receipt. |
| `computational-witness` | A finite computation witnesses a stated instance. | Reproducible construction and boundary; no silent generalization. |

There is no ordering that makes these interchangeable. A finite numerical agreement remains
evidence about its aperture; a renderer never upgrades it.

### 5.3 Inline canon tokens — the laboratory's four

Used **inside** a canon section, immediately after the claim, where a full grade block would break
the prose. These are short forms and carry no authority the §5.1 status does not.

| Token | Laboratory meaning, verbatim from `FORMULA.md` | Maps to |
|---|---|---|
| `**[EXACT]**` | *"standard, checkable mathematics"* | `proved-standard` |
| `**[DERIVED]**` | *"forced by the axioms plus a ratified stratum"* | `proved-derived` |
| `**[CHOSEN]**` | *"a convention we adopt on purpose"* | `definition` or `project-postulate` |
| `**[OPEN]**` | *"the live frontier"* | `open` |

### 5.4 Index letters — the claim graph and the retired reading

Used **only** in `THE_CLAIM_INDEX.md` and the ownership ledger, where a five-column table has no
room for a full grade. Verbatim meanings from `src/soma/THEORY_MAP.md` at `a07ff376`:

| Letter | Laboratory meaning, verbatim | Maps to |
|---|---|---|
| **M** | *"measured machine relation: implemented and observed under named controls"* | `established-bounded` + `measured` |
| **I** | *"implemented relation: present in source, with its measurement boundary stated elsewhere"* | `established-bounded` + `implemented-exact` |
| **D** | *"exact derivation: mathematical within declared definitions; not automatically physical or computational evidence"* | `proved-derived` |
| **A** | *"structural analogy: preserves a stated relation and helps pose questions, but is not an ontological identity"* | `interpretation` |
| **H** | *"open hypothesis: promising, unresolved, and not a production mechanism"* | `conjecture` |
| **R** | *"retired/rejected reading: retained to prevent its accidental return"* | `historical` |

**`R` is adopted deliberately.** A rejected reading that is deleted returns; a rejected reading
carried under `R` does not. This is the index-level form of §3's no-deletion rule.

A single topic legitimately carries more than one letter at different scopes. The laboratory's own
worked example: exact residue arithmetic is **D**, its bounded transport through the engine is
**M**, and a proposed route from that geometry to RH is still **H**.

### 5.5 Observation grades — one per pre-registered run

`MATCHED` · `DEVIATED` · `SURPRISE` · `UNREADABLE`. A `SURPRISE` is deposited as the next run's
declaration and is never same-run evidence.

### 5.6 Band tokens — the falsifiable facts

The band in a record header (§1.7) is a slash-joined list, each element checkable without reading
the body. The standing set:

`BRANDON-RATIFIED` · `BRANDON-AUTHORIZED` · `ASSISTANT DERIVATION` · `DEPOSITED FOR REVIEW` ·
`DEPOSITED` · `SOURCE UNCHANGED` · `SOURCE CHANGED` · `NO RUN` · `BOUNDED HOST-MEASURED` ·
`GPU-MEASURED` · `CONSTRUCTION UNSCHEDULED` · `SUPERSEDED`

### 5.7 The two grading rules that are not vocabulary

Carried from `CLAUDE.md` §8 because they decide grades and are invisible in a table:

- **A receipt that could not have come out otherwise carries no evidence.** Mark it `definition` or
  `historical`, not `established-bounded`.
- **A law that returns zero proves nothing about itself.** When the declared material cannot
  exercise a law, add a declared control that does, and make the grade require a non-zero return.

---

## 6. What the laboratory got wrong

Six defects, each measured at `a07ff376` and each with the rule in this file that prevents it. The
laboratory's inventions are the reason this file exists; these are the reason it is not a copy.

### 6.1 The chronological ledger grew to 899 KB before it was demoted

`src/soma/LEDGER.md` reached **12,367 lines / 899,497 bytes** and `src/soma/STATE.md` **4,300 lines
/ 327,004 bytes** — 1,226,501 bytes of turn-by-turn narration — before both were demoted with an
identical banner at commit `323522b7` (2026-07-20). That banner contains the correction:

> *"Add a focused research or observation record instead of mirroring every turn here."*

The correction is right and arrived after 1.2 MB. **Prevented by:** §1.4 and §1.11 — there is no
ledger genre in this repository, `CONSTRUCTION_STATE.md` is a position and not a log, and git is
the log.

### 6.2 Canon outgrew on-demand reading and had to say so in its own preamble

`src/soma/FORMULA.md` reached **9,718 lines / 633,803 bytes / 157 sections**. It needed a starred
`CURRENT READING RULE` naming which section currently governs interpretation, *and* a dated
`HISTORICAL READ-THROUGH` paragraph explaining what its own older preamble used to say, *and* the
instruction *"this file is read on demand, never as a chronological queue."*

The reading rule is a genuine invention and is adopted in spirit. **Needing one at all is the
defect** — it is a workaround for a file no one can hold. **Prevented by:** §1.2's size law. Canon
here is twelve small files, one mechanism each, split at roughly 600 lines rather than extended.

### 6.3 A correction was allowed to live outside the object it corrected

`src/soma/ELEMENTARY_MECHANICS.md` states, verbatim:

> *"It also corrects two overstatements in the standing record without silently rewriting that
> record: 1. the growing population in `FORMULA §CXL` is an **occurrence population**, not an
> algebraic chain; its chain is obtained only by a later linearization; and 2. deterministic
> canonicalization of the present implementation is not yet a theorem of associative, commutative,
> or causally invariant closure under arbitrary legal schedules."*

The intent — not silently rewriting the record — is correct. The execution is not: at `a07ff376`,
`FORMULA §CXL`'s heading band still reads `BRANDON-RATIFIED / BUILT / GENERALIZED JOINT REGIONAL
CLOSURE / ONE-CORE–MULTICORE–CUDA EXACT / OPEN LEADERS + DURABLE CELLULAR REST RETAINED` with no
supersession mark. **A reader of the canon section alone still gets the overstatement**, and canon
is the file people read alone.

**Prevented by:** §3.5. The correction lands in the corrected object, in place, on the same commit.
Not rewriting history and not correcting the live claim are different things; §3's banner does the
first without sacrificing the second.

### 6.4 Five grade vocabularies with no crosswalk

At `a07ff376` the corpus ran, simultaneously:

| Vocabulary | Where |
|---|---|
| `[EXACT]` `[DERIVED]` `[CHOSEN]` `[OPEN]` | `src/soma/FORMULA.md` |
| `D` `I` `M` `A` `H` | `src/soma/README.md` |
| `M` `I` `D` `A` `H` `R` | `src/soma/THEORY_MAP.md` |
| `MATCHED` `DEVIATED` `SURPRISE` `UNREADABLE` | `src/soma/OBSERVATIONS.md` |
| `ratified` `measured` `built` `open` `failed` | `.agents/COMMUNE/README.md` |

No file maps any of them onto any other. The laboratory's own `.agents/COMMUNE/README.md` names
*"fragmented vocabulary"* in its list of real observed failure modes, which is the corpus
diagnosing itself and then not treating it. **Prevented by:** §5 is a single normative crosswalk.
Every short form maps to a `canon/EPISTEMIC_GRADES.md` truth status and carries no authority beyond
it.

### 6.5 Three hundred and five research records and no index

At `a07ff376`, `git ls-tree -r a07ff376 -- src/soma/RESEARCH` returns **305 files, every one of
them a dated record**. There is no `README.md`, no index, no atlas, no disposition file. The entire
routing burden fell on filenames — which is precisely why the filenames had to be complete
declarative sentences, a genuinely excellent invention forced into existence by a missing one.

A Rust crate, `soma/tools/record-index` (2,465 lines), was eventually written to build the index
the directory never had. It is now imported here and cannot run, because
`soma/tools/record-index/src/lib.rs:192-203` discovers a root by testing for
`src/soma/FORMULA.md` and `.agents/COMMUNE`, neither of which exists in this repository.

**Prevented by:** §1.6. `research/README.md` is normative and is updated in the same commit as any
new record.

**One correction to the record about the record.** The claim that all 305 laboratory records match
the naming convention exactly is **false**. Ten do not, measured at `a07ff376`:

```
2026-07-10_ALIGN-R0.md
2026-07-10_CUT-R0.md
2026-07-10_FIBER-R0.md
2026-07-11_A1_DRIVEN_CONTINUATION.md
2026-07-12_IDENTITY_EQUIVALENCE_AND_THE_ACTION_CURRENT_ORGAN.md
2026-07-13_COLOR_IS_A_RECEIVER_FACE_THE_HIGHLIGHT_IS_THE_RELATION.md
2026-07-13_NO_WORLD_CHART_IS_THE_WORLD.md
2026-07-17_HEAT_IS_THE_INEXACT_BOUNDARY_CURRENT_TEMPERATURE_IS_THE_INTEGRATING_FRAME.md
2026-07-20_DEVELOPMENTAL_KERNEL_HYPOTHESIS_PARKED_PENDING_LABORATORY_REVIEW.md
2026-07-28_TRAINING_CONDITIONS_THE_ECOLOGY_THE_RETURN_GRADES_BEFORE_IT_ENTERS.md
```

Three of them carry an ordinal (`R0`, `A1`) in the filename, which `CLAUDE.md` bans by name. The
same ten are the only ten nonconforming names among the 314 records here — they are inherited, not
introduced, and every record deposited in this repository since extraction conforms.

### 6.6 Three simultaneous handoff documents

`AGENTS.md` (971 lines / 78,596 bytes), `SESSION_HANDOFF.md` (116 lines), and `src/soma/STATE.md`
(4,300 lines) each claimed to tell an arriving reader where the work stood. `AGENTS.md` opens by
declaring its own narrowness — *"This file does not select a research domain, schedule a
continuation, preserve an old plan, or define laboratory theory. It exists only to prevent
recurring operating failures after a fresh session or compaction."* — and then runs to 971 lines.

**Prevented by:** §1.4 and §1.11 — one position file, no siblings. **Not fully prevented, and worth
saying plainly:** `CLAUDE.md` here is 589 lines and `CONSTRUCTION_STATE.md` is 620. The contract is
within a factor of two of the laboratory's, and the same drift is available.

---

## 7. Standing defects, measured 2026-08-07

What this law does not yet describe, stated as facts rather than intentions. Each is `open`.

**The transition commit `06518c3` ("Transition to Rust: archive the C++ body, import the laboratory
machinery", 2026-08-07 13:12:16 -0700) touched zero documentation files.**
`git show --name-status 06518c3 -- CLAUDE.md CONSTRUCTION_STATE.md README.md AGENTS.md canon blueprint research`
returns empty against 1,651 renames.

**Rows struck through below were closed later on 2026-08-07** by the movement "The record names the
body it has", which rewrote `CLAUDE.md` §0/§11/§13 against the Rust body, made
`CONSTRUCTION_STATE.md` a live position record, banner-demoted eleven blueprint files, and deposited
the now-retired named-path census. It helped expose the transition damage, but was never semantic
construction authority and was removed on 2026-08-31 in favor of coherent owner review and the
manual `UNIVERSAL_CATALOG.md` crosswalk. The remaining historical rows are unchanged.

| Defect | Measurement | Genre affected |
|---|---|---|
| ~~No claim index exists~~ | **CLOSED 2026-08-10** — built and generated from the tree, so it cannot drift by hand | §1.5 |
| No supersession index exists | 3 of 314 records carry a banner; no index rows anywhere | §3.4 |
| Record atlas is stale by seven | `research/README.md` claims *"all 307 laboratory research deposits present at extraction on 3 August 2026"*; 314 records tracked, 7 dated after 2026-08-03 | §1.6 |
| Truth-status grades are nearly unused | 5 of 314 records carry a `**Truth status:**` line; 278 carry a bold band in a laboratory vocabulary with no crosswalk | §5 |
| ~~Two dead canon links~~ **closed 14:30** | `canon/06_ESTABLISHED_CAPABILITIES.md:12` and `:14` pointed at `../evidence/observations/`, which `06518c3` moved under `archive/cpp-engine/`. Both now carry the archive path | §4 |
| `README.md` reading order is pre-transition | still names `archive/blueprints/COMPLETE_CPP_ENGINE_ROADMAP.md` — now archive-bannered — as the second thing to read. Its `evidence/observations/` and `provenance/` links were repaired at 14:45; its `formal/` link now resolves, to `soma/formal/` | §1.2 |
| Observation genre is empty | `observations/` absent; 139 directories, 118 with `RESULTS.md`, sit under `archive/cpp-engine/evidence/observations/` | §1.8 |
| Ownership ledger absent; ~~lint broken~~ **lint closed 2026-08-10** | `HOLONIC_OWNERSHIP.md` still absent. The lint half is closed: both frames this row named were real — the `BASELINE_PATH` and the `src/soma/` `PROTECTED_ROOTS` — and the first hid the second, since `check_repository` reads the baseline before taking the census. Repaired; runs as the last gate of `tools/gates.sh` over 193 files and 18,203 inherited occurrences | §1.9 |
| ~~No archive banners~~ **partly closed 14:12** | eleven `blueprint/` files and `archive/cpp-engine/CONSTRUCTION_STATE.md` now carry the §1.10 banner. Still open: no file directly under `archive/cpp-engine/` or `reference/` carries one | §1.10 |
| No `//! Record:` doclines | zero owners across 282 `.rs` files name a record | §4.2 |

**None of this is scheduled here.** `CLAUDE.md` §9 governs what gets built and Brandon's latest
direct request governs that. This section exists so no reader mistakes the law for a description of
the corpus as it currently stands.

---

## 8. The one-line test

Before depositing anything, answer four questions. If any answer is missing, the deposit is not
ready.

1. **Which genre?** If two, split it.
2. **Which grade, from §5.1, and what receipt earns it?** If the receipt is prose, the grade is
   lower than you wrote.
3. **What does it supersede, and did the superseded object get its banner in this same commit?**
4. **Does the round trip close?** Canon points at record, record points at canon and at owners,
   owners point back at record.
5. **If the grade is `interpretation`, what theorem is being attempted and what falsifier can
   fire?** Restating the non-equivalence is not a return.
