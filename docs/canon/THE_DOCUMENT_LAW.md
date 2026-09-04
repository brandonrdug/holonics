# The document law

**Reconciled 2026-09-04 under Brandon's consolidation instruction.**
**Truth status:** `project-postulate` — repository documentation discipline, not mathematics.

The former document law is preserved in
[the pre-consolidation record](../../archive/operations/DOCUMENT_LAW_BEFORE_HNA_CONSOLIDATION.md).
Its mandatory generated index, metadata checks, census, document-size rules and two-commit ritual
are superseded. They are historical practices, not obligations on current work.

## Authority and location

Brandon's latest direct instruction governs. Documentation makes the actual work legible; it
does not create another approval layer for the sole human operator.

| Material | Home and responsibility |
|---|---|
| Operating contract | Root `AGENTS.md`; `CLAUDE.md` points to it without copying policy. |
| Construction order | `docs/plans/THE_ROADMAP.md` and its explicitly admitted current plan. |
| Current position | Root `CONSTRUCTION_STATE.md`, concise and updated when the work changes. |
| Architecture and interfaces | `docs/ARCHITECTURE.md`, the Soulkiller/Athena/interoperability guides, and the actual public source owners. |
| Doctrine | `docs/canon/`, with explicit grades and decisive evidence. |
| Evidence | `research/records/`, experiments, papers and formal source at their declared scopes. |
| Navigation | The repository layout, subject guides, manual `docs/ARCHITECTURE_MAP.md` and exterior Provenance graph. |
| Superseded material | `archive/`, dated and retained as provenance; it schedules nothing. |

Historical evidence inside a doctrinal file stays historical. A date, filename, old imperative,
test count or confident agent assertion cannot promote it into present authority.

## Claims and corrections

Every material claim carries one truth-status grade and applicable evidence tags from
[EPISTEMIC_GRADES.md](EPISTEMIC_GRADES.md). Separate the mathematical statement, its hypotheses,
implementation, measured receiver scope and intended product. A summary must not assert more than
its evidence. Formal acceptance, numerical agreement and useful application behavior answer
different questions.

Correct a false live statement where it occurs, and link its decisive evidence or retraction.
Keep measured and quoted historical content intact; explain subsequent narrowing explicitly.
Use dated records for substantial returned results, not as a compulsory ceremony for every edit.
Code, its documentation and its tests may be committed coherently together.

Preserve obsolete material recoverably before archiving. The archive path and a concise
supersession note identify its disposition; no second ledger or mandatory supersession index is
required. Age helps recover forgotten work, but does not decide whether its subject is obsolete.

## Navigation and maintenance

Use direct links to the relevant source or subject guide. Update the manual owner map when its
owner changes. Do not maintain file counts, regenerate an all-repository index or create another
catalogue merely to keep a previous catalogue current. Provenance supersedes the local equation
atlas; that atlas and the old generated claim index are archived.

Maintain documentation when the subject changes. Review the links and claims actually affected.
Do not make untouched Typst papers, document regexes, heading conventions or source-size ledgers
conditions for an unrelated code change. The relevant Cargo, native and Lean checks are described
in [the development guide](../DEVELOPMENT.md); no blanket validation suite is required.

Keep the root position and roadmap free of running audit diaries. Completed history belongs in
its existing records and Git. A completed position may be `NONE`; neither navigation nor an
agent's desire for another task creates construction authority.
