# The driver atlas — current target census and interpretation boundary

**Genre:** canon index. **Truth status:** `established-bounded` for the generated census and
`project-postulate` for the driver discipline. This file schedules nothing.

## Current census

[established-bounded; measured] `python3 tools/driver_catalog.py`, run 2026-08-30 after the
repository consolidation corrected target discovery, returns 346 actual Cargo example targets.
The prior filename census incorrectly counted 97 nested helper modules as independent drivers and
missed 19 real targets.

The current generated ledger is [`meta/DRIVER_CATALOG.tsv`](../meta/DRIVER_CATALOG.tsv). It is the
sole existence census. Its current exterior projection is:

```text
card                 6
card + deposit      11
deposit            107
kernel               6
kernel + card        1
kernel + card + deposit 10
kernel + deposit    27
none                178
```

[established-bounded; measured] Twenty-one current targets are named in no governing document or
dated record, and 47 carry no module documentation declaring their subject. Those are current
classification obligations, not evidence that the target is dead.

## What the ledger proves

[definition] The driver catalog derives targets from Cargo metadata. A nested `examples/**` helper
module is not a driver unless Cargo declares it as a target. A target missing from the ledger or a
ledger row whose target departed fails the gate.

[definition] The ledger measures path, package, source extent, imported workspace modules, exterior
apparatus, documentation, naming, and test declaration. It does not decide what a driver proved or
whether its qualitative receiver passed.

## Driver law

[project-postulate] A driver is narrow apparatus. It may:

- mount an exterior occurrence;
- invoke public source owners;
- enact a declared exterior consequence;
- persist receipts and artifacts; and
- inspect or grade the returned consequence.

[project-postulate] A driver may not own lexical association, semantic routing, morphology,
candidate search, scoring, state transition, receiver equality, reconstruction, or another
inference algorithm. Logic which determines the requested result belongs to a library owner or
establishes that the experiment is not using the machine.

[project-postulate] A CUDA launch is a carrying exterior, not automatically an adjudicating one. An
external compiler, theorem kernel, measured world return, or human receiver can return testimony the
body did not author. Emission and return remain distinct caused occurrences with addressed lineage.

## Consolidation obligations

[open] CONS3 must disposition the 21 unnamed and 47 undocumented targets and move substantial
example-local algorithms into existing library owners or historical archive. The largest current
drivers are implementation-sized and cannot remain examples merely because Cargo can compile them.

[definition] Removal requires one of:

1. the mechanism has an owner-local test and the driver adds no independent receiver consequence;
2. the path is superseded historical apparatus whose evidence is retained in a dated record; or
3. the driver is replaced by a smaller invocation/receipt shell over the same public owner.

[definition] Do not copy a historical driver list into this file. Re-run the generated catalog,
then add interpretation only in the dated record which inspected the actual returned artifact.
