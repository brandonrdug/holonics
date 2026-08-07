# Material retained only in the laboratory

The following remains available at `/home/b/Workspaces/laboratory` and its Git remote. It was not
promoted into the clean engine standing.

## Recoverable code/history

- Complete Git history and branches, especially:
  - `93834398843720bea2642852c24f37ebd7ebfe60` — checkpoint before the large Eros cleanup;
  - `a07ff376f2b936749be20ba907ecd0e2f01d544a` — admitted cleanup snapshot used for references;
  - `5cca1c5d910b922899c0296189a576aeb9a515af` — source HEAD during extraction;
  - branch `agent/eros-production-owners`.
- The complete dirty 3 August Soma worktree, including partially reviewed event/traversal and
  language/formal changes. These are evidence, not admitted reconstruction material.
- `src/soma/life/` and the larger application topology.
- Historical deleted bodies recoverable from Git: staging, generic CLI, duplicate worlds,
  navigation/physical bundles, old sessions, compatibility schemas, and rejected conductors.

## Generated/build/runtime material

Approximate sizes at extraction:

| Path | Size | Reason retained only there |
|---|---:|---|
| `target/` | 56 GiB | compiler artifacts; regenerable |
| `runs/` | 54 GiB | generated runs, rest images, model/runtime artifacts, and 412 generated Lean candidates |
| `src/soma/formal/**/.lake/` | 9.2–9.6 GiB | third-party Lean/Mathlib caches |
| `src/holobrochos/` | 21 GiB | full historical tree plus generated/build material; only theory snapshots were extracted |
| `output/` | 912 MiB | generated outputs; the ten clean paper PDFs were regenerated from extracted sources instead of copying this directory |
| `tmp/` | 431 MiB | transient renders and third-party paper downloads |
| `data/` | 274 MiB | acquired datasets with separate provenance/licensing requirements |
| `src/soma/observations/` | 269 MiB / 1,630 files | raw observer paths, bodies, renders, and populations; 190 summaries/reports were extracted |
| `.claude/worktrees/` | variable | duplicated working trees, not source authority |
| `.venv/` trees | variable | third-party environments |

## External PDFs not copied

- `tmp/pdfs/PointsAsTori.pdf` and duplicate: SHA-256
  `c3ff23b2b603ac339994419b1ed94ec7851ef65949ab895823c0ddda2ca96008`, CC BY 4.0,
  DOI `10.1145/3811385`; linked in the external-resource catalogue.
- `tmp/pdfs/computational-reflection.pdf`: SHA-256
  `04f477d7058deca5174defd8a2876786f95c8473a85a011a42962caeff795e6c`; redistribution
  permission was not established, so only the Cambridge record is linked.
- `tmp/pdfs/soma-journal-prospectus.pdf`: generated laboratory prospectus.
- Athena/publication PDFs: legacy material without a cleared publication/license boundary.

## Older formal trees

Old Labyrinth and Shrine Lean trees remain laboratory-only. They contain historical `OPEN`,
`sorry`, and axiom-bearing material. Promote individual results only after inspecting their exact
source and kernel receipt; do not copy the trees wholesale.

## Return protocol

When a clean construction needs historical evidence:

1. name the exact missing theorem, law, receipt, or asset;
2. inspect the smallest source path/commit that owns it;
3. classify its epistemic grade and contamination risks;
4. extract the exact artifact with commit/blob/hash provenance; and
5. rebuild the needed relation under the current canon—never restore a rejected subsystem.
