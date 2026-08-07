# Extraction provenance

## Source

- Repository: `https://github.com/brandonrdug/laboratory.git`
- Local source: `/home/b/Workspaces/laboratory`
- Source branch: `agent/eros-production-owners`
- Source HEAD at extraction: `5cca1c5d910b922899c0296189a576aeb9a515af`
- Source worktree: dirty; the dirty Soma implementation was not accepted as engine authority.
- Extraction date: 2026-08-03 (America/Los_Angeles)

## Disposition

| Destination | Source | Files | Disposition |
|---|---:|---:|---|
| `research/records/` | working-tree `src/soma/RESEARCH/` | 307 | Complete research record, including the contemporary carrier-neutral record. Chronological evidence. |
| `papers/source/` | working-tree `src/soma/PAPERS/` | 172 | Complete authored paper source. Synopsis/registry is canonical spine; other publications are supporting/historical by their own grades. |
| `papers/rendered/` | regenerated from extracted Typst source | 10 | Generated presentation artifacts, including the previously absent categorical paper. Not proof authority. |
| `formal/` | working-tree `src/soma/formal/` excluding `.lake/` and `target/` | 24 | Project-owned Lean source, toolchain, and manifests. |
| `evidence/observations/` | working-tree observation `README.md`, `RESULTS.md`, `REPORT.json` | 190 | Human-readable/structured receipts; raw observer material remains laboratory-only. |
| `reference/engine-a07ff376/` | Git commit `a07ff376f2b936749be20ba907ecd0e2f01d544a` | 211 | Pinned admitted cleanup snapshot; reference only. Includes engine/structure/language, relational geometry, architecture lint, ABI/body/membrane/mount, ownership, baseline, lock/config. |
| `reference/pureholonics-seed/` | Git commit `d6d70076fe64467724efe5d8690f44c2c615abb7` | historical | First tracked compact capsules. |
| `reference/compact-formula-2a5dff8/` | Git commit `2a5dff815d0f0ba8f8e70d3cb4f0a70831834cb4` | 1 | Exact 149-line formula. |
| `reference/soma-seed-2695ca0/` | Git commit `2695ca0f44606f3744e52934000a749a5cc4a268` | 1 | Exact first 256-line Soma formula. |
| `reference/minimum-mechanics-a07ff376/` | Git commit `a07ff376...` | 2 | Minimum mechanics and mathematical research network. |
| `reference/holobrochos-a07ff376/` | Git commit `a07ff376...` | historical | Broader theory/canon provenance, not current doctrine. |

The rendered papers were regenerated with Typst 0.15.1 after five presentation-syntax repairs,
three portable documentation/link repairs, and two dead-reference URL repairs in the clean copy.
[`PAPER_TRANSFORMS.tsv`](PAPER_TRANSFORMS.tsv) records every transformed path with source and clean
SHA-256 values. The laboratory source was left unchanged; the clean source and PDFs compile
together. New Computer Modern Mono remains an external font requirement for byte-for-byte
typographic reproduction; fallback affects presentation, not mathematical standing.

The engine snapshot intentionally precedes source HEAD. The later working tree includes unadmitted
and partially reviewed changes across foundational code. Those changes remain recoverable in the
laboratory and are not silently promoted here.

## Formal boundary

The extracted formal projects pin Lean/Mathlib 4.27.0. The project-owned active sources contain no
`sorry`, `admit`, or declared axioms according to the extraction audit. `rh-source-transport` keeps
its analytic proportional/positivity obstruction explicit and does not prove or disprove RH.

## Licensing

No license is granted by this extraction. The laboratory Rust manifests declare
`MIT OR Apache-2.0`, but the source repository contains no corresponding root license texts, and
the authored papers/formal sources have no explicit license. The new repository is private. Before
any public distribution, Brandon must choose the copyright/licensing scope and add the actual
license texts. Third-party works are linked, not vendored, unless their license is separately
recorded.

## Integrity

`SHA256SUMS` is generated at the repository root after the extraction is complete and records every
tracked file except itself. Git commit identity provides the repository-level immutable receipt.
