# Formal Holonics

[definition] This is the root for live project-owned Lean work. The main library presents a
mathematical framework of situated objects, causal interaction, transport, geometry and
receiver-relative information, with physical and computational realizations. Start with
[Holonics in Lean](elementary-holonics/README.md) and the
[framework synthesis](../docs/FORMAL_FRAMEWORK.md).

| Project | Role |
|---|---|
| `elementary-holonics/` | Reusable framework and its independent mathematical applications; default import/build is `ElementaryHolonics.Framework` |
| `kernel-witness/` | Small exterior Lean-kernel application fixture |
| `rh-source-transport/` | Independent finite source/quotient project with its own stated obstruction |

[definition] `ElementaryHolonics` remains the complete research umbrella. Historical author and
problem labels preserve attribution and exact statement lineage; subject entry points expose
reusable relations across them. Historical formalizations inside `archive/` are provenance and
supply no fallback imports to a live build.

[definition] Run `bash tools/lean_check.sh` from the repository root, or name an explicit target.
The [owner map](../docs/ARCHITECTURE_MAP.md) and [development guide](../docs/DEVELOPMENT.md) connect
formal and executable owners. Each project's `.lake/` is an ignored retained cache; sources,
toolchains and dependency manifests are tracked. Lean verifies mathematics outside all HNN
cultivation and inference.
