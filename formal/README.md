# Formal foundations

[definition] This is the single root for live project-owned Lean work. Historical formalizations
inside `archive/` are frozen provenance and do not provide missing imports to a live build.

| Project | Role |
|---|---|
| `elementary-holonics/` | Main mathematical and HNA foundation, with its default engine umbrella and independent RH/Millennium owners. |
| `kernel-witness/` | Small exterior Lean-kernel application fixture. |
| `rh-source-transport/` | Independent finite source/quotient project with its own stated obstruction. |

Run `bash tools/lean_check.sh` from the repository root, or name a focused target such as
`ElementaryHolonics.RH.CriticalChart`. See the [owner map](../docs/ARCHITECTURE_MAP.md) and
[development guide](../docs/DEVELOPMENT.md). Each project's `.lake/` is a retained, ignored cache;
the theorem sources and dependency manifests are tracked.
