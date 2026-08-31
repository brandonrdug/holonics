# Epistemic grades

Every material claim receives exactly one truth-status grade and zero or more evidence tags. Truth
status and evidence are orthogonal: a formal checker, implementation, or measurement does not by
itself decide whether a claim is a definition, theorem, conjecture, or open obligation.

## Truth-status grades

| Grade | Meaning | Required boundary |
|---|---|---|
| `definition` | A declared term or construction. | Types, scope, and construction rule. |
| `project-postulate` | A governing discipline adopted by this project. | Consistency boundary; never advertised as a theorem of all mathematics. |
| `proved-standard` | A standard external theorem in its ordinary scope. | Primary source or named trusted library theorem. |
| `proved-derived` | A theorem derived in the project. | Complete proof and dependencies. |
| `established-bounded` | A factual capability/result established for a declared construction or receiver family. | Exact scope plus direct implementation, formal, computational, or measured evidence. |
| `conditional` | A conclusion under named hypotheses. | Full hypothesis and dependency chain. |
| `interpretation` | A proposed structure-preserving correspondence and active theorem-finding program. | Explicit maps, limits, preserved diagram, first derivation target, and a falsifier that can fire; never an identity without proof. |
| `conjecture` | A precise unproved claim. | Testable statement and known obstructions/counterevidence. |
| `counterexample` | A construction refuting a stated stronger claim. | Exact refuted statement and witness. |
| `open` | A named unresolved fiber or missing capability. | Concrete missing return, coupling, proof, or receiver distinction. |
| `historical` | Preserved provenance that does not govern current construction. | Source and disposition. |

## Interpretation is a theorem-development state

[project-postulate] An `interpretation` is not a terminal disclaimer. Once its source and target
maps, preserved diagram, limits, first derivation target, and falsifier are deposited, work proceeds
until it returns a scoped derivation, a counterexample which narrows or kills the bridge, or a
concrete residual obstruction. Repeating the non-equivalence boundary is not a returned
consequence. A proved subclaim receives its own `proved-derived` grade and becomes a dependency of
the next claim; it does not silently upgrade the rest of the correspondence.

## Evidence tags

| Tag | Meaning | Required receipt |
|---|---|---|
| `formal-checked` | A named proof kernel accepted the declared formal statement. | Complete source, toolchain, imports, assumptions, and kernel receipt. |
| `implemented-exact` | A bounded construction returned exact invariant/equality receipts. | Source, declared input family, receiver boundary, and exact grade. |
| `measured` | A calibrated experiment returned receiver testimony. | Apparatus, aperture, calibration/bounds, inputs, and raw or summarized receipt. |
| `computational-witness` | A finite computation witnesses a stated instance. | Reproducible construction and boundary; no silent generalization. |
| `source-inspected` | Direct inspection of a named source revision supports the claim without executing it. | Exact revision, path, line/construct anchors, dependency boundary, and the inference drawn from them. |
| `source-audit` | A declared source or dependency closure was searched for presence, absence, reachability, or contamination. | Exact revision, complete aperture, reproducible command or traversal, and every excluded root. |
| `process-audit` | Process chronology, repetition, timeout, exit, or validation cadence supports the claim. | Exact command, source/input closure, start/end or elapsed time, exit status, and disposition. |

## Imported synopsis crosswalk

- Synopsis `identity` is treated as `proved-derived` only when the displayed derivation and its
  dependencies are complete; otherwise it is `conditional` or `historical` as declared locally.
- Synopsis `historical-toy` maps to `historical`, optionally tagged `computational-witness` for its
  bounded instance.
- A synopsis entry's own grade remains authoritative for that entry; extraction does not upgrade
  it.

Wording follows the claim's single declared truth-status; dependency chains expose every
`conditional`, `conjecture`, and `open` premise. There is no ordering that makes `formal-checked`,
`implemented-exact`, or `measured` interchangeable. A finite numerical agreement remains evidence
about its aperture; a renderer never upgrades it. A theorem can coexist with an open
implementation, and an exact implementation can remain theoretically open beyond its declared
receiver family.
