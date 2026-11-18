# Expression atlas

Agent context, not for human reading. It catalogues the derived expressions, identities, bounds and
constructions that exist in this repository, each stated on the elementary objects, with its owner.
The essential laws are in CLAUDE.md/AGENTS.md and the operator contract, which are always in
context. This atlas holds the rest.

Use it before deriving, designing or claiming absence. Grep it for the objects, operations and
classical names of the subject, read the matched rows, then open the owner.

A lens that arrives in a discipline's language (music, lightning, a vortex ring, a cipher, a
packing, a zeta function) is routed through [the charts](CHARTS.md): the object and the operation
the discipline is a chart of, the row prefixes that already hold it, and what stays behind in the
discipline.

```bash
rg -i 'contact|DQ|slip' docs/atlas/          # by object or operation
rg -i 'Foster|Weil|de Bruijn' docs/atlas/     # by classical name
rg '^ratio\.' docs/atlas/objects.tsv          # by id prefix
```

## Shards

| File | Subject |
|---|---|
| `objects.tsv` | The elementary objects and their direct derived laws: complex, Holon/coholon (`holon.*`), constitution, navigator, the Swing's half-turn family (`swing.*`), pair contact, parametron, tube/tower, globe, deposition, ratio, receipt, Holarchy, aeon/epoch/cycle, compression, keys, landmarks, inertia. It also holds the HNN (`hnn.*`, rebuild steps 4–5: field, moments, propagation and junction scattering, word, receiving, retention, keys), which is machinery built from the objects, not an object. |
| `geometry.tsv` | Winding, carry, lock addresses (Farey), trace faces and zeta, cell holonomy, screws, helical pair and serial chain, frames and Cayley charts, jets, towers (Iwasawa), fractal packing, curvature, the egg. **Motion** (`motion.*`: the turn/boost split against a receiver's metric, the port-Hamiltonian reading, pivots, the three kinds of quadratic motion, Iwasawa `KAN`, the sling, the traction disk, the path jets and the moving-metric energy law); the chase terrain (`pursuit.*`); two `swing.*` charts. |
| `information.tsv` | Learning covector, loss as log ratio, KL and physical cross-entropy, code cost and description length, navigator inference, relevance kernel, receiver-history compression, the softmax ratio family and normalization, Preimage Fibre, retention (historical `standing.*` ids) and release, Holonic Encoding, context, joint prediction, and the population receivers and their checkpoints (`receiver.*`). |
| `physics.tsv` | Port-Hamiltonian/Dirac, induction and Maxwell, Einstein and stress-energy, mass–energy, clocks, heat and entropy production, fluids (complex Euler, Navier–Stokes), waves, Lorentz/Minkowski, quantum readings. |
| `arithmetic.tsv` | Ratio series and partial navigators (π, `e`, Machin), radix windows, prime valuation, primality, rational and modular linear algebra, rational polynomials, Jacobi/theta, Hecke–Euler, analytic navigation. |
| `targets.tsv` | RH (Foster tanks, zero-pair lock, de Bruijn–Newman, Copson–de Bruijn, ξ, spectral placement, hearing); Hodge (receiver, index, barycentric, cycle production, integral obstruction); Navier–Stokes (Lamb current, vorticity, H-classes, relevance tail); BSD (descent, family kernel, Tunnell, cokernel calculus); Yang–Mills gap readings. It also holds the **couplings** (`coupling.*`): the receiver-form joins shared across targets (the closure staircase, Swing words, sling transport, frame questions, lattice gauge), which the targets consume. |

## Row format

Tab-separated, one expression per line, no header row, UTF-8. Mathematical notation is Unicode in
[Holonic notation](../HOLONIC_NOTATION.md): kets `|H⟩`, bras `⟨Ȟ|`, faces `⟨Ȟ|H⟩`, navigators `Ĝ`,
ratios `R=Ĝ_(T←H)`. Plain ASCII such as `->`, `<=` and `sum_k` is allowed where Unicode is awkward.

| # | Field | Content |
|---|---|---|
| 1 | `id` | Stable slug: `<object-or-subject>.<name>`, lowercase, hyphenated (`contact.dq-adjoint`, `rh.zero-pair-lock`). |
| 2 | `objects` | Comma list from: `complex, holon, coholon, constitution, navigator, motion, swing, contact, parametron, tube, tower, globe, deposition, ratio, receipt, receiver, holarchy, aeon, epoch, cycle, compression, key, landmark`. `motion` is the Swing as the move about a grip (turn, boost, free fall, pivots, the sling, path jets; `Geometry/Motion`); `swing` is the half-turn `S_a x = 2a − x` and its older charts (harmonic conjugation, the pantograph, the clocked pantograph). |
| 3 | `expr` | The expression in full: an equation, identity, inequality, map, or construction. No floats; integers keep their factorization. |
| 4 | `reads` | What it says, in one clause, in current vocabulary. |
| 5 | `scope` | The hypotheses and domain, tersely (`finite complex`, `PSD M`, `σ∈(0,1)`, `n≥1`). Empty only if none. |
| 6 | `owner` | Where it lives. Several owners are separated by `; `. Lean: `L:<Dir>/<File>:<decl>`, with the path relative to the library root (`lean/Holonics/` or `lean/HolonicsResearch/`) and no namespace, so moving a module between the libraries does not break it. Rust: `R:<crate>::<path>::<item>`, the crate as Rust writes it (`holonics_engine`, `holonics_engine_cuda`, `athena`), or `R:<path>:<item>` for a Rust file no crate builds (the notebook's harnesses). A host tool or a test: `T:<path>` or `T:<path>:<name>`. A kernel source: `K:<path>` or `K:<path>::<kernel>`. Guide: `D:<file>#<anchor>`. Record: `N:<record filename>`, with its `.md`. Paper: `P:<path under research/papers/source/>`. History: `H:<path>` at `13f8c734`, or `H:<path>@<commit>` (with the item where it helps, `H:<path>:<item>@<commit>`) for an owner retired later (the last commit that held it): `d5ed4adc1` holds the October library `crates/holonics`, `d6bbd1644` its card crate `crates/holonics-cuda`, and `8a77b7755` the library's examples. A note may follow an owner after a space. |
| 7 | `grade` | One of `definition`, `proved-derived`, `proved-standard`, `formal-checked`, `counterexample`, `interpretation`, `open`, or `measured` for a row whose statement is a reading of the machine, with its record as an owner ([the grades](../canon/EPISTEMIC_GRADES.md) keep truth status and evidence apart; this field holds whichever the row rests on). 63 rows of the September and October machines, each with an `H:` owner, keep in this field the dated status they were written with (`implemented-exact; Lean owed #62`, `native-checked …`): it is that date's reading of a retired owner, and a row that is taken up again is graded then. |
| 8 | `rel` | Related ids, as `kind:id`, comma-separated, read from this row to the target. Kinds: `uses` (this row consumes the target), `instance-of` (this row is a case of the target's construction), `specializes` / `generalizes` (this row's law is a special case of the target's / contains it as a case), `equiv` (the same law in another chart or shard), `face-of` (a reading of the target), `dual-of`, `obstructs` (a counterexample or barrier to the target). No other kind is used. |

## Maintenance

A change that adds, moves or retires an expression's owner updates its row in the same commit. One
law has one row where the rows are literally the same statement; two charts of one law keep their
rows and join them with `equiv`, and a case of a general row names it with `specializes`. When two
rows merge, the surviving id keeps the union of owners and relations, and every `rel` to the
retired id is repointed. A module moving between `Holonics` and `HolonicsResearch` rewrites no
`L:` rows, because the paths are relative to the library root. A retired Rust owner, test or kernel
becomes `H:` with its commit, and an owner that stands in the tree is never written as `H:`.

`python3 tools/link_check.py atlas` reads every owner against the tree: an `R:`, `T:` or `K:` owner
resolves to a tracked file and a name declared in it, an `L:`, `D:`, `N:` or `P:` owner to its file
(with its declaration's name or its anchor), and an `H:` owner with no commit names no path of the
tree. It prints one line an owner that does not resolve. Run it after a change that moves or retires
an owner.
