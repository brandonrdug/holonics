# Expression atlas

Agent context, not for human reading. It catalogues the derived expressions, identities, bounds and
constructions that exist in this repository, each stated on the elementary objects, with its owner.
The essential laws are in CLAUDE.md/AGENTS.md and the operator contract, which are always in
context. This atlas holds the rest.

Use it before deriving, designing or claiming absence. Grep it for the objects, operations and
classical names of the subject, read the matched rows, then open the owner.

```bash
rg -i 'contact|DQ|slip' docs/atlas/          # by object or operation
rg -i 'Foster|Weil|de Bruijn' docs/atlas/     # by classical name
rg '^ratio\.' docs/atlas/objects.tsv          # by id prefix
```

## Shards

| File | Subject |
|---|---|
| `objects.tsv` | The elementary objects and their direct derived laws: complex, Holon/coholon, constitution, navigator, Swing, pair contact, parametron, tube/tower, globe, deposition, ratio, receipt, Holarchy, aeon/epoch/cycle, compression, keys. |
| `geometry.tsv` | Winding, carry, lock addresses (Farey), trace faces and zeta, cell holonomy, screws, helical pair and serial chain, frames and Cayley charts, jets, towers (Iwasawa), fractal packing, Swing charts, curvature. |
| `information.tsv` | Learning covector, loss as log ratio, KL and physical cross-entropy, code cost and description length, navigator inference, relevance kernel, receiver-history compression, the softmax ratio family and normalization, Preimage Fibre, standing and release, Holonic Encoding, context, joint prediction. |
| `physics.tsv` | Port-Hamiltonian/Dirac, induction and Maxwell, Einstein and stress-energy, mass–energy, heat and entropy production, fluids (complex Euler, Navier–Stokes), waves, Lorentz/Minkowski, quantum readings. |
| `arithmetic.tsv` | Ratio series and partial navigators (π, `e`, Machin), radix windows, prime valuation, primality, exact and modular linear algebra, rational polynomials, Jacobi/theta, Hecke–Euler, analytic navigation. |
| `targets.tsv` | RH (Foster tanks, zero-pair lock, de Bruijn–Newman, Copson–de Bruijn, ξ, spectral placement); Hodge (receiver, index, barycentric, cycle production, integral obstruction); Navier–Stokes (Lamb current, vorticity, H-classes, relevance tail); BSD (descent, family kernel, Tunnell, cokernel calculus); Yang–Mills gap readings. |

## Row format

Tab-separated, one expression per line, no header row, UTF-8. Mathematical notation is Unicode in
[Holonic notation](../HOLONIC_NOTATION.md): kets `|H⟩`, bras `⟨Ȟ|`, faces `⟨Ȟ|H⟩`, navigators `Ĝ`,
ratios `R=Ĝ_(T←H)`. Plain ASCII such as `->`, `<=` and `sum_k` is allowed where Unicode is awkward.

| # | Field | Content |
|---|---|---|
| 1 | `id` | Stable slug: `<object-or-subject>.<name>`, lowercase, hyphenated (`contact.dq-adjoint`, `rh.zero-pair-lock`). |
| 2 | `objects` | Comma list from: `complex, holon, coholon, constitution, navigator, swing, contact, parametron, tube, tower, globe, deposition, ratio, receipt, receiver, holarchy, aeon, epoch, cycle, compression, key, landmark`. |
| 3 | `expr` | The expression, exact: an equation, identity, inequality, map, or construction. No floats; integers keep their factorization. |
| 4 | `reads` | What it says, in one clause, in current vocabulary. |
| 5 | `scope` | The hypotheses and domain, tersely (`finite complex`, `PSD M`, `σ∈(0,1)`, `n≥1`). Empty only if none. |
| 6 | `owner` | Where it lives. Several owners are separated by `; `. Lean: `L:<Dir>/<File>:<decl>`, with the path relative to the library root (`lean/Holonics/` or `lean/HolonicsResearch/`) and no namespace, so moving a module between the libraries does not break it. Rust: `R:<crate>::<path>::<item>`. Guide: `D:<file>#<anchor>`. Record: `N:<record filename>`. Paper: `P:<path under research/papers/source/>`. History: `H:<path>` at `13f8c734`. |
| 7 | `grade` | One of `definition`, `proved-derived`, `proved-standard`, `formal-checked`, `counterexample`, `interpretation`, `open`. |
| 8 | `rel` | Related ids, as `kind:id`, comma-separated. Kinds: `uses`, `instance-of`, `dual-of`, `specializes`, `generalizes`, `face-of`, `obstructs`, `equiv`. |

## Maintenance

A change that adds, moves or retires an expression's owner updates its row in the same commit. A module moving between `Holonics` and `HolonicsResearch` rewrites no `L:` rows, because the paths are relative to the library root. A
retired Rust owner becomes `H:`.
