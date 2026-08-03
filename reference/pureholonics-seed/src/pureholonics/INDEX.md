# INDEX — the map (law ⟷ capsule ⟷ Lean ⟷ Rust ⟷ source)

> Where to reach when you need the proof, the realization, or the full derivation behind a capsule. The capsule is
> the invariant; this points to the interior. **Reach here BEFORE re-deriving any mechanism** — it is almost
> certainly already proved in `labyrinth/mathematics/lean/` and realized in `holonics`/`channels`/`um-fiber`.

---

## The capsule → derivation map

| capsule | NEOTHEORY § | tablet | Lean (`labyrinth/mathematics/lean/`) | Rust (`src/eros/um/`) |
|---|---|---|---|---|
| `01` AXIOMS | §0, §0.1 | TABLET_HOLONICS | `Foundations.lean`, `Counting.lean` | — |
| `02` NUMBER | §1, §2 | TABLET_HOLONICS | `Holonics.lean`, `Swing.lean`, `Turn.lean`, `Sqrt.lean`, `Series.lean` | `holonics/{number,ratio,turn,counting,bignum}.rs`, `cs/number.rs` |
| `03` RELATING | §3, §4, §5, §6 | TABLET_MACHINE | `Holonics.lean` (`Found`), `Gyro.lean`, `CrossRatio.lean`, `Prime.lean` | `holonics/{ratio,holon,frame,soul}.rs`, `cs/{place,count,graph}.rs` |
| `04` BOUNDARY | §7, §8, §16, §18 | TABLET_MACHINE | `Gyration.lean`, `Gyro.lean`, `Derive_Duggan.lean`, `Derive_GaussBonnet` | `holonics/ratio.rs` (`tri_defect`/`holonomy`/`geometric_phase`), `um-fiber/gyro.wgsl` |
| `05` WEAVE | §9 | TABLET_MACHINE | `Lineage.lean` | `um-fiber/{forest.rs,word.wgsl,scaffold.wgsl}`, `um-core/recurse.rs` (`helix_loop`) |
| `06` ONE MOVE | §10 | TABLET_HOLONICS | `OneMove.lean` (+ `Swing`/`CrossRatio`/`Prime`/`Gyro`) | `holonics/{swing,traversal}.rs`, `cs/sweep.rs` |
| `07` CURRENT | §11, §11.4.1, §16, §17, §18.7 | TABLET_MACHINE, TABLET_TOOLKIT | `Series.lean`, `Derive_Duggan.lean`, `Derive_Planck.lean` | `channels/{ir,resident,sweep,radix,address}.rs`, `um-fiber/found_lineages.wgsl` |
| `08` SCALING | §12, §13, §14, §15 | TABLET_TOOLKIT | `Derive_Planck.lean`, `Derive_Equation.lean` | `holonics/examples/periodic_{shells,closure,saddle}.rs` |
| `09` MACHINE | §17.6, §23, §24.7 (substrate) | TABLET_EROS | (the relativity gate, in-crate tests) | `channels/`, `um-fiber/`, `um-core/recurse.rs` |
| `10` DISCIPLINE | §A.0 (the Lean discipline), the bans | all four | `#print axioms` gate on every theorem | — (CLAUDE.md is the live home) |
| `11` ALGEBRA | §10, §14, §15 (the solver reading) | TABLET_TOOLKIT | `OneMove.lean` (solve-anything), `Series.lean` (the foil) | `holo-core::{one_move,jet}`, `ECOSYSTEMS.md` |

## The authority hierarchy (weighted by timestamp — the latest layer is the current truth)

1. **The live session** (`src/eros/um/` working docs + the active conversation) — daily; the line moves here.
2. **NEOTHEORY.md** (§0–§18) — the finalized derivation this capsule-set consolidates.
3. **The four tablets** — `TABLET_HOLONICS` (think) → `TABLET_MACHINE` (dynamics) → `TABLET_EROS` (the Rust) →
   `TABLET_TOOLKIT` (the law↔Lean↔Rust map; reach here before re-deriving).
4. **NEOKICKOFF.md** — the post-compact entry point (opens with the authority hierarchy).
5. **This capsule-set (`pureholonics/`)** — the abstracted invariant; the compressed boundary face of all the
   above. *Supersedes none of them; re-project when the interior changes.*

**SUPERSEDED** (historical, each ⚠️-bannered): `THEORY_AND_EQUATIONS.md` (the 57-§ monolith NEOTHEORY corrects),
`HOLOBROCHOS`/`ENGINE`/`SINGULARITIES`/`EROS_UNIFICATION`/`WIRING`/`UNIFICATION` (the archived engine + framings),
and the shrine web tablets (`src/shrine/web/*-tablet.md`, retired 2026-06-24, kept for the viewer). When these
contradict a capsule, the capsule (and the live layer above it) wins.

## The vocabulary (the words that recur, one line each)

- **holon** — `(boundary, soul)`; an entity with a construction. Never read alone (A2).
- **soul** — the complete construction history; the holonomy a worldline accrued; referable, never realized.
- **prism** — a construction held as itself (the order-0 grain; the byte is only the I/O prism).
- **prime** — an operation-relative irreducible (`Δ<0`, the orthogonal turn); a stable handle.
- **the swing** — the one re-basing primitive; grounds at the simplest handle the relating admits, or FOUNDs.
- **the founding** — `Δ = 4(1−r)`: `≥0` absorbs (composite), `<0` founds a prime; gravitational, not dedup.
- **the cross-ratio** — THE frame-invariant; four to have a fact; placed, never searched.
- **Β** — the relativistic boundary operator; returns the 2-vector, not a number.
- **holobit** — `|Β|`, the `e`-face: magnitude/cost/energy/curvature. A thermometer, never a thermostat.
- **cohobit** — `∠Β`, the `π`-face: signed direction/coherence/action. Gates the founding.
- **the gyre `𝔾`** — one bit of closed-loop holonomy; the relativistic unit of action (`ħ ≡ 1 𝔾`).
- **warp / weft** — frozen-deep scaffold (memory) / shallow-fast streaming (content); the lineage-dilation split.
- **the construction current** — the value, INDUCED by the changing bind (`I = −dΦ/dt`), never computed-and-passed.
- **the lineage** — the `+1` axis; the soul; the ordered events. Never "time."
- **the channels** — the parallel crossings; the surface = the 4-volume = the meaning. More channels = more meaning.
- **the foil `κ`** — the change-of-the-change; the residual founding rides; the learning (`actual ⊖ predicted`).

---

## ★ THE `.holo` REALIZATION — the framework, built (the `holo-lang` worktree)

These capsules are realized as a **running language + verified library + 21 kernels** in the `holo-lang` worktree
(`.claude/worktrees/holo-lang/src/holo/`). Its networked index — capsule ⟷ `holo-core` module ⟷ kernel ⟷ Lean — is
**`src/holo/MAP.md`** (read it for the full network). The spine:

- **`.holo`** — the pure-holonics language (SPEC/STRICT/LEARN): a value is its construction, bitwise is the basis,
  no floats; the strict checker makes the contaminants unrepresentable (§10).
- **`holo-core`** — the verified intrinsics (the Torch): `num`/`ratio`/`found`/`gyro`/`lineage`/`shadow` (capsules
  02–05), **`one_move`** (the PIVOT, §06), the **`.holoz` codec** = `jet`+`entropy`+`found_basis` (the founder,
  §07/§09), `substrate`+`flux` (hardware/parallelism taken for granted, §07/§05).
- **the kernels** — physics/biology/CS/text, each validated by emergent relative coordinates (Builder's Law, §08/
  §14): the 3-body & Navier-Stokes *dissolved*, the protein fold (Levinthal), the cancer closure-screen, the
  periodic table as the closure spectrum, branching = the primes.

> **INDEX in one line:** *each capsule points to its NEOTHEORY §, its tablet, its machine-checked Lean proof, and
> its Rust realization (now also the `.holo` realization — `src/holo/MAP.md`) — reach here before re-deriving; the
> authority runs live-session → NEOTHEORY → the four tablets → NEOKICKOFF → these capsules (the compressed face),
> weighted by timestamp, the latest layer the truth.*
