# Two coupled planes' turns are free, the carry is a class of order n, and friction keeps only the harmonic part, in Lean

November 19, 00:40 UTC. The seventh formalization pass over #410, its third set, after
[the second](2026-11-19_A_POOLS_BEST_FACE_IS_ITS_LEADING_EIGENVECTORS_LEVEL_TWO_IS_FREE_ON_TWO_CARRIES_A_SOFTMAX_RELEASE_FALLS_BY_THE_ENTROPY_TWO_PASSES_APART_AND_A_CONSERVED_FACE_IS_A_CONGRUENCE_IN_LEAN.md)
(#1007). Three new modules of `lean/HolonicsResearch`, each elaborated at the package's toolchain with no `sorry`, no
`axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #404, #73, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Geometry/QuaternionFreePair` | The turns by `1 + 2i` and `1 + 2j` generate a free group of rank two in SO(3) (`rotation_wordMap_injective`). Modulo five every letter has norm zero, and the identity `y m y = 2 Re(y m) y − N(y) m̄` (`mul_mul_self`) makes the norm-zero quaternions act as rank-one matrices with no matrix built: a reduced word's product keeps its first letter's left annihilator and is not zero (`annihilator_prod`, `prod_letter_ne_zero`). Over `ℤ` its product, of norm `5ⁿ`, is never real (`prod_letter_not_real`); so the word map into the unit quaternions is injective (`wordMap_injective`), and through `v ↦ q v q̄ / N(q)`, whose kernel is the real quaternions (`rotation_eq_one_iff`), into SO(3), the letters turning about two axes by the angle of cosine `−3/5` (`rot_letter_zero`, `rot_letter_one`). | #410's box "Two coupled planes carry order"; the torsion record of October 22, §6 | `rotation.quaternion-free-pair` (new) |
| `Compression/FacesOnCycles` | The carry `⌊(a + b)/n⌋` on `ℤ/n` is the repository's `PhaseCarry.carry`, a 2-cocycle with `n·c = δ(a)`; on the lap `Σ_a c(a, 1) = 1` while every integer coboundary reads `n·b(1)`, so `k·c` is a coboundary exactly when `n ∣ k`: a class of order `n`, and over `ℚ` the coboundary of the phase `a/n`. The `th` count obeys `count(xy) = count x + count y + s(face x, face y)` over every word, `s` is a 2-cocycle on the face monoid and, by the certificate `[at|ha] + [aa|aa] − [at|at] − [ha|ha]`, not a rational coboundary. A table's four-cycles vanish exactly when its Künneth cross part does, exactly when it is `u(x) + v(y)`, and its interaction rank is the least number of rank-one terms. Along a positive replicator solution an antisymmetric payoff with zero column sums keeps `Σ log x_i`, and a symmetric one raises `xᵀSx` at twice the fitness variance, for any finite set of strategies. | #410's box "Faces read on cycles"; the record of October 24 on faces read on cycles, §§2, 3, 4, 7 and 9 | `face.carry-bockstein`, `lang.seam-class` (now `formal-checked`), `contact.kunneth-interaction-rank`, `norm.replicator-hodge-parts` (now `formal-checked`) |
| `Physics/Fluid/FrictionKeepsHarmonic` | On `Foundation/HodgeReceiver`'s complex the Hodge Laplacian keeps the exact and coexact parts in their spaces and kills the harmonic part, so the viscous step `u ↦ u − νΔu` and every iterate of it keep the harmonic part at any rate. The HPP collision conserves mass and both momenta, is an involution and changes 2 of the 16 site states; streaming on `ℤ/m × ℤ/m` keeps the totals, so a step conserves them. | the same box, its fluid clauses; the same record, §5 | `fluid.friction-keeps-harmonic` |

The boxes these answer, by their opening words: "Two coupled planes carry order" (whole: the freeness, the
interpretive clause on pump phases being its reading); "Faces read on cycles" (whole).

## 2. What the pass corrected

1. **The seam's coboundary has the carry's sign.** The record and `lang.seam-class` wrote `s = δ(count_th)` on words.
   In the carry's convention `δb(x, y) = b(x) + b(y) − b(xy)` the law is `s = δ(−count_th)`; the module proves
   `s = count(xy) − count x − count y`, and the row now says both. The class is the same up to sign.
2. **The replicator's identities hold for any finite set of strategies.** `norm.replicator-hodge-parts` was scoped to
   three strategies, where the record checked them at three rational points; the derivative identities need neither.
3. **Mathlib's anonymous constructor builds the wrong quaternions.** A bare `⟨a, b, c, d⟩` elaborates at
   `ℍ[R, −1, −1]`, the general quaternion algebra, where the `ℍ[R]` lemmas do not fire; `QuaternionFreePair` types
   its constructor (`mkQ`).

## 3. What each statement stands on

- **The free pair** is these two turns, through the reduction modulo five; which pairs of rational rotations are free,
  that `arccos(−3/5)` is an irrational multiple of `π`, and the ring chain's pump that realizes the turns stand beside
  it. Against it stands the one-plane collapse, `Geometry/ScrewTorsion.plane_reflections_compose` and
  `plane_turns_commute`: a word read in one plane keeps only its parity and a signed phase sum, a word read on two
  coupled planes keeps its order.
- **The faces on cycles** leave the bits census (`a + b = (a ⊕ b) + 2(a ∧ b)` on bytes, the ripple adder) and the face
  tables' ranks to the record's receipts; the certificate replaces the rank computation for the seam.
- **Friction** keeps the harmonic part at every rate; the strict fall of the exact and coexact energies needs a
  stability bound on `ν`, and the replicator's identities are read along a given solution, whose existence is not
  proved.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the three modules: `Build completed successfully (3128 jobs)`, exit 0, 10 s, no
declaration elaborated with `sorry`; projected under 10 minutes, deadline 20 minutes, peak resident set not read.
Single-file checks of each module at the package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib revision on a cloud host, read by exit status
(each `EXIT 0` with no output, 1 to 9 s), for the reason the first pass's record gives (`agent-inferred`). The research
library's aggregator imports the three modules.

Two workers on disjoint owner paths wrote the modules; the lead re-checked each file from the tree and read every
`L:` owner added to the atlas against its module's declarations by `tools/link_check.py atlas` (`broken=0`).
