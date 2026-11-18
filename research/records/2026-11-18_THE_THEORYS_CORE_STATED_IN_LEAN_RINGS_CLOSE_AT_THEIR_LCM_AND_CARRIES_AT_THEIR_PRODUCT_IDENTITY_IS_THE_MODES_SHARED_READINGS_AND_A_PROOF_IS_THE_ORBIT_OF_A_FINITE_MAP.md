# The theory's core stated in Lean: rings close at their least common multiple and carries at their product, identity is the modes' shared relative readings, a code without its key is fair bits, and a proof is the orbit of a finite map

November 18, 22:00 UTC. A formalization pass over statements the guides, the atlas and the records of
November 10 to 16 carry in prose, with the boxes of #410 that they answer. Ten modules of
`lean/HolonicsResearch`, 411 declarations, each elaborated at the package's toolchain with no `sorry`,
no `axiom` and no `native_decide`. Nothing here touches the engine, a state or a run.

Refs #410, #147.

## 1. What is stated, by module

| Module | What it proves | Source | Atlas rows |
|---|---|---|---|
| `Geometry/RingClosure` | Rings ticked together return exactly at multiples of the least common multiple of their periods; the orbit holds `lcm` of the `Π n_i` joint states, all of them exactly when the periods are pairwise coprime; a carried cascade (mixed-radix digits) returns exactly at multiples of the product. For `[7, 11, 33]`: `231 = 3·7·11` against `2541 = 3·7·11²`, the chord `33 : 21 : 7`. | [the winding guide](../../docs/WINDING_CARRY_AND_PLACEMENT.md) §9, §10; the chord record §2.3 | `lock.rings-close-at-lcm` (new), `lock.coprime-torus-diagonal`, `encoding.frame-explosion`, `winding.odometer` |
| `Geometry/SolenoidChart` | The finite solenoidal chart `(s, w, z)` and its advance: the lift `w + s` advances by `a`, `z − w` is kept, restriction commutes with advance and addition, the face returns exactly at whole multiples of the modulus with the winding advanced; the inverse limit over unbounded moduli has no return period. | the winding guide §9 | `solenoid.finite-compatible-chart`, `solenoid.restriction-action-square`, `solenoid.no-return-period` (new) |
| `Foundation/SharedModes` | Two complex mode vectors share every relative reading `z_i conj(z_j)` exactly when they differ by one common unit phase; two positive spectra share every ratio exactly when they differ by one common scale; lines of term values sum to zero round a closed walk; a merge's fibres lie inside every conserved level; a row's worth is at most its state's surprise, with the far fair bit as witness; commuting kernels' cross relation; a larger receiver family has a smaller kernel and its quotient maps onto the smaller family's. | the junction record of November 13, §2 to §4; the chord record §2.7 | `holon.identity-shared-relative-modes` (new), `standing.merge-inside-conserved-level`, `landmark.pin-worth-surprise`, `landmark.carry-worth-state`, `receipt.two-kernel-cross-relation`, `compression.receiver-family-kernel-antitone` |
| `Compression/CipherCode` | Under a dyadic law every bit of the code stream is fair given its prefix, across codeword boundaries, and fair at every node is equivalent to dyadic; a group key carries each message to each reading once, and no smaller key set does; the founding criterion `N·P² < (S/(S − drop))^N` is the unicity inequality in logarithms, with the three rulers `42`, `212`, `1522` as least counts; a gene's worth `I/D`. | the cipher record of November 16, §1 to §3; the Demeter record | `code.compression-is-a-cipher-without-its-decoder`, `unicity.readings-are-description-over-reading`, `unicity.gene-partial-key`, `key.pad-one-key-each-reading` (new) |
| `Compression/FaithfulModes` | A mode `k` of `ℤ/n` reads its argument modulo `n/gcd(k, n)`; the faithful modes are the units, `φ(n)` of them (96 of `ℤ/97`, 32 of `ℤ/96`); the frame potential is `tr S²` and bounds the participation; a loop's face depends on fractional parts alone; a chosen pair of 5-cycles has a 5-cycle for commutator, which is an AND of their presence, and a commutative family has none. | the cipher record §4 to §6 | `prime.faithful-modes-and-towers`, `frame.moment-map-loudness-colour`, `helical.loop-geometric-phase-remainder`, `key.commutator-is-and` (new) |
| `Foundation/FiniteKey` | The diagonal: a map reaching every assignment forces every self-map of the values to have a fixed point, and the half-turn on two faces has none; the recursor is the orbit of one finite map, and a descent reaches its ground in at most `μ(x)` steps; one reading refutes a statement over an unending family and no finite set of readings completes it; a form scaled by `q` places every non-isotropic mode at `‖α‖² = q`; two half sweeps meet in the middle. | the record of November 15 on proofs; the navigation record of November 10 | `key.diagonal-half-turn`, `key.forall-orbit-of-finite-map`, `key.derivation-finite-word-every-reader`, `key.scaled-form-places-modes`, `key.meet-in-middle-half` |
| `Foundation/HankelKey` | A solution of a recurrence of order `r` has zero Hankel determinants above order `r` at every shift; the census `N_n = qⁿ + 1 − αⁿ − βⁿ` satisfies the recurrence of `(X − 1)(X − q)(X² − aX + q)`; `a² < 4q` places both roots at `‖α‖² = q`; the ruler `q = 3, a = −2`: ten counts, determinants `2·3, −2²·3², −2⁵·3⁴·11, −2⁹·3⁸, 0`, and no recurrence of order under four. | the record of November 15 on proofs, §4 | `key.finite-hankel-rank`, `key.scaled-form-places-modes` |
| `Physics/TwoWayField` | A pair's two-way flow: `β = J/S` inside the unit interval, `(1 + β)/(1 − β) = F/G`, `β = tanh` of the odd log part, the current divergence-free at rest; grouped rates `W_a P_ab = W_b P_ba`; a transport composes round every triangle exactly when it is a coboundary, and one slipped contact opens exactly the triangles through it; a friction's reach `(1 + d)/d`, resting power `(1 + d)²/(d(2 + d))` and screened chain with `μ² = d²/(1 + d)`; the determinant of a Hermitian form is kept by the moves of determinant one. | the Einstein record of November 11, §4, §5, §11, §14 | `gr.two-way-flow-parts`, `aeon.count-ratio-arrow`, `contact.friction-range-mass`, `store.finite-quality`, `lorentz.pair-hermitian-signature`, `holonomy.composes-iff-coboundary` (new) |
| `Physics/ContextCycle` | Four contexts on a cycle: one table reads `\|S\| ≤ 2`; the path of three contexts glues to a table that returns all three; for two-valued readings the glued table reads the closing context at the product of the path's readings (`48/125` against the faces' `−3/5`); unit-vector faces read `S² ≤ 8`, reached; no table returns the faces' four readings. | the Einstein record §6.3 | `quantum.context-cycle-defect` |
| `Mathematics/Chord` | The temperament `⟨12, 19, 28\|` has kernel generated by `81:80` and `128:125` and is onto; a nonzero point of the lattice is never the unison; the tempered fifth stands under the just fifth by between `1/700` and `1/600` of an octave (`2¹⁹ < 3¹²`) and the tempered third over the just third by between `1/100` and `1/80` (`5³ < 2⁷`); a chord inverted through its closing length has shared fundamental one and closes at `lcm/gcd`; `4:5:6` inverts to `15:12:10`. | the chord record §2.1, §2.2, §2.5 | `ratio.temperament-kernel-commas` (new), `ratio.inversion-fundamental-overtone` (new) |

The boxes of #410 these answer: the two-way flow's parts; the grouped rates; a transport that composes round
every triangle; a friction's reach and its screened chain; a leaking circle's resting power; `det` on the
Hermitian forms of a pair; four contexts on a cycle; a merge's fibres and a row's worth; and the chord
record's kernel, residuals and reflection.

## 2. What the pass corrected

- **The founding count is least over `N ≥ 1`.** The criterion `(S/(S − drop))^N > N|P|²` reads `1 > 0` at
  `N = 0`, so "the least such `N`" was `0` as written. The rulers `42`, `212` and `1522` are least over
  `N ≥ 1` (`founding_ruler_42`, `_212`, `_1522`), and the row `unicity.readings-are-description-over-reading`
  now says so.
- **The product is the closing length exactly when the periods are pairwise coprime.** The winding guide
  said the product "is valid under" pairwise coprimality, one direction. For positive periods it is an
  equivalence (`closing_eq_prod_iff`), and so is the agreement of the residue word with the digit word
  (`same_reading_iff`). The guide's §9 now states it with its owners.
- **The solenoid's joined operator is proved.** The guide and the row `solenoid.restriction-action-square`
  carried the Lean proof as a debt to a closed issue; `restrict_advance` and `restrict_add` hold it.
- **A commutator of two 5-cycles is a 5-cycle for a chosen pair.** The cipher record's §5 states it of two
  5-cycles of `A₅` without the choice; a 5-cycle against itself commutes (`commutator_self`). The row
  `key.commutator-is-and` carries the pair `(0 1 2 3 4)`, `(0 1 3 4 2)` and its commutator `(0 4 1 3 2)`.
- **A scaled form places a mode that is not isotropic for it.** `scaled_form_places_mode` needs `v*Gv ≠ 0`
  and no positivity of `G` or `q`: the row's `G ≻ 0` is one way to have it.

## 3. What each statement stands on, and the constructions beside it

Each module's header states its limits. The ones a later module would build on:

- The rings' cascade is the plain mixed-radix odometer. The engine's Lock and Own rings are a tick law of
  their own, and the same two readings (the residues, the digits) are the statement to make of them.
- The solenoid is joined to its finite charts through the phase over the rationals. The map from compatible
  charts into the inverse limit is the construction that completes the join.
- The Hankel direction proved is from a key to its census. Kronecker's converse (finite rank gives the
  recurrence) is a construction on the kernel vector of the first vanishing determinant.
- The fair bits are proved for independent symbols under a dyadic law. A Markov source's bias, decaying with
  its mixing time, is a bound on the same stream mass along the chain's own tree.
- The path of three contexts is the first case of gluing along a tree; the general case is an induction on a
  leaf of the complex of contexts, with the same table at each step.

## 4. Receipt

Gate 4, `bash tools/lean_check.sh` on the ten modules by name: `Build completed successfully (8716 jobs)`,
exit 0, no declaration elaborated with `sorry`. Projected under 5 minutes from the single-file checks (5 to
13 s a module), deadline 40 minutes, measured 34 s of wall time on four cores; peak resident set not read.
The library's aggregator imports the ten modules; the whole research library was not rebuilt.

The check ran on a cloud host at the package's pinned toolchain (`leanprover/lean4:v4.33.0`) and Mathlib
revision, with Mathlib's build fetched from its cache. The guide places builds and gates on the PC because
the card, the CUDA toolchain, the Lean cache and the private passages are there; a Lean type-check of modules
that import Mathlib and one module of the foundation library reads none of those and gives the same verdict
on any machine at the pinned toolchain, so that reason does not reach it (`agent-inferred`), and the PC's
card was left to the line that trains.

Three workers on disjoint owner paths wrote six of the modules (the rings and the solenoid; the cipher and
the faithful modes; the finite keys and the Hankel rank); each was re-checked by the lead before the gate.
