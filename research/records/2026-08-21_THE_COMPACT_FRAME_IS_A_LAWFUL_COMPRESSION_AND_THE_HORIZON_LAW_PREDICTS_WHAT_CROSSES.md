# The compact frame is a lawful compression, and the horizon law predicts what crosses

**Date:** 2026-08-21
**Kind:** derivation deposit — the compression face of
[the winding-census record](2026-08-21_THE_TORSION_IS_A_CENSUS_OF_CLOSED_WINDINGS_AND_THE_COMPACT_FRAME_READS_IT_WHOLE.md),
deposited at Brandon's direction after he asked whether the compact frame is relevant to
compression, noting the question bears on standing work of Sol's. **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The Lean line does not couple to the engine, per Brandon's standing ruling.
**Truth status and evidence:** `proved-derived` with `formal-checked` evidence for the kernel-checked
census and lineage/compression theorems named here; `proved-standard` for the cited classical facts,
each marked, **none of which is proved in this tree**; `interpretation` for the horizon-law reading
of the Birch–Swinnerton-Dyer conjecture and for every correspondence, marked where it sits;
`project-postulate` where a ratified corpus law is applied.

## Audit disposition — the four objects must not be fused

`proved-derived` + `formal-checked` for the abstract split;
`interpretation` for its arithmetic instantiation until the point-reduction map is constructed.

Claude's central proposal is useful, but its first wording fused four mathematically distinct
objects. The corrected decomposition is:

1. the **transport** `red_p : E(ℚ) → E(𝔽_p)`, which must be a constructed group homomorphism;
2. the **fibre theorem**, stating which population lies in `ker red_p` and, separately, that the
   relevant torsion fibre is trivial;
3. the **count receiver** `#E(𝔽_p)`, which is a scalar face of the finite codomain and is neither
   the transport nor its fibre;
4. the **decoder**, an algorithm recovering a declared source representative from an element of
   the image, with its domain and cost. Injectivity proves uniqueness of an inverse on the image;
   it does not construct this algorithm.

The split is now represented abstractly by
`Foundation/Lineage.lean` and `Millennium/LineageCompression.lean`: a transport carries its
occurrence witness, its relational shadow forgets that witness, and a quotient is lawful over
successor histories only when it intertwines every admitted transport generator. The arithmetic
reduction map would be an instance of that contract, not its replacement.

---

## 1. The classification: which species of compression the compact frame is

The governing law is `canon/TABLET_THE_COMPRESSION.md`: a compression is a **codec pivot
carrying a declared decoder**, with three species distinguished only by remainder — rebase
(zero), condensation (certified), compression (the collapsed population, family-relative).
Reduction of the rational point population at a good prime classifies under it exactly:

- **Candidate compression on the whole population** (`interpretation`). Per frame, infinitely
  many rational points have finitely many reduction faces. Its collapsed population is the
  family of fibres of `red_p`, not merely one kernel unless the group translation identifying
  every fibre with the kernel is carried. The kernel has a classical filtration by formal-group
  neighbourhoods; it is not identical to that filtration. Until an exterior representation and
  decoder are constructed, this is a receiver quotient and not yet a compression in the full
  tablet sense.
- **Receiver-exact on the closed windings** (`proved-standard`, cited: Silverman,
  *Arithmetic of Elliptic Curves*, VII.3.1; not proved here). For an elliptic curve over `ℚ`
  with good reduction at an odd rational prime, the standard local theorem gives the needed
  torsion faithfulness; the weaker prime-to-`p` injection is the general good-reduction fact.
  These hypotheses must travel with the claim. Exactness is a separate fibre theorem, never a
  consequence of the finite point count.
- **A bounded census on this curve** (`conditional`). For `y²=x³−25x` at `p=3`, the count
  `#E(𝔽₃)=4`, the four already exhibited Klein points with distinct reductions, and torsion
  injectivity together close the torsion census. The number four alone only bounds a possible
  injected torsion subgroup; on another curve it need not identify its subgroup or its routes.

**The reference sentence:** *collapse, keep every fibre, prove exactness for the declared source
subpopulation and receiver family, and never ask a scalar face to carry the transport that
produced it.*

## 2. The horizon law predicts the classification

`project-postulate` for the law; `interpretation` for its application here, and the application is the
sharpest content of this record.

The horizon law: **across a frame boundary only a ratio or a winding survives; magnitudes do
not cross.** Reduction at a prime is literally a frame crossing, and the law predicts, before
any computation, exactly what the census found:

| carrier | species | crossing behaviour |
|---|---|---|
| torsion route and its order | **winding face** | crosses faithfully under the stated torsion-injectivity hypotheses |
| canonical height / rank | **magnitude face** | individual free points reduce, but no one finite frame determines height or rank |
| local trace from point count | **ratio face** | supplies `a_p=p+1-#E(𝔽_p)` and hence one Euler factor; it does not retain the labelled reduction map |

The free part is not invisible: each free point has a reduction face. What one finite frame cannot
do is recover its height, distinguish the infinite free population, or determine the rank.
**The Birch–Swinnerton-Dyer conjecture can then be read through the horizon law**
(`interpretation`): the Euler-factor family determines the analytic `L`-function, whose central
order and leading coefficient are conjecturally related to rank and the regulator. This does not
say that the ratios reconstruct individual points or individual heights, and nothing here claims
movement on the conjecture.

## 3. Tolerance, the distinguishing word, and the obstruction group as remainder

`project-postulate` for the tolerance law (an aperture condition, never a numerical threshold);
`interpretation` for the arithmetic instantiation; `proved-standard` where cited.

Two points collapsed in one frame are **within tolerance of that receiver**, and the
**distinguishing word is another prime**: two distinct rational points reduce differently at
all but finitely many primes (`proved-standard`, elementary), and for torsion any single good
odd prime separates the whole subpopulation. This is exactly the collapsed-pair-plus-shortest-
separating-word return of `receiver_exact_compression.rs` — the machine's highest-degree organ
already computes the *shape* of this reading; the arithmetic instance gives that shape a
number-theoretic material. The two-frame law — an invariant is only visible across two
frames — is the injectivity theorem's conduct form: torsion survives the admitted good odd frames
faithfully under the stated `ℚ` hypotheses; a free generator's shadow is frame-relative.

At the global grain the same reading types a different obstruction. **The Tate–Shafarevich
group is** (`proved-standard`, definition in its usual arithmetic setting)

```text
ker(H¹(ℚ,E) → ∏_v H¹(ℚ_v,E)),
```

the joint kernel of all local restriction receivers on torsor/cohomology classes. It is not a
population of rational points collapsed by reduction modulo primes. Its nonzero members are
locally trivial yet globally unrealized, so the existing gluing and joint-kernel owners are the
correct abstract carriers. Reading its conjectured finiteness as a finite global gluing remainder
is an `interpretation`; calling it the loss of the reduction codec would conflate two different
source populations and is rejected.

## 4. The decoder discipline

`project-postulate` for the decoder discipline; `proved-standard` for the group-theoretic
consequence. A frame count quoted without the reduction homomorphism and injectivity theorem is
not evidence about rational torsion. But those theorems are still not a decoder. They establish
that torsion maps into a finite group without collision. A decoder additionally owes an explicit
partial inverse on the image (or another declared reconstruction algorithm), its representation,
and its cost. The four-point argument may close the classification theorem while the codec claim
remains open.

## 5. Why this is the reference case for the active plan's compression laws

`interpretation`, stated without presuming any session's specific difficulty. The single-card
plan's falsifier matrix carries **tiling is not compression**, and the Phoenix grade requires
condensation to carry its remainder. The compact frame is a small reference candidate because the
necessary clauses can be separated sharply; it is not a completed codec instance while its point
transport and decoder remain open:

- the transport, fibre theorem, scalar receiver, and decoder are named separately;
- the receiver family is **declared** (the frames), never implicit;
- exactness is proved **per source subpopulation** (torsion under stated hypotheses), not inferred
  from a count;
- every collapsed fibre is retained, with the kernel filtration as structure on—not a synonym
  for—that fibre;
- one frame closes the specific torsion census only jointly with the exhibited subgroup and
  injectivity, while the BSD family remains a different, conjectural global/analytic question.

A condensation or codec pivot elsewhere in the body can be graded against these five clauses
directly.

## 6. What is owed, with falsifiers

**None scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| the point-reduction transport constructed on the actual elliptic-curve point type and proved to preserve the group law | a rational point for which the proposed reduction is undefined, chart-dependent, or fails addition |
| the torsion-kernel theorem instantiated with every local hypothesis explicit — **DISCHARGED 2026-08-21, same day**, for this curve at three: `DistantWindings.lean`'s depth descent proves the kernel refuses every closed winding, spending the fibre theorem alone of the four objects (transport and count receiver unconstructed and unneeded for the census); [the kernel-descent record](2026-08-21_THE_KERNEL_DESCENDS_ON_DEPTH_AND_THE_TORSION_CENSUS_IS_A_THEOREM.md) | a nonzero torsion route in the kernel under those hypotheses |
| the `𝔽₃` point count joined to the four already exhibited, distinctly reduced Klein points | a fifth finite point or a collision among those four reductions |
| a decoder, if this is promoted from receiver quotient to codec compression | an image point with no returned source representative, or an undeclared choice/search cost |
| the tolerance instantiation run through the machine's own organ: two collapsed points handed to `receiver_exact_compression` with frames as the receiver family, returning the separating prime as the distinguishing word | a collapsed pair whose separating prime the organ cannot exhibit |
| the Sha reading joined to `SelmerLanding.lean` through local restriction maps on torsor classes, not point reduction | a proposed carrier that replaces `H¹` classes with rational points |

## 7. Boundaries

Nothing here claims a proof of Birch–Swinnerton-Dyer or finiteness of Sha. The horizon-law reading
is an `interpretation`. The injectivity of reduction on torsion and almost-everywhere separation
of distinct rational points are `proved-standard` facts with no theorem owner in this tree or its
pinned mathlib checkout as measured in the winding-census record. `WindingCensus.lean` proves the
windings below five and a reduction to one named distant-prime obligation; it does not construct
the compact-frame transport. The compression tablet governs the codec word, so no decoder-free
construction is promoted to a completed compression.
