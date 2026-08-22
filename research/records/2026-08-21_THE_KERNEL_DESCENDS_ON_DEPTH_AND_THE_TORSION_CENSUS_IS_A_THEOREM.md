# The kernel descends on depth, and the torsion census is a theorem

**Date:** 2026-08-21
**Kind:** the compact-frame deed — Brandon's direction: *"let's proceed with the compact-frame
and BSD."*  Solo orchestrator work, two Lean files, no agents; every identity verified in
exact modular arithmetic on random curve points over two large prime fields before encoding.
**It schedules nothing.** [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
The Lean line does not couple to the engine, per Brandon's standing ruling.
**Truth grades:** `proved-derived` with `formal-checked` evidence for every theorem named —
all audited by `#print axioms` to `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`;
`measured` where stated with commands.

---

## 1. What was proved

**Both of `RankOne.lean`'s named-open propositions are discharged as theorems, and the
winding census closes unconditionally.**  On `y² = x³ − 25x`:

- **`theDistantPrimeWindingsNeverCloseHolds`** — no rational route closes at a prime winding
  of five or more: `WindingCensus.TheDistantPrimeWindingsNeverClose` holds.
- **`theTorsionIsTheKleinGroupHolds`** — `RankOne.TheTorsionIsTheKleinGroup`: the points of
  finite order are exactly the identity and the three half-turns.  The torsion census of the
  rank-one curve is closed, kernel-checked, end to end.
- **`thePointHasInfiniteOrderHolds`** — `RankOne.ThePointHasInfiniteOrder`: the point
  `(−4, 6)` has infinite order, since the chain provably leaves the now-complete torsion
  table.  Five **is** a congruent number with an infinite certified chain behind its
  triangle.

Two owners:

- **`ElementaryHolonics/Millennium/FrameDescent.lean`** — the ℚ-layer: the depth calculus
  (`Deep`/`Sharp` over `padicValRat 3`, with the law that a sharp summand carries the sum
  past any strictly deeper one); the entry classification (negative abscissa depth comes in
  exact levels `(−2k, −3k)`); **the integral forcing** (the Fermat cube `x³ − x` is deep, so
  a three-integral point has deep ordinate — *the frame at three is pure half-turns* — and
  its double sinks into the kernel); and the transport chart `t = x/y, s = 1/y`, where the
  curve reads `s = t³ − 25ts²`, the chord slope is carried by a unit denominator (one
  subtraction of chart equations), the tangent line's double root is pure algebra from the
  slope's definition, and the cubic a line cuts from the chart yields the sum formula
  `(1 − 25α²)(t₁ + t₂ + u) = 50αβ` whenever the third root is distinct from the others.
- **`ElementaryHolonics/Millennium/DistantWindings.lean`** — the point layer, on mathlib's
  actual group law: the odd order keeps every multiple affine off the half-turns; the
  integral forcing produces a multiple at an exact kernel level `K ≥ 1`; the walk along the
  cyclic subgroup accumulates `t(m•R) ≡ m·t(R)` one level deep, each addition either
  obeying the estimate or landing on a negation of an addend — a coincidence the group order
  converts into a doubling whose estimate contradicts the exact level; and the closing of
  the walk, `(p−1)•R = −R`, forces `p·t(R)` a level deeper than the entry classification's
  exact level.  **The refusal is a descent on depth — the same well-founded mechanism as
  `MinusFourth.lean`'s Fermat descent, now on the torsion axis, exactly as the winding-census
  record posed it.**

**State after the merge, measured 2026-08-21:** `Millennium/` is **61 files, 20,333 lines,
975 top-level `theorem` declarations** (`grep -h "^theorem " ElementaryHolonics/Millennium/*.lean | wc -l`;
three of the files and their theorems are Sol's, in the shared tree); the library builds at
**3,382 jobs**.  The committed root imports the two new files; Sol's in-flight files remain
his to commit.

## 2. What the four-object split predicted, and what the deed measured

Sol's audit disposition on [the compact-frame record](2026-08-21_THE_COMPACT_FRAME_IS_A_LAWFUL_COMPRESSION_AND_THE_HORIZON_LAW_PREDICTS_WHAT_CROSSES.md)
separated the transport, the fibre theorem, the count receiver, and the decoder, and the
enacted route confirms the split by **spending only one of the four**:

- **The fibre theorem is the whole load**: the kernel's torsion-freeness, proved as the depth
  descent.  It was enacted *without constructing the point-reduction transport* — the census
  needed the kernel's refusal, not the map.
- **The count receiver never entered.**  The classical argument bounds torsion by
  `#E(𝔽₃) = 4`; the enacted argument replaces the count with the integral forcing — every
  affine point of the frame at three is a half-turn (`y² ≡ x³ − x ≡ 3x ≡ 0`), so an odd
  winding's route is forced into the kernel, where the descent refuses it.  The frame's
  sharpest face turned out to be its *parity*, not its cardinality: at three, the whole frame
  lies in the square-class receiver's band.
- The transport homomorphism and the decoder remain unconstructed and unclaimed, exactly as
  Sol's owed table carries them.

The coincidence handling deserves its line: the chord's third intersection landing on an
addend cannot be dismissed by classical multiplicity talk inside the kernel, and the enacted
resolution converts each coincidence into an order fact (`p | 2m+1`, `p | m+2`, or
`3•Q = 0`) and a doubling estimate whose depth contradicts the entry level — the
degenerate cases are not patched, they are where the contradiction fires early.

## 3. What this closes, in the route's terms

The BSD-facing chain on this curve now reads, all kernel-checked: the realized population
computed through the group law (`RankOne`), the descent face separating it and reading every
double trivial (`Descent`, `FaithfulFace`), the census below the fifth winding by rational
receivers (`WindingCensus`), the distant primes refused by the kernel's depth descent (this
deed), hence torsion exactly Klein and the chain infinite.  Rank zero on `y² = x³ − x` and
torsion-plus-infinite-chain on `y² = x³ − 25x` are the two smallest BSD instances' realized
sides, closed by the same tool at both axes: **refusal of an infinite descent on well-founded
terrain — heights on the rank axis, depths on the torsion axis.**

## 4. What is owed, with falsifiers

**None scheduled; the roadmap alone schedules.**

| owed | falsifier |
|---|---|
| the depth calculus generalized off the one curve (the chart identities are specific to `a = −25`; the calculus and entry classification are not) | a curve in `y² = x³ − n²x` whose chart identities the same subtraction does not produce |
| the point-reduction transport and decoder, still open per the compact-frame record's owed table | as stated there |
| `RankOne.TheFaceIsAHomomorphismEverywhere` — the remaining named-open of the descent route | a pair of points whose sum's slots leave the square class of the product |
| the rank-zero curve's kernel converse (`TheKernelIsTheDoubledPopulation`), now approachable with the same machinery | a point `Q` with `2•Q` a nonzero half-turn |

## 5. Boundaries

One curve, one prime frame.  Nothing about general curves, general torsion, or ranks beyond
the certified infinite chain; the splitting `E(ℚ) ≅ T ⊕ ℤʳ` needs finite generation (the
Mordell–Weil theorem, no mathlib owner) and is not claimed; nothing about the
Birch–Swinnerton-Dyer conjecture, whose realized side these instances inform and whose
analytic side is untouched.  The classical shape of the argument is the standard kernel
filtration (Silverman VII.3.1's ancestor), re-derived here in an elementary transport-chart
form; the coincidence-to-order reduction is, to this session's knowledge, the file's own.
