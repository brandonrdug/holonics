# The body grows by copies whose parts sum to what it learned, so it restarts wider on the same faces

Refs #404 #407. Status: [design fixed before the build; agent-inferred, October 29]; built and measured on the host and the card (§4).
Claude (opus). The step after [the continuing body](2026-10-29_THE_CONTINUING_BODY_RESTS_WITH_ITS_CURRENTS_AND_ONE_OPEN_SECTION_AND_AN_ANSWER_READS_ITS_PARTICIPATION.md):
the audit kept the growth semantics of Codex's continuing surface
([audit §3](2026-10-29_THE_CODEX_LEAD_OF_OCTOBER_27_AND_28_AUDITED_THE_THEORY_STAYS_THE_TEXT_SURFACES_ARE_WITHDRAWN_AND_PARTICIPATION_IS_NEXT.md#3-withdrawn-and-why))
as the port source for the card body. Owners it joins: the tower's material and layout
(`Tower`, `Layout`), the founding (`Tower::found_on`), participation
(`ParticipationDeclaration`, `LevelSites`), the learner's moments (`TowerLearner`), and the body
(`hnn::tower::body`).

## 1. The source read

[source-inspected] Codex's `Tower::widened` (branch `codex/counting-faces-20261028`, never pushed,
read from the PC) widens width, modes and contacts by a factor `f`. The encoding and every vector
family are repeated, so every coordinate has `f` equal copies; every matrix repeats its rows and
splits each entry over its `f` column copies into parts that sum to it; the readout splits its
columns and keeps its rows. Then every sum the forward forms is the old sum, and the grown tower
starts face for face. Its `widen_current` repeats each level's modes. What the port changes:
- **The differences come from the declared keys, at the founding's own scale.** Codex perturbed
  the parts by a seeded generator at a sixteenth of the family's largest entry. A generator inside
  the law and an unjustified sixteenth are both refused (`CLAUDE.md`, exact arithmetic: no magic
  number). [agent-inferred] The zero-sum difference of an entry is what the founding of the grown
  declaration would found there, drawn from the declared founding key stream four bytes a draw as
  `Tower::found_on` draws: the push and participation's charts at `1/√(fd)`, the reads at
  `1/√(fN)`, the contacts at `√(6/(fd))`; the families the founding opens at zero (returns, gates,
  readout, the pair drive, participation's contact) split evenly.
- **Participation is lifted.** It postdates the source. Each head is repeated, one head a copy,
  so a copy's modes are contiguous and every head of the grown tower reads the old head's sites.
  The sites' frames, met dissipation, keys and values are repeated with their modes and each
  site's dissipation with its heads.
- **The moments are lifted, not reset.** Codex founded new moments. [agent-inferred] Split evenly,
  every grown coordinate's covector at the growth point is the old one divided among the copies: a
  copy of a repeated coordinate receives `1/f` of its covector from the even parts it feeds,
  through the read's ratio to its power as well (`‖r‖_rms` is the same over the copies and
  `⟨r̂, ∂r̂⟩` is kept); only the readout's rows are not repeated, so its covector is the old one. The
  differences add a part of their own, which is how the copies come apart. The moments are the
  covector's statistics, so a grown coordinate carries the statistics of its divided part, `m/f`
  and `v/f²` (the readout `m` and `v`), and opens on the old normalized step `m/√v`. Founding them
  anew would open every coordinate at a full-rate step, the failure recorded where a founded
  family's moments opened at zero.

## 2. The law

```text
x' = (x, …, x)  (f copies)          W'[(b, r), (c, j)] = W[r, j]/f + δ_c[(b, r), j],  Σ_c δ_c = 0
U'[a, (c, j)] = U[a, j]/f + δ_c[a, j]          bias'(b, r) = bias(r)         heads' = heads × f
⇒  every sum the forward forms is the old sum:  face'_t = face_t,  widen(advance(σ, u)) = advance'(widen(σ), u)
```

`W[r, j]/f` is the Euclidean split, the remainder carried by the first parts so the parts sum
exactly. The rectifier, the pair contact's product, the gate's logistic, the move and the read's
ratio to its power act entry by entry on equal copies or on sums equal to the old ones, so the
equality is exact, not approximate. Zero-sum differences cancel in every forward sum while the
copies are equal, but the split parts' covectors differ by them as soon as the encoding's copies
move apart, so the copies specialize under learning; a family split evenly specializes through
the others.

Not lifted, and refused with the lift each needs: the pair face, the ring, the rotor, the strands,
the turned and pumped modes (their own charts), and the mutual contact, whose `⟨y, E_a⟩` and
`‖E_a‖²` would each count the copies.

**The body grows** (`TowerBody::grow(factor, keys)`): the learner widened and every current's state
widened, its pending classes, section and draw state kept. A body grows at rest, between two
operations.

## 3. Acceptance, fixed before the build

1. **Same faces.** On the host, a grown gated tower (rectifying and pair contacts, and
   participating) read from a widened state gives the old faces class by class over a passage, and
   its state after it is the widened old state.
2. **Exact parts.** The parts of every entry sum to it; the differences are the declared keys'
   draws at the family's founding scale; an evenly split family has no difference.
3. **The copies specialize.** After one learned section on the grown learner, some pair of mode
   copies differs.
4. **The moments.** The grown learner's moments are `m/f` and `v/f²`, the readout's `m` and `v`.
5. **The body.** A grown body's ask releases exactly what the old body's releases, its
   participation each head copy's the old head's; its text re-encodes and it resumes cold.
6. **Refusals.** Each unlifted part is refused.
7. **On the card.** The grown body hears, asks and answers on the 4080 as on the host (with the
   body's card test).

**Lessons checked.** No generator or magic number in the law (§1). No learned material reset: the
material and the moments carry. The growth is not catered: it adds capacity whose use the passage
decides. Every design is checked against every medium: the growth acts on classes and modes, never
on a codec.

## 4. Built, and what it measured

**Built** [source-inspected]: `hnn::tower::growth` (`Tower::widened`, `Tower::widen_state`,
`Tower::growth_draws`, `TowerLearner::widened`), `TowerBody::grow`, and the command
`grow-tower-body BODY BODY_SHA FACTOR KEYS KEYS_SHA OUT` on both routes (it moves no section; it
prints the key bytes a growth draws when the file holds too few).

**Measured on the host** (tiny towers, in the tests):
- Acceptance 1: by two and by three, on the rectifying, the pair-contact and the participating
  tower, the grown tower's face equals the old one at each of 40 classes and its state equals the
  widened old state after each, across participation's section closes. The equality is exact on
  the first build.
- Acceptance 2 and 6: every push entry's two parts sum to it and some differ by more than one; the
  readout's parts differ by at most one; the draws counted are exactly the draws read; one copy,
  too few keys, a turned mode, the mutual contact and a carried credit are refused.
- Acceptance 3 and 4: the grown learner's moments are `m/2`, `v/4` and the readout's `m`; one
  learned section on the grown learner deposits and parts a pair of mode copies.
- Acceptance 5: a grown participating body's ask releases the body's classes and reads the body's
  sites, each head copy's participation equal to the old head's; its text re-encodes and it hears
  on. Chained through the commands, the grown body's release file equals the body's.

**Acceptance 7 on the 4080.** On the RTX 4080 SUPER at `dfa6ff678` (B-PC, under the card lock,
alone on the card), `tower_pass` passed 36 of 36, among them
`the_cards_grown_body_continues_as_the_hosts` (a participating body heard, grown by two, heard,
asked and answered on the card as on the host, and resumed cold from its text): build 30.5 s, tests
11.8 s.
