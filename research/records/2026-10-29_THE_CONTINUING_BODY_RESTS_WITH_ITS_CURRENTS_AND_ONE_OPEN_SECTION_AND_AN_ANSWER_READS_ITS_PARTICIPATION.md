# The continuing body rests with its currents and one open section, and an answer reads its participation

Refs #404 #407 #405. Status: [design fixed before the build; agent-inferred, October 29]; built and measured on the host; the card's acceptance and the product run owed (§6).
Claude (opus), the third item of the order fixed in the
[October 29 audit](2026-10-29_THE_CODEX_LEAD_OF_OCTOBER_27_AND_28_AUDITED_THE_THEORY_STAYS_THE_TEXT_SURFACES_ARE_WITHDRAWN_AND_PARTICIPATION_IS_NEXT.md#4-the-order-now).
Owners it joins: the tower's learner and its section (`TowerLearner::section_realized`,
`TowerLearner::to_text`), the stream state (`TowerState`), the realized advance
(`Tower::advance_realized`), participation (`Tower::participation_at`,
[record](2026-10-28_ATTENTION_IS_THE_FIELDS_PARTICIPATION_THROUGH_ITS_OWN_TRANSPORT_SO_THE_PASSAGE_IS_TERRAIN_AND_THE_MODES_ARE_ITS_GEOMETRY.md)),
the pass realizations (`HostPass`, `holonics_cuda::hnn::TowerCard`), the declared key stream
(`receiver::release::KeyStream`) and the agreement release (atlas `receiver.agreement-release`),
and the observed stream's transaction law (atlas `hnn.observed-stream-transaction`: accepted =
published + pending, the pending interval bounded).

## 1. What is asked

Paraphrased; Brandon's words stay in the conversations.
- **The audit's order (October 29), item 3.** The save, resume and growth semantics of Codex's
  continuing surface were right: the checkpoint holds the material, the current, the pending class,
  the clocks and the draw state and no transcript. They are re-homed on the card learner with
  participation: a cold restart that resumes bit for bit, online learning on the card, and an
  answer whose provenance is its participation, the sites it read at its opening.
- **The Alpha plan, §3.** Hear online, rest and start cold with the next query bit-identical to a
  sibling that never stopped, ask from the retained state, and hear an answer as the target of the
  last ask, so the body keeps learning in conversation.
- **GPU first (October 27).** Learning runs on the 4080.

## 2. The learner now, read against it

[source-inspected]
- `TowerLearner::to_text` holds the material and the moments. A training run opens every stream
  from rest at each pass and drops the streams' states at the pass's end, so no current is
  retained.
- `release_realized` forks the rested tower for every prompt: an answer reads the material alone,
  never a current, and `participation_read` re-reads each prompt on the host from rest.
- The card reads a participating section to its close and no further, and refuses a reverse over
  a section carried open across calls (`TowerCard::reverse`). A learning section on the card
  therefore opens at a participation close.
- `TowerState` has no text.

## 3. The body

[definition; agent-inferred] The body is

```text
B = (L, (c_s)_(s<S), c_∘, k)        c = (σ, π),  π = ((u_0, q_0), …, (u_m, q_m)),  1 ≤ |π| ≤ T
```

- `L` is the learner: the material Θ, its moments and its rate.
- A current `c` is its state σ, carried to its last section's close, and its pending classes π,
  each with whether it is compared (`q`). `u_0` is the pending class: heard as a target and not
  yet read. `T` is the section (participation's section on a participating tower).
- `c_s` are the hearing currents, `c_∘` the conversation's current.
- `k` is the draw state: the keys drawn so far from the declared key stream.
- The clocks ride in σ: the news phase, and participation's open section, which is empty at a
  close.

**The section law.** Whenever `|π| ≥ T + 1`, the current reads `u_0 … u_(T−1)`, and the face after
`u_i` is compared with `u_(i+1)` wherever `q_(i+1)`. σ moves to the close, where participation
releases its sites, and `π ← π[T..]`. A section with a compared place is a learning section
(`section_realized`: the certified deposit and the moments). A section with none is read
(`advance_realized`) and the moments do not move. [agent-inferred: `section_realized` moves every
moment toward a zero covector on a section with no comparison, so a question heard alone would age
the statistics without news.]

**Retention.** π is the open section's present terrain, at most `T` classes, released at its close
as participation's sites are. Nothing else of a passage is held, and an answer's release belongs
to its fork and is released with it. The body retains Θ, the moments and the currents (the
quotient) and one open interval: the observed stream's law accepted = published + pending, on the
tower.

**The operations.**
- `found(L, S, T)`: every current at rest with `π = (END)`. A passage is entered after an end
  letter, as a release's prompt is.
- `hear(passage)`: the passage cut into `S` contiguous parts `p_s = passage[⌊sn/S⌋, ⌊(s+1)n/S⌋)`,
  each appended compared to `π_s`. Sections close together over the currents that hold one, each
  close one `section_realized` over those currents.
- `ask(prompt, keys, count, agree)`: the prompt and END appended uncompared to `π_∘`, and sections
  close. A fork of `c_∘` reads `π_∘` to the answer's opening, where the opening's participation is
  read (§4). The fork releases at most `count` classes, drawn from keys `k, k+1, …` by the
  agreement release, reading each drawn class back. `k` advances by the keys drawn. `L` does not
  change.
- `answer(answer)`: the answer and END appended compared to `π_∘`, and sections close. The answer
  is the target of the last ask: source END target END, the target-place law of
  `train-target-tower-classes`.
- `rest`: `text(B)` is `text(L)`, the body's line `(S, T, k)`, then each current's state and its
  pending line. `from_text(text(B))` re-encodes equal.

[agent-inferred] The conversation is one current beside the hearing currents, so an ask never
answers from a current that holds another passage's part mid-section. The hearing currents read in
parallel, as the race's streams read their parts.

## 4. Provenance is participation

At the answer's opening (the END after the prompt), each level's heads read the open section's
admitted sites (`Tower::participation_at`). Each site is named by its distance back from the
opening and the classes that end there. The sites are the conversation's own: the exchange before
the prompt within the open section, and the prompt. What lies before the section's opening is
carried by the modes and has no site. Provenance is participation, never an index of heard text: the
recitation reading of the Alpha plan's §3 (the longest spans shared with the corpus, by
`path:span`) is a store of the corpus and is not built. The reading runs on the host from the
carried state, which is the card's to the bit by the realization contract, beside the release; it
decides nothing.

## 5. Acceptance, fixed before the build

1. **Rest is gauge.** On the host, the body's text re-encodes equal, and a body read back from its
   text between two hearings, which then hears, asks and answers, equals the never-stopped sibling
   in its whole text and its release.
2. **Online on the card.** The card's body (`TowerCard`) equals the host's after found, hear, ask
   and answer, in its text and its release, at a participating declaration. A card body restarted
   cold from its text with a new card realization equals the never-stopped host body. Run on the
   4080.
3. **One open section.** After every operation every current holds `1 ≤ |π| ≤ T`.
4. **An ask moves no material; an answer is compared at its target.** `L`'s text is unchanged by
   an ask, and an answer's sections compare the answer's places and its end letter alone.
5. **Provenance.** Every ask on a participating body returns the opening's participation; none
   without participation.
6. **The product.** On the 4080, a body founded from the participating race's last learner with
   the race's streams hears a passage the race did not read, rests, starts cold, and answers the
   race's release prompts and an unseen design question. Each answer is shown whole with its
   provenance, beside the cold restart's equality.

**Lessons, checked before the build** ([the failures that repeated](2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)).
- Retention as a tape or journal: refused. π holds at most one open section and the release is not
  kept.
- Recitation or an index counted as generation: provenance is participation, not a corpus index.
- An uncertified deposition step: every deposit is `section_realized`'s certificate.
- Learning on the host: hearing and answering deposit through the card's realization; the host's is
  the reference in the tests alone.
- Text on its codec's grain as the exception: the body reads classes. The codec (octets as
  classes, END the alphabet's last) is the exterior's.
- Bits read as progress: the product is the restart's equality and the answers with their
  provenance.

## 6. Built, and what it measured

**Built** [source-inspected]:
- `hnn::tower::body`: `TowerBody` (`found`, `hear`, `ask`, `answer`, `to_text`, `from_text`), its
  `Current`, `Hearing` and `Answer`, the section law (`close`), and the state's text
  (`TowerState::to_text`, `Tower::state_from_text`, eight lines, each part refused at the wrong
  extent).
- The agreement release moved into the library (`receiver::release::agreement_face`,
  `agreeing_class`), where the body draws; the class release's commands import it.
- The commands `found-tower-body`, `hear-tower-body`, `ask-tower-body` and `answer-tower-body`
  (`complete_language/tower_body.rs`), on the host route and on the card route
  (`tower_pass train complete-language …`). Each writes the body create-new, reads it back and
  re-encodes it before reporting; an ask writes its releases and the participation at each
  opening (the class release's `PARTICIPATION.tsv` format, now one function both share).
- [agent-inferred] The rest is the text, not the struct: the learner's swell is the last section's
  receipt reading and its text has never carried it, so a body read back from its text equals the
  live one in every operation, release and later text, and differs only in that reading.

**Measured on the host** (the reference; tiny towers in the tests only):
- Acceptance 1 and 3: a body rested between two hearings, which then hears, asks and answers, is
  the never-stopped sibling in its whole text and both releases; every current holds
  `1 ≤ |π| ≤ T` after every operation.
- Acceptance 4 and 5: an ask leaves the learner's text unchanged and learns no section; it returns
  each level's heads over the open section's sites, one weight a site, the opening's end letter
  last; an answer's learned cells are exactly the answer's places and its end letter; a body
  without participation returns none.
- The commands chain through files: found, hear, two asks and an answer, each body read back by its
  SHA-256.
- Gate 1 passed on the change (all 22 entries).

**Owed on the 4080**: acceptance 2 (`the_cards_body_hears_asks_and_answers_as_the_hosts_and_resumes_cold`
in `holonics-cuda/tests/tower_pass.rs`, alone on an idle card) and acceptance 6, the product run.
