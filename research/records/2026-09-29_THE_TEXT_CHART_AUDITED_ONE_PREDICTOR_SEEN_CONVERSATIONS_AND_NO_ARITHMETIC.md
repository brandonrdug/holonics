# The text chart, audited: one predictor, seen conversations, and no arithmetic

**Date.** September 29. **Issues.** #73, #148, #63. **Grade.** [measured; source-inspected] for
the findings, [agent-inferred] for the corrections.

**Occasion.** After F0's acceptance run failed, Brandon's questions were: what "the egg" and "the
flat tree" are ("there would be many eggs and also tubes of the tree"), what "truth" means ("if
you mean 'Truth' as in sample it's meant to repeat, that's just straight up contamination"), what
"bytes a cell" is, what is being compressed, what the text chart does with arithmetic, and which
elementary things are neglected. Two independent audits answered from source: a code trace of the
whole text path (every claim cited to a line) and GPT-6 Astra's review. They agree, and the trace
adds the measurements below. Both were read-only and printed counts and hashes only. Neither
opened the evaluation partition.

Brandon's earlier lenses, read from the repository's logs (`tools/human_messages.py`, counts and
his own paraphrased words only), fix what the chart should have been measured against:
- holonic compression never reconstructs past raw states ("un-boil the egg", September 2);
- arithmetic emerges from counting and calculus; it is not a skill to discover (August 13);
- `2 + 2 = 4` and `2^2 = 4` are different generators with one face, and the generator is causally
  relevant (September 11);
- a multiplication table is a map of how digit pairs occur relative to each other in a base
  (September 27), and bases 2, 10 and 16 matter (September 28);
- eggs are generators that pack into complete objects, and compression and generators are
  classified as eggs with families of code lengths (September 27);
- no codec (prose, arithmetic, Rust, Lean) is to be catered to (August 12).

## 1. What the text chart is, in plain words

- **The data.** The UTF-8 bytes of the visible messages in this repository's own development
  conversations, laid end to end. A **cell** is one byte, or one of twelve section letters that
  mark a conversation's opening, a switch between conversations, a new turn or a further part, per
  channel (human, agent, tool). The alphabet has 268 symbols (`curated_source.py`).
- **What is measured.** The prequential code length: each validation cell is coded from the model's
  face before that cell is deposited, and the bits are summed. It is a code length, not a
  compressed artifact. The model keeps learning during validation.
- **"Standing, bytes a cell."** The size of the model's saved state divided by the cells read. After
  F0's passage it is 2,141,915,637 bytes after 1,046,085 bytes of text: 2,047 bytes of state per
  byte read, about 20 tree nodes a cell; the flat control holds 1,296 bytes a cell. Size alone does not prove
  memorization (the tree's labels are context paths, and its counts drive predictions). It does
  show that the state grows with the data and is thousands of times the code length of what it read.
- **"The flat tree."** One context-tree-weighting predictor (binary KT counts at each node, a mixture
  over pruned context trees) at depth 48, over the bytes with every section letter removed. It
  never sees a message boundary.
- **"The egg" in F0.** One fixed predictor, `AdmittedEgg`, with these parts:
  - a channel-typed byte tree at depth 12;
  - a letter tree predicting which section letter comes;
  - a part clock and hazard predicting where a part ends, with a sentence counter as its carry;
  - a copy stage that follows the request when the reply quotes it;
  - a pointer to the request.

  In F0 and U2 no population exists while scoring: the egg is called directly, and the release uses
  a population of one. The only "many" is the tree's own mixture over pruned trees. That mixture is
  where the tubes of the tree live, and it is present on both sides of the comparison. F4 mixed
  eight families, and its posterior sat wholly on this one.
- **"Truth."** The logged reply. It is never a loss. It served as display, as the length the flat
  control's release was given, and as a reference column for the legibility counts. The name
  contradicts the owner's own rule (`receiver/population/admitted.rs`: "a response is observed
  conduct, not a gold target") and Brandon's lens. The name is retired (§4).

## 2. The findings, most severe first

1. **The acceptance comparison was lopsided.**
   - The egg paid for response stops, and every byte face carries its "no stop" factor.
   - But it was given, free:
     - the identity of all 981 section letters;
     - the human parts' closes;
     - the request pointer (`518 + 12/16` bits);
     - channel-typed contexts.
   - Under full accounting the egg codes the curated stream `+2122 + 14/16 + ε` bits worse than the
     flat tree.
   - Its byte gain, `−1981 + 0/16 + ε`, is under one bit in 264 a byte, and it lies within the
     `533 + 1/16 + ε` spread between splits. F0's failure verdict stands, more strongly.
2. **"Unseen families" were unseen messages in seen conversations.**
   - A development family is `(provider, record_group)`: one message. There are 22,449 families
     over 87 conversations.
   - The F0 choosing role holds all 87 conversations; the validation role holds 69, every one of
     them also in choosing.
   - Conversational future crosses roles: 103 choosing replies answer validation requests (8,856
     bytes), and 13 choosing human returns answer validation replies (39,292 bytes). Both are read
     before what they answer is scored.
   - Verbatim repeats are small: 6,452 of 502,034 validation agent bytes lie in 64-byte windows also
     in the choosing cut.
   - Both predictors see this material, so the comparison stays fair, but every absolute rate is
     optimistic. The "fresh" splits of F0, U2 and F2 reshuffle the same messages, and the egg's
     settings were chosen on data holding F0's validation messages in other roles.
3. **The "response stops" are mostly not the ends of responses.** Only 42 of the 936 are followed
   by a human part. Of the other 894:
   - 370 are record boundaries within one turn;
   - 368 are switches to another conversation;
   - 141 are new turns;
   - 15 are openings.
4. **The stream interleaves 87 conversations.** After a switch, the depth-12 context is another
   conversation's bytes, and no state is kept per conversation. The objects' own reading
   (conversations are aeons, turns are epochs) is declared in the section letters and not realized
   in the predictor.
5. **The text chart has no arithmetic.**
   - Digits are opaque bytes. `13122 = 2·3⁸` costs five byte cells, at best between 16 and 17 bits
     in a familiar context and near 8 bits a byte otherwise. Its size alone needs 14 bits, and its
     factored form is the exponents `(1, 8)`.
   - The larger loss is relational. A computed result is determined by its operands, and the carry
     egg codes it at 0 bits (`receiver/population/arithmetic.rs`), but the byte tree pays full price
     unless it has seen the exact string.
   - The arithmetic owners exist: `RecordClock`, `CarryEgg`, `Counter` and `Sieve`, composed as
     `clock ⊳ carry` and `clock ⊳ (counter ⊳ sieve)`. Their only callers are tests and the
     synthetic-terrain harnesses. The text chart never composes them.
6. **Generation is autoregressive sampling, not egg packing.**
   - A release is a run of certified inverse-CDF draws from the byte face, one cell at a time,
     until a section letter or the cap (`receiver/population/text_release.rs`).
   - `decode(T_native(encode x)) = T(x)` appears only as a check that the output decodes as UTF-8,
     with producer provenance `None`. 3 of 28 egg releases failed even that.
   - The recombined project vocabulary Brandon saw in the releases is what this class of predictor
     does.
7. **Leaks and borrowings that remain.**
   - Construction hands the scorer the whole relation schedule. No prediction reads a relation
     before its letter, but span retention looks ahead.
   - The general `branch_future` still clones future relations; only F0's `branch_at_present`
     withholds them.
   - The flat control's release borrowed the logged reply's length.
   - Before `branch_at_present`, a release could be refused at a future relation's letter. This
     leaked the logged reply's length in F0's dry run on F4's passage (6 of 8 refusals stopped
     exactly at it). F4's own record claims no validation release.

## 3. What stands

- The context-tree predictor is a legitimate control, and the exact arithmetic, clocks and release
  law the chart runs on are sound.
- Every measured number above is exact and reproducible from its record.
- F0 failed, F2 failed on work, and the byte population stays a compression result. That verdict
  is now stronger: the whole-stream accounting is against the egg.

## 4. The corrections

[agent-inferred; the order is Astra's ranking, joined to the trace's measurements. Each item's
acceptance is fixed here, before any run.]

1. **The data protocol.**
   - The split unit is the conversation, the aeon, not the message.
   - A reserve of development conversations is held that nothing has read. It is named by hash
     before any run, and every earlier split is marked as a reshuffle of read material.
   - The predictor keeps its state per conversation, so a switch does not splice two conversations'
     contexts.
   - Acceptance: no validation conversation, and no reply to or return from one, lies in any
     choosing role. Replacing any withheld continuation, with its length and future relations,
     leaves the request-time state, faces and keyed release unchanged.
2. **A symmetric comparison.**
   - Both sides receive the same available context and predict the same events: bytes, section
     letters and ends.
   - Every declared choice is charged to both.
   - "Stop" is split into its kinds: a response's end (followed by a human part), a record boundary,
     a turn, a switch.
   - Acceptance: the charged difference's upper bound lies below a margin fixed before the run.
3. **Arithmetic joined through one shared contract, not a patch for prose.**
   - Numbers in a stream are read by the existing counting, place-value, carry and factorization
     navigators (`receiver/population/arithmetic.rs`, `ratio`), composed at a port. The same
     contract serves text, code and Lean, so no codec is catered to.
   - Acceptance, on unseen operands:
     - in bases 2, 10 and 16, a computed result codes at the operands' cost with the consequence
       square closing exactly;
     - two producers of one face (`2 + 2`, `2^2`) stay distinguishable to a provenance receiver.
4. **Generation as a requested consequence.**
   - A release is a native composition carrying its decoder, keys and fibre.
   - Deterministic consequences, such as the result of an arithmetic request, agree exactly.
     Stochastic ones agree as faces.
   - Conversation uses F5's blind relevance and retrieval gate, never equality with a logged reply.
5. **Retention around the admitted actions.**
   - The context tree is kept as the control.
   - Exact merges preserve decoding and continuation under the admitted actions, and coarsening is
     reported apart.
   - The whole state, the peak memory and the complete warm response lie within fixed limits, with
     no diagnostic subtraction.

**Done in this commit:** "truth" is retired in the harnesses (`hnn_population_f0.rs`,
`release_legibility.py`) in favour of "the logged reply", observed conduct.

**Next (THE_REBUILD U6, restated):** item 1's protocol and item 3's arithmetic contract, each with its
acceptance above, as the chart's next loop. F0's release gate and F5 wait on them. Brandon reviews
this record before that loop is built.
