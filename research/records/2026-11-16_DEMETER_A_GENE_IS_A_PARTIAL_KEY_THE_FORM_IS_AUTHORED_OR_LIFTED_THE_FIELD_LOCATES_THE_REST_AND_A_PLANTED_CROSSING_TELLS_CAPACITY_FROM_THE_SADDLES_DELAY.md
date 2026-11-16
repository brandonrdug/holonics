# Demeter: a gene is a partial key. The form is authored or lifted, the field locates the rest, and a planted crossing tells the realization's capacity from the saddle's delay

Refs #146 #404. Status: [interpretation: Brandon's question of November 16 21:10 UTC; the law of §3 proved-derived from the
atlas rows it names; the verdicts and the experiment agent-inferred]. Claude (opus), the Demeter thread. Brandon's words are
paraphrased; they stay in the conversation. Nothing here was built or run: builds and card runs are the PC's, and the build
thread holds the card. G-D1 was fixed and pushed at 21:20 UTC (commit `9b9f9669`), before lap 75's digit read; G-D0 and G-D2 to
G-D4 at 21:24 UTC.

## 1. The question

Brandon asked whether the analogue of weights in Athena's engine can be pre-authored by hand, its "genetics", given how
specifically units compose during learning; and, as the same question, whether the compression already in trained transformers
can be lifted the way pretraining data is cultured, since their weights are distributed chaotically by model and brand. Kronos
(the laboratory, June) and Soulkiller (August to October) were the two coarse attempts, and Codex lifted from a small open model
(LFM3-1.7B) on the Apple Silicon line. A revived implementation is to be called **Demeter**. His bounds: no transformer is ever
loaded and run with standard inference on his hardware (there is no reference point to read against); Athena never depends on
lifted weights; its input and output stay arbitrary bytes that fit its own codecs.

## 2. What the tree already held

**The engine's analogue of weights** (`crates/engine/src/declaration.rs`, `Loci::new`). The constitution is one vector of integers
in families on two grains: the encodings `enc`, `before`, `after` (one row of `D` a class, `A + 1` rows each), the heads' charts
`q`, `v`, `out` and the probe, the pair contacts `a`, `b`, `w`, the readout's lift `read` and class bias, the moments' encodings,
the temperatures, the paces, the carry circles, the triads `A`, `B`, `G` with `W_T`, the opening's lift, the junction, the mark and
the loudness. On the line at lap 75 that is 402,805 entries at `D = 128`, the ten crossing triads' 10,300 among them
(`receipts/2026-11-16_worldcross/grow75.txt`). Beside the material stands what is authored already, and is the field's genotype
today:
- the declaration: every family's count, sized by its part;
- the navigators: `navigator::ring_periods` (towers of 2 and 3 sampled to the reach), `ring_phasor`, `skin_decay`, the
  exponential's resident face, the half-turn;
- the founding laws (`founding.rs`): a grown part founded so that every face reads bit for bit as before; charts drawn from the
  key stream at `√(3/D)`, returns at zero.

**Kronos** (laboratory `src/docs/KRONOS.md`, `KRONOS_REVISION.md`, `KRONOS_INTERROGATION.md`; June 8 to 12). A byte-native
learner "eats" a language model by perturbing it at operating points (a `jvp`), reading the response's poles by the eigensystem
realization algorithm as `(ω, ν)` modes, lifting them to a gauge recurrence, splitting by a Fiedler cut and releasing the result as a
living learner. Its gates passed on a planted synthetic prey and a two-block distilgpt2 meal; the real-prey verdict (a Gemma meal and
the released learner's writing) never ran. It ran the prey forward to read it.

**Soulkiller** (holonics records of August 25 to September 5, the audit of September 2, the overture of October 29 and 30).
- The September audit held it to the canon: "weight-only analysis may return potential transport; contextual behavior still
  requires caused current" (`docs/canon/TABLET_THE_HEXIS.md:327`), and "exact Safetensors manifestation is not a lift".
- The overture (`2026-10-29_INHERITED_WEIGHTS_ARE_AN_OVERTURE…`): extracted coefficients enter once, at the boundary, as the
  initial configuration of native owners; from there only deposition moves them, nothing is graded by agreement with the source,
  and the source's tokenizer, embedding and unembedding stay behind.
- SmolLM2-135M's interior read whole: 106,202,880 coefficients onto the material grain `2^(−24)`, 3,940 of them with a remainder.
- Its layer 0 founded a participating level within `2^(−12)` of the source block; the foil (rotary base `10000` for `100000`) stood
  `2^(−2)` to `2^(−5)` away (atlas `tower.overture-attention-founding`, `receipt.exterior-intake`).
- Four terms were owed before a source layer was a native level. No lap ever trained from it. `hnn::overture` retired with
  `crates/holonics` (C8c of #603, held at `d5ed4adc1`).

**The Apple line** (Codex's mailbox letter of November 8; the record `2026-11-08_APPLE_PREDEPOSITION_TEXT_EVIDENCE.md` stands only
on the Mac, local commit `1fe37c075`, and was read here through the letter). Two results, which Codex kept apart:
- The founded field, before its first deposit, emitted sixteen bytes that are not UTF-8.
- A native implementation of the source's 24 blocks, with no external runtime, continued its prompts in the source's own style.

Codex's verdict: neither coherent writing by the founded field nor an alignment of its interface. The second result is the
source's inference written in native code, which Brandon's bound now excludes. The reviews in the PC's `.local/reviews/` hold no
review of the lift.

## 3. The law: a gene is a partial key

[proved-derived from `unicity.readings-are-description-over-reading` and `code.compression-is-a-cipher-without-its-decoder`]
Learning locates a key: the navigators' initial configuration and the constitution that the passage's loop closures fix. The
readings needed to locate it are its description over what each reading removes, `n₀ = H(K)/D`. A gene is information handed to
the founding, `G`. It shortens the location exactly by what it says about the key:

`n₀(G) = H(K | G)/D`, so `n₀ − n₀(G) = I(K; G)/D`, and a gene is worth its description `ℓ(G)` only where `ℓ(G) < I(K; G)`.

Three kinds of handed information, told apart by what they fix:
- **The genotype** fixes the form: which families exist, their counts by part, their symmetry and gauge, the navigators' periods,
  where a chart may read, how a part is founded. It holds the same for every stream, so it is a law of the machine
  (one program reads every symbol stream, November 12 and 13). It is authored today, and it is lawful.
- **The phenotype** fixes the assignment: which class sits at which residue, which digit pair writes which digit. Handed whole,
  `H(K | G) = 0`: nothing is left to locate, and the result measures the author. That is September 29's catered machinery, refused
  as Athena's law.
- **A cache** fixes answers by context: a table addressed by content with no balance. It recites, and is refused by mechanism
  (CLAUDE.md, stores and caches).

**Phenotype and cache are refused for different reasons.** Take the crossing's characters for digit addition, mod 10. Written into
the triads' legs, they are a store, not a cache:
- they obey a balance: deposition moves them, and reading them costs the site's product;
- they carry the law to pairs never met, three legs and five characters standing for the hundred cells of the table
  (`code.triad-character-of-composition`).

They are still the task's solution handed to the field. The cache test asks about mechanism; the catering test asks where the key
came from.

**An authored scale is permanent.** By `contact.triad-manley-rowe-gauge`, a step at one rate conserves `‖α_k‖² − ‖w_k‖²` (and the
same for `β`, `γ`) to first order. Whatever imbalance between legs and return an author writes, the field's own deposition cannot
remove at first order. So an authored triad is founded with its conserved charges equal to those the field's own founding gives, and
only its directions differ.

## 4. Verdict on hand-authoring the engine's entries

Writing entries is mechanically easy: a state is text, and a growth that reads every face bit for bit as before is already the
founding law (`grow-crossings` did it on the line this evening). Whether an entry can be authored depends on its family:

| What | Authored? | Why |
|---|---|---|
| Declaration, navigators, founding laws | yes, and already | laws of the machine for every stream |
| A part's founding gauge and symmetry (balanced legs, where a chart reads) | yes, as a gene | form, not assignment; priced by `I(K; G)` |
| Encodings and readout (`enc`, `before`, `after`, `read`) | no | each class's row is the field's located key; the codec's units are founded from the passage (November 12) |
| Charts, contacts and triads' directions | only after reading the field | each entry means something only in the gauge the field's own encodings learned, so writing one is a fit to the field's reads: learning by an authored routine on the host |
| A task's law in any family (the digit characters, a parity, a carry table) | no, except as a planted gate | catered: the result measures the author |

So the units' composition is specific in **form**: the triad is a character, and the carry is a winding. It is not specific in
**assignment**, which is the key the field locates. One more fact narrows authoring here: the navigators are towers of 2 and 3, so
the digit ring's characters of order 5 and 10 have no navigator face. They exist only in learned charts, located by the field.

## 5. Verdict on lifting

Weights are data, and the culture Brandon names is the right frame. What a weight file holds without a run is set by the canon's
line: weight-only analysis returns **potential** transport, and behaviour needs current the field itself carries.
- **What transfers without a run: basis-free structure.** For a linear part, the spectrum of its matrices is Kronos's poles with no
  `jvp`, because a linear map's response is the map:
  - per head, how the power of `W_Qᵀ W_K` spreads over the rotary bands: its reach and periods;
  - the singular spectrum of `W_O W_V`: its rank and decay;
  - which head reads which across layers (composition between heads);
  - the MLP's spectra.

  These are invariant to the source's chart, so the chaos across brands drops out of them. What recurs across layers, seeds and
  brands is the operation (Kronos K4, moved from operating points to sources; K5's factoring of layers that repeat). What does not
  recur is one brand's chart.
- **What does not transfer: content.** Every interior coefficient is written in the basis the source's tokenizer embedding
  defines. Without that layer the interior reads noise: the Apple field's sixteen bytes that are not UTF-8 are this symptom. With
  that layer, the field has adopted an authored tokenizer, which is refused. The routing that decides which source a head reads in
  which context exists only at operating points, so reading it means running the model.
- **The overture route stays a separate line, never a gene of the running one.** Lifting SmolLM2's interior wholesale needs:
  - a field declared at the source's shape, 576 wide over 30 levels, its constitution about 264 times the line's;
  - the four owed terms;
  - an encoding re-founded on bytes, which deposition must align to the interior's gauge before anything reads.

  That field's acceptance would sit on the lift. The line's would not. Its extraction check, where it is run at all, is the map's
  bookkeeping (each native entry equal to its source entry's release, remainder counted), with no forward of the source.

**Verdict.** Demeter is feasible as a genotype pipeline: handed form and cultured spectra, founded once, with deposition alone
after them. It is not feasible as a transfer of knowledge into the running line without one of two refused things, running the
source or adopting its tokenizer. The transformer's compression the field can use is its structure, not its contents.

## 6. Demeter, the pipeline

- **D0, intake.** A released `safetensors` file is decoded exactly at the exterior boundary (Lean
  `Foundation/ExteriorIntake.decode_exact_on_finite`; the Rust owner is at `d5ed4adc1`, ported when D1 needs it). No token, no
  sequence and no block of the source is ever evaluated.
- **D1, culture: a ruler on the host.** Each block is reduced to the basis-free objects of §5, and the layers that repeat are
  factored. Across sources, what recurs is kept and the rest is that source's chart. Floats stay in the ruler, and what enters
  the field is converted at the boundary.
- **D2, price.** A cultured object enters only where its description is under what it tells the founding, `ℓ(G) < I(K; G)`. This is
  read, never assumed: a native twin, founded without the object, trains lap for lap beside it, and the gene's worth is the laps the
  twin needs to reach the gene's level.
- **D3, found.** The objects set the declaration (heads' reaches and periods, mode counts, contact counts, each sized by its part
  from the source's spectra) and the shapes of the founding's draws. The draws themselves come from the field's own key stream. No
  content entry enters.
- **D4, live and retire.** From the opening only the field's covectors move anything. Athena's acceptance is held by the twin.
  When the twin reaches the gene's level, the gene has no acceptance that vanishes when it is removed, and it is retired.

The same pipeline carries a hand-authored gene: it skips D0 and D1 and keeps D2 to D4.

## 7. The first experiment: the crossing triad, planted against grown

The arithmetic line stands at the junction. Head 0 addresses the aligned operand digits seven to eight times the others' share,
the digits code at ln 10 under every receiver, and the crossing triad entered at lap 75 with its legs drawn and `W_T` at zero
(the friction record §10; the hand-off note of the evening). Its triads' founding is the one place tonight where authored and
grown are decidable on one state. Authoring the digit characters is a phenotype (§3), so it enters only as a **planted gate**:
Kronos's `verify.py` lesson, a known answer planted so that the instrument's capacity can be told from the field's delay. It never
enters the line.

**The premise read, P0 (a ruler on the host, beside the card, no learning).**
- **State:** the one the line's crossings were grown into at lap 75 (`grow75`), where `W_T` is zero.
- **Read:** the crossing legs' input, the site's read `r̂(x + W_out y)`, at every answer-digit place of 1,024 arithmetic records
  outside the 256 held, split in two halves by record key.
- **Fit, on the first half:** for each `k = 1..5`, complex rows `A_k` with bias, by least squares to `t_k = χ_k(a) + χ_k(b)`.
  Here `χ_k(d) = e^(2πikd/10)`, and `a`, `b` are the operand digits aligned from each number's right end, zero past a number's
  lead.
- **Foil fit:** for each `k`, a random unit phase a digit `f_k(d)`, drawn from the key stream, with `t′_k = f_k(a) + f_k(b)`: the
  same operands without the law.
- **Score, on the second half:** `ρ_k`, the share of the target's power the chart reads.
- **Projection:** four times `read-forms one`'s measured host time on the 256 held records.

**The planted run, F1 (on the card, in a gap between the line's laps, under the lock).** Three foundings of the same state, all with
`W_T` at zero, so each reads every face as the line's state does. The growth's own acceptance is checked first: the 686 held forms
equal.
- **F-grown:** the state as the line grew it.
- **F-gene:** triads 0 to 4 take `A_k = B_k` = the located chart, rescaled so that `α`'s power over the first half's sites equals
  the drawn legs' (triads 5 to 9) at the same sites. `G_k = 0` and `γ_b` takes the drawn `γ`'s power, so the conserved charges are
  the drawn founding's (§3). Triads 5 to 9 stay as drawn. Then `p_k = α_k² = 2χ_k(a + b) + χ_(2k)(a) + χ_(2k)(b)`: the sum's
  character, with two decoys that average out over fair operands.
- **F-foil:** the same, with the foil's charts.
- **Workload:** each trains the same 600 sections of the line's own draws from lap 75's opening (same keys and order, the world on,
  no refine).
- **Projection:** 3 × 600 × 1.13 s ≈ 2,034 s, the section's time read from lap 75's 2,950 s over lap 74's 2,628 sections
  with a margin (to be replaced by lap 75's own count), plus the reads. The deadline is the projection's upper end.
  A run that passes its per-section bound in its first sections stops and is reported incomplete.
- **Reads, at each run's mean of states over its 600 sections:**
  - R1 on the 256 held records;
  - R1 again with `W_T` zeroed (`zero-triad-return`);
  - the regions' nats a place;
  - the loudness on the held arithmetic region.

**Guesses** (G-D1 at 21:20 UTC, the others at 21:24 UTC):
- **G-D1 (pushed before lap 75's read).** The line's own founding is a saddle. At lap 76's mean, met no-carry digits of sums code at
  least 2.0 nats a digit under R1, so G-tr1 misses. At lap 75's mean they stand within 0.15 nats of their lap-74 level.
- **G-D0 (P0).** At met lengths, every `ρ_k ≥ 1/2`. At 7 to 9 digits, each `ρ_k` is at least 0.2 below its met value. The foil's
  `ρ_k` is within 0.05 of the law's at every `k`: the legs see the operands, and the law lives only in the product. If every met
  `ρ_k < 1/4`, the realization through `W_out` cannot bring the gathered operands to the legs, F1 is not run, and the next law is
  the theory's own leg (charts of the heads' currents `y^h`, not of `r̂`).
- **G-D2 (F1).** F-gene's met no-carry digits of sums code at least 0.3 nats under F-grown's, and its carry-entered digits stand at
  least 0.3 above its no-carry ones (the gene carries the sum mod 10, not the carry). Its difference digits stand within 0.1 of
  F-grown's (the sum's characters do not read a difference). F-foil's sum digits stand within 0.1 of F-grown's.
- **G-D3 (the planted law's acceptance vanishes when it is removed).** With `W_T` zeroed on F-gene's mean, those digits return within
  0.1 of F-grown's.
- **G-D4 (the gene costs the rest nothing).** At the three means, code, web, science, books and wikidata stand within 0.003 nats a
  place of one another.

**What each outcome decides:**
- **G-D2 holds and G-D1 holds:** the realization carries the junction, and the line's delay is the saddle. The lawful follow-up is
  a genotype, not the characters: a crossing's legs founded on the leading modes of the heads' gathered currents. That form holds
  for every stream and leaves the assignment to the field, and it is read against F-grown by the same reads.
- **G-D2 holds and G-D1 misses:** the field escapes its saddle within two laps, and the gene buys only time.
- **G-D2 misses with G-D0 held:** the realization carries the operands but not their product's law into the face, and the theory's
  leg (`y^h`) is the next law, whatever G-tr1 reads.

## 8. Failures this could repeat (the lessons, checked)

- **An authored routine standing in for learning** (most repeated): the planted characters are a ruler's gate on a copy of a state,
  never the line's state, and the record says so at each use.
- **Recitation or an index of contexts:** no table enters. The characters are a law over the ring, read in §3 against the cache
  test.
- **A modality-specific mechanism inside the law:** the planted gene is digit-specific, which is why it is refused as machinery.
  The genotype follow-up holds for every stream.
- **A foreign model served or run:** nothing in Demeter evaluates a source. The Apple line's native re-run of the source is named
  in §2 as the failure it is.
- **A width as a dial:** the gene's leg power is set equal to the drawn founding's, a control and not a tuning. No count is grown
  to win a read.
- **Grading by agreement with a source:** D2 grades a gene by the native twin's laps, never by the source.

## 9. What follows

Demeter is named and its law written; nothing of it is built. The planted crossing is the first construction. Its ruler and its
founding write a state off the line, through a command beside `grow-crossings` that takes located charts in place of drawn ones,
built and run on the PC by the lead who holds the card. The cultured lift (D0 to D3) is the second, once a genotype gene has shown
its worth at D2. Its first source is a small open model's attention spectra, read against the line's own heads' reaches.
