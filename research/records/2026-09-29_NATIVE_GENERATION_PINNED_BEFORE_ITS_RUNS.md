# Native generation, pinned before its runs

**Date.** September 29. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [definition;
agent-inferred] for the pins, [measured] for the development table (§3), read on development seeds
and on the choosing role only.

**Occasion.** Brandon, September 29, on the U6 releases: "Why is there a context length? That's
contamination … we have so much research on diffusion models and Holons as particles and encoding
on tori/helices … we do not work with frozen models, they do not have context windows." The laws
say the same (`docs/HNN_FORMULA.md`, "Generation as field refinement and boundary radiation"): the
source enters as phase-carried moments, generation develops a joint field through the model's
constituted dynamics, its refinement clock is not a token index, and a generation is never
independent per-coordinate predictions. The
[text-chart record](2026-09-29_THE_TEXT_CHART_IS_THE_ONE_MACHINES_FIELD_TORI_HELICES_EGGS_AND_TUBES_ARE_ONE_FAMILY.md)
names `hnn::prediction` as the loop that builds it.

## 1. What is built (commit `64eac0eb`)

- `hnn::word`: a continuing word (`Word::continuing`) opens on the change the previous word of the
  same refinement left, the pump reading the refinement's clock; its return
  (`Word::pull_back_continuing`) reads an end covector and per-step anchor covectors and returns the
  covector on its opening change. THE_MACHINE guard 16 is amended: the change lives only inside its
  word or its refinement.
- `hnn::prediction`: the latent section `x(0) = I_h(ξ)` (the latent on the receiving ring, the
  request's moment `P_g^(τ_g) m̃_g` on the source ring), `K` words of `w` full ticks with the moment
  re-entering every word, the joint readout `y_j = ρ_R(P_R^(1+j) v_R)` of every station from the one
  anchor at the last junction (station `j` the receiving ring's clock unwound from the request's last
  tick, its target phase `(1 + j)/d_R` turns), the release at tolerance zero through
  `receiver::release` (held when a station's top grain cell is plural), a keyed member of the latent
  family as the selection within the joint family, and learning by the section's covector pulled back
  through the `K` words and deposited by the normal law in the refinement's diamond.
- Lean `HNN/Prediction`: `refine_iterate`, `jointSection`, `joint_not_marginals`,
  `release_width_zero`, `plural_section_held`, `consumer_eq`.

The computational object is the helical pair interaction: the section is a span of the receiving
ring's helix (the response clock's winding), the refinement is the tube, the joint readout is faces
and placement, and the contacts' transit carries the pair. The cell holonomy and the tower thread
stay attached through the field's complex and its carry chain.

## 2. The pins

**The field** (`hnn_prediction.rs`, `declare`). Three rings of period `d = 32` in a chain
`0 — 1 — 2`, joined node to node on every node at exponent 0 (`G_a = Y_a = 2`), `Y_g = 2`, `h = 1`,
placements at the quarter turns. Ring 0 is the source and the receiving ring, its lock every port (it
steps once a cell, so the port chart does not enter); rings 1 and 2 step only by carries. No pair
offset. The receiver's tolerance `1/16` (`L_R = 16`), aperture `K·w + 1`, depth 1 (the tree it
declares is never read). Population `2^16`, above every `n*`.

**The constitution** is `Constitution::initial` at campaign 1's steps, `γ_U = 1`, `η_x = ½`:
`R = 0` and `E` the declared sign sequence. Nothing is authored for a terrain (the governing law
"No catered machinery"): the echo and the continuation must be located by the field's encoding,
refinement and deposition.

**The refinement.** `K = 2` words of `w = 1` tick; `m = 8` stations on the terrains and `m = 32` on
text; the termination class is the chart's last. Requests are ingested from rest, each into its own
moment. A deposit takes a batch of 16 refinements at one commit.

**Acceptance 1, the internal checks, on every refinement.** Every refinement's balance closes
(every tick, chained within and across the words, the injection the only jump, the executed residual
within its bound); its return's pairing is exact on the executed charts with no transient split;
across its deposit's commit the balance closes with the deposition work; every locus outside the
refinement's diamond is unchanged, material and deposit clock, by the deposit; and each release's
width over the section's grain fibre is read. **Passes** when every count equals the refinements
(or the deposits, for the unreached check).

**Acceptance 2, known truth.**
- *Copy*: requests of `n = 8` symbols drawn uniformly from 4 (the chart `|A| = 5`, its fifth class
  the termination), below the moment's capacity (`n* = 135`); the truth is the request itself.
  Training reads 1,536 requests from `Draw::new(2_026_092_901)`; evaluation reads 256 fresh requests
  from `Draw::new(2_026_092_902)`, each refined at rest and released.
- *Moiré*: one moiré of two gratings drawn from the family of denominator 3, class the sheet tuple
  (4 classes), from `Draw::new(2_026_092_903)`; a request is its window of `n = 8` cells at an offset
  and the truth the next 8 cells. Training reads 512 windows at offsets drawn from
  `Draw::new(2_026_092_901)`; evaluation reads every distinct window, one per offset below the least
  period. These windows are finitely many, so the moiré's evaluation is not unseen: it reads whether
  the field locates the continuation of one navigator.
- **Passes** when every evaluated section is released at width zero and equals its truth exactly.
  Anything less is reported as its count and fails the item.

**Acceptance 3, text.** The passage `curated-u6-passage-cut.bin` (U6 item 2's; the reserve
excluded). Training reads the choosing role's request relations whose response opens an agent part,
both parts nonempty, in letter order, up to 1,024 of them (the passage holds 385), two passes, the
request the human part's bytes and the target the response's first 32 bytes with the termination
where it ends. Generation answers the 8 validation requests F0's rule selects (`RELEASE_SEED =
20_260_929`, the rule U6 item 2 released with): each refined at rest; if its section is plural, the
keyed members 1–8 in order, the first released one emitted with its key; otherwise a typed refusal.
The bytes up to the first termination are the generated section. They are written whole to an
owner-only file and shown in the conversation only, with nothing beside them: no control, no logged
reply, no reference. **Illegibility is a failed output**, whatever the code measures.

**Time and memory.** Every run's training stops at 540,000 ms (reported incomplete if it does), and
its resident set is capped at 20,000,000,000 bytes. The projections, from the probes and the
development reads (§3): copy about 456,000 ms (1,536 refinements at about 282 ms each with their
deposit share, and 256 generations at about 90 ms), moiré about 142,000 ms, text about 386,000 ms
(770 refinements at about 490 ms, 8 generations of at most 9 members at about 130 ms); peak resident
sets below 1,000,000,000 bytes.

## 3. The development reads (before the pins; development seeds and the choosing role only)

Every read below closed every balance, every pairing and every commit, and every unreached locus
stayed unchanged.

| Read | Training | Result |
|---|---|---|
| copy, `d = 16`, `K = 4`, `s = 1`, batch 8 | 512 | 16 of 64 sections exact, 424 of 512 stations |
| copy, `d = 16`, `K = 4`, `s = 1`, batch 8 | 2,048 | 31 of 128 exact, 803 of 1,024 stations |
| copy, `d = 16`, `K = 4`, `s = 4`, batch 8 | 1,024 | 1 of 128 exact, 422 of 1,024 stations |
| copy, `d = 16`, `K = 4`, `s = 2`, batch 8 | 1,024 | 7 of 128 exact, 716 of 1,024 stations |
| copy, `d = 32`, `K = 4`, `s = 1`, batch 8 | 512 | 93 of 128 exact, 964 of 1,024 stations |
| copy, `d = 32`, `K = 4`, `s = 2`, batch 16 | 1,024 | 47 of 128 exact, 866 of 1,024 stations |
| copy, `d = 32`, `K = 2`, `s = 1`, batch 16 | 1,024 | **118 of 128 exact, 1,013 of 1,024 stations**, 296,295 ms |
| moiré, `d = 16`, `K = 4`, `s = 1`, batch 8 | 128 | diverged: `E`'s entries grew 1, 6, 26, 316 over four deposits and the words' exact bits with them; stopped |
| moiré, `d = 16`, `K = 4`, `s = 8`, batch 8 | 256 | 1 of 6 windows exact |
| moiré, `d = 16`, `K = 4`, `s = 4`, batch 8 | 512 | 6 of 6 exact |
| moiré, `d = 16`, `K = 4`, `s = 2`, batch 8 | 512 | 6 of 6 exact |
| moiré, `d = 32`, `K = 4`, `s = 1`, batch 16 | 512 | diverged (not finished in 900,000 ms) |
| moiré, `d = 32`, `K = 2`, `s = 1`, batch 16 | 512 | **6 of 6 exact**, 141,671 ms |
| text, `d = 32`, `K = 2`, `s = 1`, batch 16 | 385 (one pass) | stable; 76,580 bits over 12,320 stations; 189,460 ms |

`s` is the step denominator: `γ_U = 1/s`, `η_x = 1/(2s)`. [agent-inferred] **The divergence and
the choice.** The normal law moves a locus's output by the whole covector that reaches it ("the pure
normal solve"); the covector reaching the source port `E` sums every station and every word the
moment re-enters, times the receiving map's gain, and the lattice rule assumes it is unit-scale. On
the moiré, whose windows repeat, those covectors add coherently and the refinement's moment,
re-entering four times, overshot: `E` grew geometrically and the contrast port amplified the words.
Two words halve the re-entries and the covector; at `K = 2` campaign 1's steps are stable on both
terrains and the copy learns fastest, so the declaration keeps campaign 1's steps and takes `K = 2`.
`d = 32` gives the copy's readout room: the 15 offsets of 8 cells read through 4 symbols are 60
directions, which the ring's 64 real coordinates separate and its 32 do not. The step divergence is a
limit of the normal law in a deep refinement, recorded here and not repaired in this loop.
