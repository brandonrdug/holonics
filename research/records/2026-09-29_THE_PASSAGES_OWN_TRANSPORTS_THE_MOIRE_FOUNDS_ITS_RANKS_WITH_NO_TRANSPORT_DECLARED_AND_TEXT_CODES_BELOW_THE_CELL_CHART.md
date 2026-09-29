# The passage's own transports: the moiré founds its ranks with no transport declared, and text codes below the cell chart

**Date.** September 29. **Issues.** #73, #148, #63 (THE_REBUILD U6). **Grade.** [measured] for the
receipts, read once each against the [pin](2026-09-29_THE_PASSAGES_OWN_TRANSPORTS_PINNED_BEFORE_ITS_RUNS.md)
(`962d038e`) on the build `32314569`; [proved-derived; formal-checked] for the Hankel identification;
[agent-inferred] for §5.

The computational object is the helical pair interaction. Of the winding guide's six objects the loop
touches **faces and placement** (the founded forms and each founded class's placement), the **helix**
(the passage's right actions and the rings' selective clock, which the founded classes now step) and
the **tower thread** (a class not born restricts to its parent); the pair, the cell holonomy and the
tube stay attached through the moment chart, `Field::holarchy` and the word.

## 1. What was built

- `hnn::encoding::ContextClasses`: a passage's context classes (its words' end-position classes)
  reached from the empty context by the cells' right actions `T_u e_p = e_(pu)`, with their parents; a
  closed cycle's positions are read modulo its period.
- `PassageChart::passage` (one transport per reached cell, `B e_u = e_[u]`, the forms
  `ρ_c(p) = N(pc)`, the opening) and `PassageChart::unconditioned` (the passage's own tick
  `Σ_u T_u`). `Encoding::found` on them is the passage's Hankel realization; no transport is declared.
- `found_passage`, the charged founding: the reach closure's ladder, each reached class born only
  where `receiver::population::birth_price` (`merge_cost_mass_iff` read from the birth's side, at the
  charge `(|A_R| + 1)²`) shortens the founding passage's KT code; `PassageChart::founded` and Birth's
  closure on the founded machine.
- The consumers: `found_ports` places the founded classes; `hnn::field::{PortChart, FoundedMachine}`
  carry the machine and the step codes; the source moment carries the founded class; the target
  phases, the keys' crib and the letters' reader read step codes; `E_0` opens at the founded
  injection; the card refuses a founded machine. The exterior founding (the identity its only
  transport) is retired. `birth::Closure` reads its dependents' coordinates in blocks of the basis's
  size (the whole kernel at once carried every dependent against every other).
- Lean `HNN/Encoding`: `hankel_identification`, `hankel_rank_eq`, `forms_span_kernel`,
  `continuation_intertwines`.
- The harnesses: `hnn_exposure` (`ports passage`, `expansions`, `found-only`) and `hnn_prediction`
  (`text … founding <cut> [train <pairs>] [passes <n>]`, `probe … founding <cut>`,
  `develop text … [founding cut]`).

## 2. Acceptance 1, the exact checks with no transport declared

`hnn::tests::encoding`, the terrains and draws of the encoding loop. On every terrain `D E = ρ`,
`E T = U E` and the injection square held exactly on every reached state, in both readings.

**The moiré holds as pinned.** Every emission is periodic from its start.

| Rates (parity) | Least period | (a) the letters' founding = count Hankel rank | (b) the unconditioned tick = the declared rank |
|---|---|---|---|
| `1/3, 1/4` | 12 | 12 | 7 |
| `1/4, 1/6` | 12 | 12 | 7 |
| `1/4, 3/5` | 20 | 20 | 11 |

(a) is the rank of `[N(ps)]` counted over the cycle independently of the founding (contexts and
futures up to one cell past the cycle's determining depth); the derivation's correction in the pin
predicted 12, 12 and 20. (b) equals the declared chart's founded dimension and the cycle's block
Hankel rank.

**The rotor crib: (a) holds; (b) fails as pinned.** Every one of the eight draws falls, after a
transient, into one fixed cell, so its closed cycle is that cell:

| Ring | Declared founding | Transient | Least period | (a) | (b) |
|---|---|---|---|---|---|
| 0 (`d = 5`), four draws | 4, 4, 3, 6 | 3, 3, 2, 5 | 1 | 1 | 1 |
| 1 (`d = 7`), four draws | 32, 16, 40, 16 | 31, 15, 39, 15 | 1 | 1 | 1 |

The declared dimension is the transient and the fixed cell (the reached orbit is a path into a fixed
point, not a cycle); reading the periodic part drops the transient, so (b)'s pinned equality with
3–6 and 16–40 does not hold on the crib. The pin assumed the crib's orbits were cycles; they are not.

**Beside it** (the same tests): a drawn word of 10 cells founds exactly 10 (the exact realization
is an index); the charged founding keeps the opening alone on a drawn word of 400 cells over 4
cells; on `3 1 4 0 2` repeated it founds 5 classes (the opening absorbs `2`'s context, whose
successor it already reads); the passage chart's moment of a driven passage is the sum of its suffix
contexts' classes and its encoding runs the founded recurrence `z ← U_u z + J e_u`. **The ladder is
myopic**: on `0 1 0 2` repeated it keeps `0` alone, since `10` and `20` are reached only from `1` and
`2`, which add nothing alone once the opening reads their successor.

## 3. Acceptance 2, text: holds

`hnn_exposure -- cut-file u6-encoding-probe.bin cells all ports passage`, the host, the pin's 6,148
bytes (4,096 development, 2,052 held out; no reserve, no evaluation window).

- **The founding** (the development part only): 65 reached cells; the ladder's rungs
  (reached, born, undecided) `(65, 24, 0)`, `(273, 10, 0)`, `(43, 1, 0)`, `(6, 0, 0)`; 36 founded
  classes, 0 returned; Birth's closure keeps all 36 (founded dimension 36 on 36 reached); a plural
  fibre of 191 codes. The development cells' KT code falls from `18585 + 3/16 + ε` at the opening
  alone to `16097 + 8/16 + ε` over the founded classes, with the classes' description
  `429 + 2/16 + ε`. 24 of the 36 classes are one-cell contexts; the longest shortest-member is 3
  cells.
- **Recurrence** (sorted anonymous counts): development `[936, 568, 396, 262, 228, …, 7, 4]`, the
  fibre 0; held out, read from the opening, all 36 classes recur, the fibre 8.
- **Placement**: ring 0's lock holds 3 classes, on 174 development cells (the 65-cell chart's 210,
  the residue chart's 842); rings 1 and 2's, 2 and 1 classes on 147 and 135 cells.
- **The code** (the receiver's face on campaign 1's field, every reading at `L_R = 16`,
  `ε ∈ [0, 1/16)`):

| Reading | The 65-cell chart (`38cf65ac`) | The passage-founded chart | The residue chart (the attribution run) |
|---|---|---|---|
| held out, the field's face | `5463 + 9/16 + ε` | `5461 + 10/16 + ε` | `5459 + 13/16 + ε` |
| held out, the tree alone | `5476 + 3/16 + ε` | `5476 + 3/16 + ε` | `5476 + 3/16 + ε` |
| held out, the field's part (field − tree) | `−13 + 5/16 + ε` | `−15 + 7/16 + ε` | `−17 + 10/16 + ε` |
| development, the field's face | `13069 + 2/16 + ε` | `13068 + 0/16 + ε` | `13069 + 5/16 + ε` |
| `Kt`, the whole passage charged | `20022 + 11/16 + ε` | `20023 + 10/16 + ε` | `19992 + 3/16 + ε` |

  The held-out code is **strictly below `5463 + 9/16 + ε`**: its enclosure's upper end is below
  `5461 + 11/16`, the other's lower end is `5463 + 9/16`, so it is shorter by more than `1 + 14/16`
  and less than 2 bits. `Kt` charges the description (1,467 bits: the chart's rule 2 and its
  founding passage's length), 4 key bits (ring 3's key published at the one aeon boundary, cell
  3,574) and `⌈log₂ work⌉ = 23`. The joint clock closed one aeon (at cell 3,574) against two on the
  65-cell chart; at its boundary ring 3's key was published and rings 0–2 fell back, where every key
  fell back before.
- **Work and memory**: setup 9,692 ms (the founding 9,647); the exposure 427,589 ms over 3,074
  windows; peak 381,263,872 bytes, within the ten-minute and 20 GB projection.

## 4. Acceptance 3, to eyeball

The founded classes' expansions and the 8 sections were shown in the conversation only, whole; the
material is private and is not in the repository.

**The pinned prediction run passed its bound twice and produced no section.** `hnn_prediction --
text` on the choosing role's pairs with the chart founded on the probe's development part (36
classes, a fibre of 192 codes on the field's 257 codes):
- the first run was stopped by its external bound at 660,000 ms (exit 124) after 16 deposits (their
  stages 199,286 ms and deposits 44,934 ms), with no training report and no section;
- the rerun, projected at 15 minutes, was stopped at 900,000 ms the same way, at 3,116,012 kB
  resident (against the pinned run's 819,576,832 bytes on the residue chart).

A development reading (`develop text`, one pass over the choosing pairs, never the validation role)
located the blocker by its measurement: on the founded chart a batch's stage took 2,043–8,751 ms up
to the eighth deposit, then 55,433 ms at the ninth, 22,392 at the tenth, 10,563 at the fifteenth
and 47,107 at the sixteenth, and the seventeenth batch did not end within the reading's remaining
160 s; the word's peak bits reached 42. On the residue chart every batch staged in at most 6,047 ms
(the whole pass, 25 deposits, in 187,334 ms), the peak bits 37. The founded `E_0` (each
code's column at one node, many codes sharing a node) is the only difference on this field, whose
source ring's lock admits every port.

**The sections shown are a bounded reading, not the pinned run** (`train 128 passes 1`: 128
choosing pairs, one pass, 8 deposits, 68,477 ms of training, 69,668 ms in all, peak 783,413,248
bytes). Every refinement's checks held (128 balances, 128 pairings, 128 commits, 56 unreached loci
unchanged). Six of the eight sections released the termination at their first station (no bytes);
two released 32 bytes each of `r`, `e`, `s`, `o` and spaces. They are illegible.

## 5. The verdict

- **Acceptance 1**: the moiré holds exactly in both readings (12, 12, 20 by the letters, as the
  derivation corrected; 7, 7, 11 by the tick, as the brief asked). On the crib (a) holds and (b)
  fails as pinned: its emissions fall into a fixed cell, so the closed cycle is one cell and drops
  the transient the declared founding counts.
- **Acceptance 2 holds**: the held-out code is between `1 + 14/16` and 2 bits below the 65-cell
  chart's, every charge included.
- **Acceptance 3**: the expansions were shown. The pinned prediction run passed its bound twice and
  produced no section; the 8 sections shown come from a bounded reading (128 pairs, one pass) and
  are illegible, six of them empty.
- **What stays open, by its measurement** [agent-inferred]: the passage-founded chart still codes the
  held-out cells about `1 + 13/16` bits above the residue chart with the sign sequence; ring 0's lock
  admits 174 development cells against the residue chart's 842; the founded classes are mostly
  one-cell contexts (24 of 36), and the ladder is myopic (a class that pays only through a longer
  class it opens is never born). The source moment still bins the exterior cells by the rings'
  phases; the founded classes enter only the steps and `E_0`. On the prediction field, whose source
  ring steps on every cell, the founded `E_0` alone makes the refinement's exact cost grow past its
  bound from the ninth deposit (a stage of 55,433 ms against at most 6,047 on the residue chart).

## 6. Owed in #62

**HNN/Encoding (U6, the passage's own transports, `32314569`).** Proved: `hankel_identification`,
`hankel_rank_eq`, `forms_span_kernel`, `continuation_intertwines`, which close the linear half of the
owed item "the reach-restricted founding meets the emission's Hankel rank". Owed:
1. *Birth's executed closure spans the readings.* The stable rung of `Closure::found` restricted to
   the reached span is `span{ρ ∘ T_w}`, so `forms_span_kernel` applies to the executed forms
   (`Compression/Landmark/Context/Birth.{ladder_stabilizes, founded_le}` joined to `HNN/Encoding`).
2. *A primitive cycle's count Hankel rank is its period; a word's is its length* (the passage's exact
   realization is an index). Measured in `hnn::tests::encoding`.
3. *The founded machine is causal and its placement is SelectiveDecl's*: a cell's step code is a
   function of the cells before it, and the field reading the passage-founded chart steps the
   founding passage exactly as the founding did (extends the owed item on the founded chart's
   causality). Tested, not proved.

## 7. The gates

- `cargo check --workspace --all-targets`: clean.
- `cargo test -p holonics --lib`: 923 passed (the encoding tests 13, the merge tests 12).
- The GPU suite, alone on the card under `.local/gpu.lock`:
  `cargo test -p holonics-cuda -- --include-ignored --test-threads=1`, 32 passed (the card refuses a
  founded machine; its residue-chart paths are unchanged).
- `bash tools/lean_check.sh Holonics HolonicsResearch`: 10,246 jobs, no `sorry`.
