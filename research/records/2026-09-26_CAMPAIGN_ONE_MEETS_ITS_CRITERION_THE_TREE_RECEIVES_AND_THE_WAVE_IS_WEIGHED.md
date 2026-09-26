# Campaign 1 meets its criterion: the tree receives, and the wave is weighed

**Date:** 2026-09-26. **Status:** recorded (#73, campaign 1's repair; Decisions 28–30).
**Occasion:** the [located failure](2026-09-25_CAMPAIGN_ONE_LOCATED_FAILURE.md) named three missing
terms. The [landmark tree](2026-09-26_THE_LANDMARK_TREE_COMPRESSES_THE_STANDING_CUT_BELOW_PPM_TWO.md)
then compressed the standing cut below PPM-2 on its own. This record keeps the receipt of the whole
HNN with the tree as its receiving face.

## 1. What changed in the machine

[definition; agent-inferred] These changes are stated in their owners: `hnn::receiving`
(`ActiveAddress`, `Mixture`, `grain_exponent`), `hnn::landmark`, `hnn::moment::PopulationChart`
and `hnn::reference`.

- **The receiving parametron's storage is the landmark tree** (`D = 4`, the odometer-digit
  emission, on its fixed-width lattice). It replaces Decision 27's region table, the depth-one case
  of the tree's whole-cell emission (Lean `depth_one_is_decision_27`), which is not the digit tree's. The region table retires from Rust.
- **Each phase reads the tree at its own causal address.** The address is the window's earlier
  targets, then the receiver's active suffix address. The resident keeps that address beside the
  tree, shifts it at each ingest, and keeps it across the collapse. The moment's window and `n*`
  are unchanged. This repairs the aperture-two window's pooling of lags one and two.
- **Every comparison is scored before its own deposit, then deposited, held-out cells included**
  (Decision 29). The held-out asymmetry against the online baselines is gone.
- **`R_0 = 0`, and `E_0` is the sign generator times ½.** The located failure's prior reading
  `R_0 z` alone was `10 + 9/16 + ε` bits a cell. With both maps at zero every feature is zero and
  the wave never moves. With `E_0` nonzero, `R` moves at commit 2 and the upstream loci at
  commit 3 (window 0 opens on an empty moment). `E`'s persistent prior is a fixed feature map that
  `R` reads, not a face term.
- **The scored face weighs the tree's face against the combined face** (tree plus wave) by their
  likelihood ratio (Decision 30).
- **The source opens on its normalized counts** (Decision 26's third term, Lean
  `HNN/IndexedOpen`). Each `1/n` is a lattice chart with a certified residual, so the word stays
  dyadic on the card.

## 2. The receipt

The standing real cut: 3,074 windows and 3,074 deposits, complete, prequential. Bits a cell at the
grain `L_R = 16`:

| Law | model, held out | tree alone | combined face | model, development |
|---|---|---|---|---|
| the tree wired in, no mixture | `13 + 11/16 + ε` | `3 + 1/16 + ε` | (the model) | `8 + 2/16 + ε` |
| with the mixture | `3 + 1/16 + ε` | `3 + 1/16 + ε` | `13 + 10/16 + ε` | `3 + 10/16 + ε` |
| with the mixture and the normalized open, scored in cell order | `3 + 1/16 + ε` | `3 + 1/16 + ε` | `3 + 1/16 + ε` | `3 + 10/16 + ε` |

The first two rows read the tree alone at the grain and step one `β` a window; the review found
both, and the last row reads the tree on its exact face (the face the mixture weighs), each phase's
tree face after the earlier phases' deposits, and `β` stepped per phase.

The held-out baselines read order-0 `4 + 12/16 + ε`, order-1 `4 + 5/16 + ε` and PPM-2
`3 + 4/16 + ε`. Under the final law, held out and in all (each `+ ε`):
- model − order-0 reads `−1996 + 12/16`: **the campaign criterion is met**;
- model − order-1 reads `−1494 + 11/16`;
- model − PPM-2 reads `−252 + 5/16`;
- `L_C − L_T` and `L_model − L_T` each read `−7 + 13/16` (development `−19 + 12/16` and
  `−18 + 12/16`); the tree at the grain less its exact face reads `0 + 6/16`.

Each ordering is decided by disjoint exact enclosures. The exposure's exact tree sums equal the
count-only tree's exactly.

**The wave's course.** `log₂ β` at the aeon boundaries reads `−2 + 9/16`, `−8 + 10/16`,
`−12 + 2/16`, `−17 + 2/16` and `−21 + 0/16`, and `−25 + 9/16` at the end (each `+ ε`), carried at
`W = 28` with 6,147 rebases and a certified drift of `5844186179759863429570124736444603/2^126`
bits.

**Disclosure.** The mixture and the normalized open were adopted after full-cut runs whose readings
included the held-out cells. The three laws tried are charged `⌈log₂ 3⌉ = 2` bits, so the wave's
held-out gain is `5 − 13/16 − ε` bits. The margins against the baselines are unaffected. The wave's
maps are read at the window's opening standing, so the cell-by-cell protocol holds for the tree,
`β` and the baselines, and window by window for the wave.

**Parity and cost.**
- **Parity.** The host and the card (`holonics_cuda::hnn::Resident`) print identical readouts, line
  for line, outside the wall times and the traffic: 3,303 lines. Every interaction return matched
  in lockstep, the tree's and the mixture's staged steps included.
- **Wall time.** The host took 399,911 ms (`130 rem 291 over 3074` ms a window) and the card
  353,499 ms (`114 rem 3063 over 3074` ms a window).
- **The tree read** costs `1727 rem 2244 over 3074` µs a window on the card run, against the
  card's word refine read of `2113 rem 276 over 3074` µs; the in-window overlay adds 49 µs.
  The card port of the tree read is a #76 debt.
- **The carrier limit.** The tree's lattice widths outgrow `u128` from 87,382 cells at campaign 1's
  `|A| = 256`, `D = 4`. A carrier law for longer passages is also owed in #76.

## 3. What it says

[interpretation] The compression carries campaign 1: its landmarks and their code-length weighing
hold the passage below PPM-2.
- The wave, the helical machinery's rings, contacts and charts, now earns weight honestly. Its
  features no longer grow with the population, and it lowers the code length in every aeon.
- It earns only a few bits so far (`5 − 13/16 − ε` after the charge), far less than its
  computation costs.
- Campaign 2's rings and contacts (storage, lock and flow) are therefore measured by the same
  mixture. A navigator's modes earn their place by the bits they save against the landmark tree.
