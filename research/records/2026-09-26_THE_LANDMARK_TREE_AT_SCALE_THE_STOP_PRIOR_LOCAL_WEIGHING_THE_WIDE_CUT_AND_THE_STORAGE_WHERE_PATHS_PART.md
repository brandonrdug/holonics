# The landmark tree at scale: the stop prior, local weighing, the wide cut and the storage where paths part

**Date:** 2026-09-26. **Status:** [historical] measured September 26 (commits `0a43b608` to
`f4bae3de`, #73); moved here verbatim on September 27 from THE_REBUILD's former Decisions 32–37
when the Decisions log dissolved into its owners ([unity audit](2026-09-27_THE_HOLARCHY_AND_ITS_AEONS_ARE_THE_TOP_THE_DECISIONS_DISSOLVE_INTO_THEIR_OWNERS_AND_LEARNING_IS_PROTOTYPED_WHERE_A_HOLARCHY_MADE_THE_TERRAIN.md), #63).

Where each part now lives:
- the laws that stand are in `hnn::landmark`'s module doc: the declared stop prior (§1), the
  stop-weight mixture per digit tree (§3), and the storage where paths part (§6);
- the wide cut and the rule for re-measuring at scale (§4) are in THE_REBUILD's
  [(f) Measurement](../../docs/plans/THE_REBUILD.md#f-measurement);
- the choices that did not stand (§2, the Born face; §3's landmark-local and switching laws; §5,
  second-arrival founding; the full arena) are one line each in THE_REBUILD's
  [(h) Retired choices](../../docs/plans/THE_REBUILD.md#h-retired-choices).

The text keeps its original numbering: "Decision N" resolves through THE_REBUILD's
[Decisions index](../../docs/plans/THE_REBUILD.md#i-the-decisions-index).

## 1. The stop weight is a declared prior (the former Decision 32)

**The landmark tree's stop weight is a declared prior, chosen on the development cells.**
Decision 28 weighs each landmark's own face against its split at `½`, the founding ratio
`β₀ = 1`. Campaign 2's controls showed that this weighting is not the code-length optimum:
constant slots, which carry nothing but raise the stop weight, coded the development cells up
to 133 bits below the cell-only tree.
- **The law.** For any stop weight `w ∈ (0, 1)`, `W_s = w E_s + (1 − w) ∏_b W_(s b)` is the
  mixture over pruned trees with weights `w^(leaves) (1 − w)^(internal nodes)`. Those weights
  sum to one, and the tree codes within `−log₂` of its weight of the best pruned tree. Decision
  28's `½` is the case `w = ½`.
- **The founding.** The executed tree founds each node at `β₀ = w/(1 − w)`.
- **The family.** The declared family is the dyadic ladder `w = 1 − 2^(−j)`, with `β₀ = 2^j − 1`
  an integer, together with its per-depth form.
- **The choice.** Development cells only, charged `⌈log₂⌉` of the family tried, then one
  held-out pass.

Source: agent-inferred, from campaign 2's controls and the Kraft form (`kraft_and_dominance`).

**Measured (September 26).** The development cells choose `½`: of the 256 laws declared (the
global ladder `j = 1..16` and the root-and-below pairs), every other law codes above it, from
`+32 + 7/16` to `+2063 + 7/16` bits, charged 11 bits.
- Held out, the chosen tree reads `3 + 1/16 + ε` a cell. It is above the uncharged `½` tree by
  exactly its 8 family bits.
- The 133 bits of campaign 2's controls are a choice of stop weight per digit tree: the control
  is the per-depth law `(1, r + 1)` joined with the `½` tree in each dyadic cell. Picking the best
  law per digit tree reads `−244 + 9/16` bits before its naming cost.
- The law that could capture it is a mixture of stop weights inside each digit tree. That is
  still Kraft-complete, since each tree pays at most `−log₂` of its weight. It is a measured lead,
  not adopted (Lean `stop_mixture_over_trees`, `stop_kraft_and_dominance`).

## 2. The wave read by the Born rule, measured negative (the former Decision 33)

**The wave reads by the Born rule: reception applies the cell's operator to the ring's state.**
Campaigns 1 and 2 showed that the direct-sum wave earns only the mixture's few bits: the rings
add coordinates, and the text's information lies in the joint correlations of its cells. Brandon,
September 26: light and shadow as one package, composition as weaving, and diligence with
quantum mechanics. The law is a finitely correlated (quantum hidden Markov) receiver on the
receiving ring's register:
- **The state.** The ring's state is a density `ρ`: Hermitian, positive semidefinite, of trace
  one, over the Gaussian rationals and carried on its lattices with certified residuals
  (Decision 24). `ρ` is the retained quotient. It is future-sufficient for this receiver, and it
  keeps no tape.
- **The face.** A cell is emitted as its odometer digits, each digit `i` with operators
  `A_(i,0)` and `A_(i,1)`. The face is
  `p(b | ρ) = Tr(A_(i,b) ρ A_(i,b)†) / Σ_(b′) Tr(A_(i,b′) ρ A_(i,b′)†)`: exactly normalized, and a
  dyadic partition of the unit cell, like the tree's.
- **The reception.** Observing `b` changes the receiver:
  `ρ ← A_(i,b) ρ A_(i,b)† / Tr(A_(i,b) ρ A_(i,b)†)`. This is the elementary reception
  `I_C(|H_S⟩, |H_R⟩) = (|H′_S⟩, |H′_R⟩, f_R)`, with the collapse as its receipt. Between cells
  the ring's power-neutral Cayley tick evolves the state: `ρ ← U ρ U†`.
- **The shadows.** Complex amplitudes add before they are squared, so `Tr(AρA†)` can cancel
  toward zero without any positivity constraint on the operators. Destructive interference
  carves the face's shadows. At equal memory this is strictly more expressive than a
  nonnegative (hidden Markov) receiver (Glasser, Sweke, Pancotti, Eisert and Cirac, 2019).
- **The learning.** The ratio covector of the Born face, `R⁻¹dR` of the trace ratio, is
  deposited into the operators by the normal law's prox step on their lattices.
- **The weighing.** The Born face enters Decision 30's likelihood mixture beside the tree and
  earns its weight only by lowering the code length.
- **The register.** Its width `χ` is chosen on the development cells from a declared family and
  charged.
- **The tensor join.** Rings as the sites of a matrix product state, with the contacts as bonds
  of width `χ_a` and entanglement at most `log χ_a` across each, follows only if the single
  register earns bits.

Success: on the development cells, a register family whose mixture with the tree codes below the
tree alone, charged; then one held-out pass, host and card.

Source: agent-inferred, from campaigns 1 and 2 and Brandon's direction.

**Measured (September 26): negative.**
- **The law as built** (`hnn::born`, Lean `HNN/BornFace`).
  - The state is kept pure (a ray over the Gaussian integers), opened at the ring's harmonic
    mode.
  - The executed digit split sits on `2^(−M)`, so the cell's face is an exact dyadic partition.
  - The tick is the identity: every fixed unitary is absorbed exactly into the first digit's
    operators (`born_tick_absorbed`).
  - The opening operators are the Walsh–Hadamard unitary with declared signs.
  - Learning is Fisher scoring through the normal law's prox step.
  - `born_interference_zero` exhibits two operators whose masses cancel to zero, a zero no
    nonnegative receiver can make.
- **The sweep.** On the development cells, 18 members were tried (two emissions and
  `χ = 1, …, 256`, charged 5 bits).
  - The best Born face, one operator pair per dyadic cell at `χ = 128`, reads `4 + 3/16 + ε`
    bits a cell. That is below order-0 and order-1 and above PPM-2 and the tree
    (`3 + 10/16 + ε`).
  - Every mixture with the tree codes `6 + 0/16 + ε` bits above the tree: the mixture's prior
    bit plus the charge.
  - No held-out pass ran.
- **What it located.** Decision 30's mixture telescopes over the passage to `½W_T + ½W_B`.
  - It earns only when the second face beats the tree over the *whole* passage.
  - A face that is better only in some contexts or epochs can never earn. That is why the wave
    earned only its few bits.
  - The weighing law, not only the wave, limits the machine.

## 3. Weighing is local (the former Decision 34)

**Weighing is local: every face is weighed at each landmark, in each digit tree and across
epochs, by its own evidence there.** Decisions 30, 32 and 33 located one limit. A global
mixture of whole passages cannot use a face that is better only in some contexts or epochs.
Campaign 2's controls found 133 development bits that are a stop weight chosen per digit tree,
and the wave and the Born face lose globally while possibly winning locally. Decision 28's own
law already weighs locally inside the tree: each landmark weighs its face against its split by
that landmark's evidence. The same law extends to every face.
- **At each landmark.** A node's own face becomes the node-level mixture of its KT face and each
  admitted external face (the wave's, the Born face's), weighted by that node's own likelihood
  ratio. It stays normalized and Kraft-complete, and each node pays at most `−log₂` of its
  prior weight.
- **In each digit tree.** Each dyadic cell mixes the declared stop weights by its own evidence:
  Decision 32's measured lead.
- **Across epochs.** A switching (fixed-share) mixture lets the weights move between epochs of
  the passage, at a declared price per switch.
- **The first falsifiable landmark.** On the development cells, the per-cell oracle
  `Σ_t min(ℓ_T(t), ℓ_X(t)) − L_T` bounds what any local mixture of the tree with face `X` can
  gain before its price. If it does not exceed the price, the local law is refused for that
  face.
- **Success.** A local law that codes below the tree on the development cells, charged; then
  one held-out pass, host and card.

Source: agent-inferred, from Decisions 30, 32 and 33, and from Decision 28's weighing law.

**Measured (September 26).** Lean `HNN/LocalWeighing` has 44 declarations. The forward
mixture, its telescope and its dominance underlie all three laws, with fixed-share,
landmark-local own weights and the stop mixture per digit tree. Each law was chosen on the
development cells and charged its family:

| Law | Development, charged, vs the `½` tree | Held out, charged, vs the `½` tree |
|---|---|---|
| the stop mixture per digit tree (`½` joined with `(1, 3)` at `π = ½`) | `−121 + 7/16 + ε` | **`−7 + 12/16 + ε`**, below order-0, order-1 and PPM-2 |
| landmark-local weighing with the Born face | `−52 + 11/16 + ε` | `+17 + 3/16 + ε` |
| switching across epochs | `−98 + 9/16 + ε` | `+11 + 4/16 + ε` |

- The stop mixture is adopted as the count face's law. Its uncharged development gain is
  exactly campaign 2's one-slot control. Mixing all 256 laws per digit tree was refused: its
  naming would cost 1,232 bits against a gain of `244 + 9/16`.
- The other two gained on the development cells and lost held out. Selection among hundreds of
  members on 4,958 development cells does not transfer to 1,190 held-out cells.
- This located the measurement's own limit: the standing cut is too small to choose among
  large families (Decision 35).

## 4. The wide cut (the former Decision 35)

**The count-only receiver is measured on a larger development cut.**
- **Why.** Decision 34 showed that choosing among families of hundreds of laws on 4,958
  development cells does not transfer to 1,190 held-out cells. The development stream holds
  15,462,581 cells, and the standing cut uses its last 6,148. Campaign 2's rebase lifted the
  tree's carrier limit.
- **The cut.** A second pinned development cut holds the stream's last `2^20` cells, which
  include the standing cut. Its final `2^17` cells, one eighth, are held out. The standing cut
  holds out `1,190` of its `6,148`. `2^20` is the largest power of two whose tree fits the workstation's memory
  budget at the measured bytes a node; the worker derives it and refuses a larger cut. The
  evaluation partition stays unspent.
- **What runs on it.** The count-only receivers' laws are chosen on its development cells, then
  one held-out pass is read: the tree, Decisions 32 and 34's laws, the Born face and the
  baselines.
- **What stays.** The HNN's full exposure stays on the standing cut until its cost per window
  falls.
- [correction] **What a larger cut re-measures.** It re-measures the laws already chosen, one
  prequential passage each, in minutes. A family is re-swept only when the scale could change
  its choice, and only at a cost stated in advance. The first run re-swept 529 stop laws with
  their depth sweeps and took 43 minutes to reconfirm `½`, so it was stopped. The development
  cells chose `D = 6` at this scale.

**Measured (September 26).** The wide cut is `.local/cuts/wide-real-cut.{bin,json}`: `2^20`
cells, the final `2^17` held out, with the standing cut as its tail, byte for byte. One
prequential passage was run, taking `109,950` ms with a resident peak under 2 GB.
- **The depth.** The development cells chose `D = 6`. The code fell strictly with depth, and the
  memory cap stopped the sweep at 6. An uncapped probe kept improving down to `D = 16`. `½`
  stayed first among Decision 32's laws.
- **Held out, bits a cell** (each `+ ε`):
  - the tree `1 + 15/16`;
  - the adopted stop mixture `1 + 15/16`;
  - PPM-2 `3 + 0/16`;
  - order-1 `3 + 12/16`;
  - order-0 `4 + 13/16`.
- **Orderings.** The tree is below PPM-2 by `−133980 + 11/16 + ε` bits in all, more than a bit
  a cell. The adopted mixture, charged 15 bits, is below the tree by `−38 + 7/16 + ε`: it
  transfers, and the gain is small.
- **The carriers.** At `2^20` the carriers hold within the rule: `M_p = 55`, `W = 36`, the
  largest operand 127 bits, and the largest residual within its bound.
- **Disclosed.** The standing cut lies inside the wide cut's held-out range, and the adopted law
  was designed on those cells. On them the adopted law now reads `+2 + 12/16` above the tree.
  Its gain at scale is made on other cells.
- **What it located.** The tree learns with the passage: `3 + 1/16` a cell on the standing cut
  alone, `2 + 0/16` on the same cells inside the wide passage. Depth is limited by memory, at
  `178` bytes a node and 5,110,443 nodes at `D = 6` (Decisions 36–37).

Source: agent-inferred, from Decision 34's measurement.

## 5. Founding at the second arrival, measured and retired (the former Decision 36)

**A landmark is founded where paths converge: at its second arrival, not its first.** The
objects define a landmark as a face where navigator paths converge (CLAUDE.md, "Holonic
Compression"). Decision 28 founded every node at its first arrival.
- **The problem.** At scale the deepest nodes are mostly visited once. They hold no convergence,
  and they cost memory that caps the depth the development cells want: `D = 6` at the memory
  cap, with improvement continuing to `D = 16`.
- **The law.** A node is founded at its second arrival. Until then, the path read stops at its
  founded parent. The first arrival is recorded only as the parent's counts, which the tree
  already holds.
- **What changes.** This declares a different prior: an unfounded child reads as absent, not as
  a KT node with one count. So it is a new law with its own Lean (normalization, Kraft form,
  dominance), not an approximation of Decision 28's.
- **What is measured.** On the wide cut's development cells, the convergence-founded tree
  against Decision 28's at equal memory. The depth it admits under the cap. Then one held-out
  passage. Nodes, memory and time are reported beside the code.

**Measured (September 26).** One development sweep and one held-out passage on the wide cut
(notebook `hnn_landmark converge`; Lean `HNN/ConvergenceFounding`, 31 theorems).
- **Memory.** The pending records bound the memory at every depth: the carriers admit `D ≤ 73`.
  The development cells chose `D = 19` of 20, at 671,092,356 live bytes, against 914,360,948
  for Decision 28's tree at `D = 6`.
- **Development.** The convergence tree codes `1827190 + 13/16 + ε` bits (charged 6 for its
  choice). That is above Decision 28's tree at `D = 6`, `1822006 + 1/16 + ε` (charged 4), by
  `5186 + 12/16 + ε`. The development cells choose the first arrival, so Decision 28's founding
  stays.
- **Held out** (disclosed, not a choice). The convergence tree is below Decision 28's by
  `−490 + 11/16 + ε` bits, and below PPM-2 by `−134468 + 7/16 + ε`.
- **What it located.** A node at depth `d` opens only after its context has recurred `d + 1`
  times, one level a recurrence. Deep contexts open late: the early cells pay and the late cells
  gain. The memory it saved is had without changing the prior (Decision 37).

Source: agent-inferred, from the landmark definition and Decision 35's depth limit.

## 6. The tree is stored at the faces where paths part (the former Decision 37)

**The tree is stored at the faces where paths part.** Decision 28's prior needs no late founding
to save memory, because its unary chains are determined by their ends.
- **The law.** Consider a chain of nodes, each with one reached child. Every node on it routes
  the same arrivals: the address is padded with `Boundary`, so every arrival runs to the declared
  depth. So each node holds the same counts and the same KT face `P_e`.
  - With `ρ = P_w/P_e`, the weighting reads `1 − ρ_j = (1 − w_j)(1 − ρ_(j+1))`. For the dyadic
    rungs `w_i = 1 − 2^(−j_i)` this gives `1 − ρ_top = 2^(−Σ j_i)(1 − ρ_bottom)`, an exact shift.
  - So a chain with the node below it is one Decision 28 node whose rung is the chain's summed
    rung. With `X` the product of the bottom's children, `P_w(top) = W E + (1 − W) X` with
    `1 − W = 2^(−Σ j_i)`. It is founded at `β₀ = 2^(Σ j_i) − 1`, and its `β` steps by the
    unchanged law.
  - A chain that ends at the declared depth (a leaf, `w = 1` there) has `ρ = 1` at every node,
    so it reads as one KT node.
  - A split at a chain's depth `k` cuts its rung into `S = S_up + S_low`. The lower part keeps
    its counts at `β_ℓ = β (2^(S_low) − 1)/(2^S − 1)`. The upper part holds the same counts at
    `β_u = (2^(S_up) − 1) 2^(S_low) β_ℓ / ((2^(S_low) − 1)(β_ℓ + 1))`, which is
    `2^(S_up) − 1` above a leaf.
- **What is stored.** The compacted tree stores each chain with the node below it:
  - each node with at least two reached children, where paths part;
  - each leaf, whose chain runs to the declared depth;
  - each with its label: the letters from its parent's face to its bottom.

  A root with one reached child folds into its chain. The root is stored alone only before any
  arrival.

  An arrival that parts from a label at depth `k` founds a node there with the label's counts and
  its chart from the closed form.
- **What does not change.** The prior. This is Decision 28's tree at the declared `D`, code for
  code, exactly in ℚ. No family is re-swept; only the depth is re-chosen, because memory no
  longer caps it.
- **Memory.** A passage of `n ≥ 1` cells keeps at most `2n − 1` nodes in each digit tree it
  enters, at any depth, each with its label.
- **Retired.** Decision 36's Rust realization: `Founding::SecondArrival` and the pending
  records. Its Lean stays as the law of absent children and stopping rules.
- **What is measured.**
  - Exact equality with `IdealLandmarks` at the same `D` on small passages.
  - On the wide cut's development cells, a depth sweep that doubles from 6 until the code rises:
    at most five passages, stated in advance at about two minutes each, with memory and time
    beside the code.
  - Then one held-out passage.
- **The card.** If the development cells adopt the depth, the card ports the compacted arena in
  the same step (Decision 25).

**Measured (September 26).** Lean `HNN/LandmarkCompaction` proves `compacted_is_decision_28`
for every passage: the compacted root weight is `stopWeight`, every face is `stopFace`, positive
and normalized, and both prequential codes are equal in ℚ. `compacted_node_bound` keeps at most
`2n − 1` nodes a tree. Rust `Landmarks` in `hnn::landmark` runs the same `Law`, and
its oracle equals the full oracle exactly in ℚ at every face in the tests. Each split ratio is
carried once at `W` bits, and its unit enters the drift. On the wide cut (notebook
`hnn_landmark compact`, 177535 ms in all):
- **The check at `D = 6`.** On the development cells the compacted and full trees both read
  `1822006 + 1/16 + ε`. They are equal within their certificates. The compacted tree holds
  2784875 nodes in 477104868 allocated bytes; the full tree holds 4620707 nodes in 914361060.
  Allocated bytes count the containers' capacity, not their occupancy.
- **The depth sweep** (development, charged `⌈log₂ 5⌉ = 3` bits, the same as Decision 35's
  charge for its depth):

  | D | code | nodes | allocated bytes | ms |
  |---|---|---|---|---|
  | 6 | `1822006 + 1/16 + ε` | 2784875 | 477104868 | 14291 |
  | 12 | `1802252 + 14/16 + ε` | 8527193 | 1920994548 | 22078 |
  | 24 | `1801962 + 7/16 + ε` | 10664559 | 1996493076 | 23988 |
  | 48 | `1801940 + 12/16 + ε` | 10985626 | 2097158484 | 24936 |
  | 73 | `D = 48` plus `0 + 0/16 + ε` | 11066401 | 2202018284 | 25133 |

  The rise at 73 lies within the certificates. **The development cells choose `D = 48`**, which
  is `−20066 + 10/16 + ε` below Decision 28's `D = 6`. Decision 37 is adopted.
- **Held out** (one passage, 131072 cells). The tree at `D = 48` reads `258201 + 3/16 + ε`,
  which is `1 + 15/16 + ε` a cell. Charged, it is below Decision 28's tree by
  `−3416 + 15/16 + ε`, below PPM-2 by `−137395 + 11/16 + ε` (a cell `−2 + 15/16`), below order-1
  by `−238483 + 1/16 + ε` and below order-0 by `−373509 + 2/16 + ε`. Each ordering is decided
  by disjoint exact enclosures. The passage stores 12542969 nodes and 40352545 label letters. The
  harness's resident peak was 1594884096 bytes.
- **On the card** (Decision 25, #76). The receiving path and the card run the compacted tree,
  the only storage left. Retired with it: the full arena, and Decision 34's node-local law's Rust
  (measured at `d2a2e0db`; its Lean stays). `W` is derived from `2n* + 1`, which keeps the rule
  below half a grain. The GPU suite ran alone on an idle card: 39 passed. Campaign 1's exposure on
  the card reads every recorded reading unchanged, host and card identical. Held out the whole
  HNN reads `3 + 1/16 + ε` a cell. It is below order-0 by `−1996 + 12/16 + ε` and below PPM-2
  by `−252 + 5/16 + ε`. The constitution holds 4836937 bits. The card takes
  `103 rem 2667 over 3074` ms a window.
- **What it located.** The development cells wanted depth, and memory had been hiding it. Once
  the tree is stored at its parting faces, the depth costs at most two nodes an arrival, and the
  code still falls at `D = 48`. Decision 36's held-out gain is had here without its
  development loss.

Source: agent-inferred, from Decision 36's measurement and the unary-chain identity (the
compacted context tree of Willems's unbounded-depth weighting).
