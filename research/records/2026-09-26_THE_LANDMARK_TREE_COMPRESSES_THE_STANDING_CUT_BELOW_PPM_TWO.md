# The landmark tree compresses the standing cut below PPM-2

[historical] September 26. Decision 28's count-only landmark tree, measured on the standing real
cut (Decision 23) under the prequential protocol (Decision 29). Owners: Lean
`HNN/LandmarkTree`, Rust `holonics::hnn::landmark`, notebook `hnn_landmark.rs`; issue #73.

## 1. What ran

[definition] The receiving parametron's storage is a tree of landmarks. Each node is a typed
address word: the preceding cells, newest first, with `Boundary` before the cut. A node is founded
at first arrival and holds Krichevsky–Trofimov masses (one per two) in half-units. The face is the
context-tree weighting along the one path the current address opens, and a deposit moves only
that path (`landmark_step`, `treeWeight_arrive_off`).

Two emissions were declared.
- `Digits`: a cell is emitted as its eight binary odometer digits, most significant first. Each
  digit is read at its dyadic cell, a forced split, then mixed over the context letters. The
  executed face is a dyadic partition of the unit cell. Each digit's ideal split is rounded to the
  lattice `2^(−M_f)`, and the cell's face is the width of its descended interval
  (`executed_split_laws`, `cell_faces_partition`).
- `Cell`: the whole cell carries 256-ary KT masses at each node. Its depth-one forced case is
  Decision 27's region table (`depth_one_is_decision_27`), and a test checks that equality exactly.

[definition; agent-inferred] Every width is derived rather than tuned.
- **The mixture ratio `β = E/∏W`** is carried exactly while its odd parts fit `W` bits, and
  rebased past that. The exponent is its carry; the mantissa is its phase within the octave.
  - `W` is the least width with `2^W > 8 L_R n*`: `W = 20` at `n* = 6148 = 2²·29·53` and
    `L_R = 16`.
  - This holds the accumulated log₂ residual at a node below one grain over the passage.
- **The digit face's width** is `M_f = ⌈log₂(2n*+2)⌉ + ⌈log₂(B L_R)⌉ + 2 = 23`.
  - Every digit face is a convex combination of binary KT faces, so it is at least `1/(2n+2)`
    (`digit_face_ge`).
  - Rounding moves `ln q` by at most `ε/(μ−ε)` with `ε = 2^(−M_f−1)` and `μ = 1/(2n+2)`
    (`digit_log_residual`).
  - The first-order form `ε(2n+2)log₂e` fails when rounding moves the face down: `M = 7`, `n = 42`,
    `q = 1/86`, `q̂ = 1/128` (`host_digit_bound_fails_downward`).
- **The depth** is chosen on the development cells only. `D` rises from 1 while the development
  code length decreases strictly, and `⌈log₂⌉` of the family tried is charged as description bits.

## 2. The receipt

Bits a cell at the grain `L_R = 16`, prequential, over the same cells in the same order for every
coder. Each cell is scored at the standing before its own deposit.

| Coder | Held out (1,190 cells) | Development (4,958 cells) |
|---|---|---|
| tree `Digits`, `D = 4` (executed dyadic face) | `3 + 1/16 + ε` | `3 + 10/16 + ε` |
| tree `Digits`, its ideal ℚ face | `3 + 1/16 + ε` | `3 + 10/16 + ε` |
| tree `Cell`, `D = 1` | `4 + 12/16 + ε` | `4 + 15/16 + ε` |
| uniform | `8` | `8` |
| online order-0 KT | `4 + 12/16 + ε` | `4 + 15/16 + ε` |
| online order-1 KT | `4 + 5/16 + ε` | `5 + 1/16 + ε` |
| PPM-2 (escape C) | `3 + 4/16 + ε` | `3 + 12/16 + ε` |

The held-out cells decide three orderings. Each is a disjoint pair of exact enclosures, with the
tree charged its three depth bits.
- The tree lies below order-0 by `−1987 + 15/16 + ε` bits in all (a cell: `−2 + 5/16 + ε`).
- It lies below order-1 by `−1485 + 14/16 + ε` (a cell: `−2 + 12/16 + ε`).
- It lies below PPM-2 by `−243 + 7/16 + ε` (a cell: `−1 + 12/16 + ε`).

All three orderings also hold on the development cells. Decision 28's criterion holds.

The depth sweep for `Digits`, on the development cells:
- `D = 1`: `4 + 0/16 + ε` a cell.
- `D = 2`: `3 + 12/16 + ε`.
- `D = 3`: `18152 + 7/16 + ε` in all.
- `D = 4`: `18067 + 2/16 + ε`.
- `D = 5`: `18098 + 7/16 + ε`, which rose, so `D = 4` is kept.

The `Cell` emission stops at `D = 1`.

The charts:
- **Founding and rebasing.** Tree `Digits` founded 63,320 landmarks and rebased 91,781 times.
  Its most-rebased node rebased 6,120 times, a bound of `765/16384` bits, below one grain.
- **The dyadic partition's cost.** The executed face costs `0 + 0/16 + ε` bits over the ideal face
  in all.
- **The per-cell residual.** The largest certified per-cell residual is at most `463939/2^31`
  bits. The rule's a-priori bound is `24596/2794153`.
- **Wall time.** The prequential run took 56,757 ms and the two depth sweeps 216,970 ms. A second
  run reproduced every value. The exact enclosures and the PPM-2 fibre are in the notebook's
  receipt row.

## 3. What the receipt says

[interpretation] The compression Brandon named is here in its first, count-only form. It is the
landmarks connecting the navigator's addresses, opened one path at a time. Shallow and deep
landmarks are weighed by their own code-length evidence at every node, not by a frequency rule.
- It passes PPM-2, which escapes between fixed orders.
- It passes order-1 KT, which pays for a 256-ary face in every context.

The two emissions separate cleanly.
- **The `Cell` tree never earns a split.** A whole-cell KT context carries a prior mass of 128 over
  256 classes, so a sparse context's evidence never outweighs it. Its face stays at the root's
  order-0 face.
- **The `Digits` tree splits.** The odometer digits factor the cell through its dyadic
  restrictions. A context then pays only for the digits it actually visits, and the scale square
  of the alphabet becomes the address of the prediction.

[conditional] This is a finite-cut ordering and not the CTW redundancy theorem.
- `kraft_and_dominance` proves the tree mixture is within `Γ(S)` bits of every pruned tree's
  code.
- The KT parameter bound that completes CTW's theorem is binary and is owed in #62.
- The β chart's per-node bound and the wide-face reading (`landmark::code_length`, a 98-bit
  mantissa with a certified widening) are stated in Rust and checked by tests. Their Lean
  statements are owed in #62.

## 4. Corrections found on the way

- **The fixture.** The CTW paper's example is `0110100` after the past `010`, which gives the
  weighted probability `95/32768`. The pair first briefed, `0100110` after `110`, gives `7/2048` in
  the paper's convention. The test keeps both: the paper's pair, and the briefed pair checked
  against an independent block recursion.
- **The reading.** `log2_enclosure` of a tree face of about 3,000 bits costs about 80 ms. A certified
  mantissa reading costs about 3 ms. The baselines' faces are never that wide on this cut
  (`n* + |A| ≤ 2^24`), so they read exactly as before.

## 5. What it changes

[definition; agent-inferred] The receiving face that later campaigns measure against is the
landmark tree's, not Decision 27's region table, which is its depth-one case.
- The wave earns its computation only by lowering the code length below this count-only face,
  whether as address letters the tree weighs in or as a correction.
- The HNN's exposure moves to the prequential protocol (Decision 29), with per-cell causal
  addresses in place of the aperture-two window's pooled region.
