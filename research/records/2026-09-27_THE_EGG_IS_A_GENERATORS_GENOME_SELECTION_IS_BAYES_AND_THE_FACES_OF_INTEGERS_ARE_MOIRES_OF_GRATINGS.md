# The egg is a generator's genome, selection is Bayes, and the faces of integers are moirés of gratings

**Date:** 2026-09-27. **Follows:** [egg packing](2026-09-27_EGG_PACKING_THE_MOIRE_OF_TWO_HELICES_IS_A_TORUS_KNOT_AND_THE_TREFOIL_IS_THE_HALF_TURN_WITH_THE_THIRD_TURN.md).
Refs #73, #62.

**Grades:**
- **`proved-derived`:** exact computations in this session; the scripts are receipts, not formal
  checks.
- **`established-classical`:** statements with their sources, not formalized here.
- **`agent-inferred`:** the joins.

Brandon, September 27, asked to cement the egg and continue deriving it:
- "classify compression and generators as these eggs and most likely attain something like
  computational genetics about entropic flux diffusion patterns";
- a low-level code-length distribution that speaks for behaviour, compared with genetics;
- information theory and gauge theory;
- the chicken and the egg, the lens and the retina, light and shadow, "literally coupled";
- clouds and lightning leaders;
- learning as "a free-fall Plinko kind of thing … divergence … of wavelengths and
  classifications";
- deciphering a dead language from distributions, where failing configurations "will literally
  die";
- the faces of integers and floats, multiplication tables, primes by their digits, binary and
  hexadecimal, π and `e`;
- zeta zeros as faces causally attained, with `½ = 2^{e^{iπ}}`.

## 1. The egg is the unit object, and its genome is its description

`agent-inferred`, over existing owners:
- **An egg** is a generator:
  - a navigator family with its keys (the genome's content);
  - a constitution (its material, convex or concave by the frame of its flux);
  - the receiver family that reads its faces.

  Its **genome** is its self-delimiting description: declaration, keys and material, of length
  `ℓ` bits. Its **phenotype** is the faces it emits.
- **Two eggs are one species** when every admitted receiver reads the same faces from both. That
  is the kernel of the face map taken over generators (`compression::FaceMap` on the generator
  family), and the species is its quotient.
- **Classifying compression and generators as eggs** is exactly this quotient. Its prior is Kraft's
  `2^{−ℓ}`: the low-level code-length distribution over genomes, which speaks for every later
  behaviour because every later face is a genome's phenotype.
- **The genetic comparison** (`established-classical` for the biology):
  - a genome is a compressed generator, and development is its expression in a medium;
  - selection weighs phenotypes by their success;
  - no selection acts on the sequence directly.

  The library already holds the formal side, `Foundation/CausalRelevance` and the retention
  quotient. The protein, DNA and RNA scope stays as `docs/FORMAL_FRAMEWORK.md` bounds it.

## 2. Selection is Bayes, and Bayes is the replicator

`established-classical`: Harper, "The replicator equation as an inference dynamic", 2009; Shalizi,
*Electron. J. Statist.* 3, 2009. With weights `w_i` over eggs and the likelihood `L_i` of the event
just received, Bayes' rule is

```text
w_i′ = w_i L_i / Σ_j w_j L_j
```

That is the discrete replicator equation with fitness `L_i`. `agent-inferred`:
- **The receiving tree is a population under selection.** It is the mixture over pruned trees
  (candidate standings) with the stop prior as the birth distribution
  (`Compression/Landmark/Context/Standing.mixture_over_leaf_standings`). Its dominance bound
  `−log₂ W ≤ ℓ_S − log₂ L_S` (`Tree.own_kraft_and_dominance`) says the population never codes
  worse than its fittest genome plus that genome's length.
- **Failing configurations die.** A configuration that predicts worse loses weight geometrically
  in its likelihood ratio.
- **The terrain showed it** (the audit record's §6.1). The tree's population converged on the
  source's minimal tree. That was the only species that "physically works" for that source; the
  drawn spelling with two equal leaves was one genome of it.

## 3. Learning is Plinko: a digit descent through biased pegs

`agent-inferred`, exact in the owner:
- **The descent.** A cell is emitted as its odometer digits, and each digit is split at a node of
  its digit tree by that node's face (`Tree.digit_emission_normalized`). So a cell's emission is a
  ball falling through a Galton board: each peg is a node, each bounce is a digit, and the landing
  bin is the cell.
- **Learning biases the pegs.** Deposition moves each peg's counts toward what fell through it.
- **The sorting is the dyadic partition.** Each digit halves the interval of cells, so each level is
  a finer band: Brandon's "divergence of wavelengths and classifications".
- **Free fall.** The ball's path is fixed by the pegs it meets. Nothing chooses; a peg's bias is
  the only material the fall reads.
- **Generation is the same board run forward.** The requested face is packed into the keys, and the
  fall emits it (egg packing, §6).

## 4. Decipherment is loop closure up to gauge

- **Linear B** (`established-classical`; Chadwick, *The Decipherment of Linear B*, 1958). Alice
  Kober's inflectional "triplets" found the grid of shared consonants and vowels from distributions
  alone, before any sound was known. Ventris's grid then locked when a few place names anchored
  it. The causal basins were found first, and the anchor fixed the labels.
- **The join** (`agent-inferred`):
  - A dead language is a source whose receivers (meanings) are unknown.
  - Its distribution fixes its causal states: the retention quotient, histories that predict alike
    (Crutchfield and Young, 1989, already joined in the September 26 record).
  - A translation is a map between two sources' causal-state structures that closes every loop of
    contexts. That is the Bombe's loop closure over the menu (`hnn::keys`).
  - It is fixed exactly up to the structure's automorphisms, the gauge. `HNN/Keys.gauge_fix_unique`
    is the key location's gauge fixing.
  - Occlusion, blur and noise widen the fibre. A candidate that fails in new contexts loses weight
    by §2 and dies.
- **Brandon's mental arithmetic.** He "anchors results around confirmed parts of the digits". That
  is the same gauge fixing: exact anchors (§7.2) fix the class, and the rest is filled inside its
  fibre.

## 5. Gauge and information

`agent-inferred`:
- **The code length is gauge-invariant; the keys are not.** Relabelling a source's symbols, turning
  a ring's phase or re-plugging a board changes no code length.
- So the face lives on the quotient by the gauge group, and the fibre over a face is a gauge orbit:
  the plural preimage fibre the notation already keeps.
- The gauge-invariant constraints are holonomies, the loop closures around declared circuits
  (`Transport/CellHolonomy`). Information theory with a gauge is the code on the quotient plus the
  holonomies that fix the orbit.
- The unresolved gauge is the part of the key that no admitted receiver can read, so no
  compression can recover it and no learning should try.

## 6. The chicken and the egg; light and shadow

- **Coupled partitions** (`proved-derived`, the rank–nullity ledger, `compression::FaceMap`'s
  `rank + dim ker = dim X`). A receiver's image (the light) and its kernel (the shadow) are one
  partition of the terrain. Neither precedes the other: each is the other's complement.
- **Coupled development.** Reception changes both participants, `I_C(|H_S⟩,|H_R⟩) =
  (|H'_S⟩,|H'_R⟩,f_R)`, so source and receiver develop together.
  - `established-classical`: the vertebrate lens and retina develop by reciprocal induction. The
    optic vesicle induces the lens placode, and the lens in turn shapes the optic cup (Spemann,
    1901, and its modern reviews).
- **Two predictions of one partition.** Predicting light predicts where the transported current
  goes and how bright it is: the face. Predicting shadow predicts where the paths cancel or are
  blocked: the kernel, the gaps and intersections.
- **Clouds.** Sun through clouds shows the complement of the vapor's cover. The shafts are the
  moiré of the gaps.
- **Lightning.**
  - `established-classical`: the dielectric breakdown model of Niemeyer, Pietronero and
    Wiesmann (1984) grows a stepped leader by branching with probability rising with the local
    field. A fractal channel explores until one branch connects.
  - Then the return stroke carries the current back up the connected channel.
  - `agent-inferred`: the leader is differentiation (divergent exploration, the Plinko fall), the
    connection is the lock, and the return stroke is integration by reflection. The current returns
    through the one path that closed.
  - Learning and egg packing are these two passes of one discharge.

## 7. The faces of integers are moirés of gratings

### 7.1 An integer is a digit vector, and multiplication is convolution with carry

`proved-derived`, computed exactly:
- `n = Σ d_i b^i`.
- The product's digit vector is the convolution of the factors' vectors (the Toeplitz matrix of
  one factor acting on the other), then the carry. Examples:
  - `7 · 3`: `[1,1,1] ∗ [1,1] = [1,2,2,1]`, which carries to `10101` in base 2;
  - `255 · 255`: `[F,F] ∗ [F,F] = [225,450,225]`, which carries to `FE01` in base 16.
- The square of the two-digit number whose digits are both `b − 1` reads `(b−1)(b−2)01` in every
  base: `9801`, `FE01`, `1001`. It is the polynomial identity
  `(x² − 1)² = (x − 1)x³ + (x − 2)x² + 0·x + 1` read at `x = b`.
- Without carry the product is linear: a carry-free polynomial product. The carry is the helix's
  winding, the odometer. An integer is a Holon's digit vector on a helix, as the library already
  treats it (`Aeon/Clock/CarryWord`).

### 7.2 Two exact faces, and the middle between them

- **The trailing face.** The last `k` digits, `n mod b^k`, form a ring homomorphism, exact for `+`
  and `×`.
- **The leading face.** The first digits are the mantissa, the logarithm's chart. It is
  multiplicative up to a carry fibre. This is the float's mantissa, and the HNN's grain reading
  `carry + phase/L + ε` is this face.
- **The middle digits** are where the two faces' fibres meet, through the convolution's carries.

`agent-inferred`: mental arithmetic anchors both exact faces and fills the middle. That is
Brandon's "fuck with the digits in my head and shortcut answers", and why it "is still doing math
but feels different": it reads two receivers and solves the fibre between them.

### 7.3 Primes by their digits: cheap faces and gratings

`proved-derived`:
- **Cheap faces.** In base `b` three faces are free:
  - the last digit reads the primes dividing `b`;
  - the digit sum reads the primes dividing `b − 1`;
  - the alternating digit sum reads the primes dividing `b + 1`.

  | base | last digit | digit sum | alternating sum |
  |---|---|---|---|
  | 2 | 2 | — | 3 |
  | 6 | 2, 3 | 5 | 7 |
  | 10 | 2, 5 | 3 | 11 |
  | 16 | 2 | 3, 5 | 17 |
  | 30 | 2, 3, 5 | 29 | 31 |

  Base 6 is the first whose last digit reads both 2 and 3: the hexagon's two-three carrier again.
  Base 16 reads 3, 5 and 17 for free.
- **Every other prime is a grating.** For `n = b^m k + r`, `p | n` exactly when
  `k ≡ −r·b^{−m} mod p`: a grating of period `p` on the leading index `k`.
- **Brandon's "…17".** In `n = 100k + 17`:
  - 3 covers `k ≡ 1 mod 3`, giving 117, 417, 717, 1017, …;
  - 7 covers `k ≡ 2 mod 7`, giving 217, 917, 1617;
  - 11 covers `k ≡ 5 mod 11`, giving 517, 1617, 2717;
  - 13 covers `k ≡ 1 mod 13`, giving 117, 1417;
  - 19 covers `k ≡ 8 mod 19`, giving 817.

  His groups {117, 217}, {417, 517} and {717, 817, 917} are these gratings overlapping. The primes
  17, 317, 617, 1117, 1217, 2017, 2417, 2617 and 2917 are the gaps.
- **Why the intuition works and then fails.** The intuition reads the trailing face ("ends in 17":
  prime to 2 and 5). The gratings then decide on the leading index. The gaps thin as more gratings
  overlap, like `∏(1 − 1/p)` (Mertens): Brandon's "groups … growing in set size".
- This is the laboratory's sieve as moiré (`holobrochos/holo/src/found.rs`), read on the digit
  positions.

### 7.4 Bases chain from 2

`proved-derived`:
- A base `2^j` groups bits: hexadecimal is 4-bit words, and its trailing faces nest,
  `mod 2 ⊂ mod 4 ⊂ mod 8 ⊂ mod 16`.
- A base's cheap primes come from `b` and `b ± 1`, so moving between bases moves which gratings are
  cheap.

`agent-inferred`: a machine can choose the base whose cheap faces are the gratings it needs. That
is a computational optimization, as Brandon suspects, not a change of the law.

### 7.5 Transcendentals are generators, not digit strings

`proved-derived` from exact rational partial sums, and classical:
- **π's hexadecimal digits are addressable one by one** by the Bailey–Borwein–Plouffe generator,
  `π = Σ_k 16^{−k}(4/(8k+1) − 2/(8k+4) − 1/(8k+5) − 1/(8k+6))` (Bailey, Borwein and Plouffe,
  *Math. Comp.* 66, 1997). The exact partial sums give `3.243F6A8885`. Base 16, and so base 2, is a
  native digit face of π; no base-10 digit generator is known.
- **`e`'s regular continued fraction is `[2; 1, 2, 1, 1, 4, 1, 1, 6, 1, 1, 8, …]`**: a period of
  three with a growing carry. It is its Stern–Brocot descent, a word of the modular group (egg
  packing §2), with a generator of a few symbols.

`agent-inferred`:
- A transcendental's identity is its generator: the navigator is its address. Its digits in a base
  are one receiver's faces of it.
- Compression finds the generator, not the digit statistics. π's decimal digits look like noise to
  a digit receiver while its generator is a line.
- The laboratory's `pi-series-01` kept the Gregory–Leibniz unfolding as exact pairs in two orders.
  It is the same object: one terminal pair, two paths.

### 7.6 Finite generators, specific faces

`agent-inferred`, with a classical base:
- There are finitely many generators below any description length (Kraft). So a family of faces
  admits finitely many short generators.
- A key, a translation or a solution squeezes into the few that reproduce every admitted face: the
  quotient of §1, with a gauge orbit (§5) as its fibre.
- A generator that cannot predict the same outcome is a different species of interior dynamics.
  This is the black-box reading of the horizon, and the Bombe.

## 8. The zeros as faces

`agent-inferred`, over existing owners:
- `½ = 2^{e^{iπ}} = 2^{−1}` is the fixed line of the half-turn Swing `s ↦ 1 − s`, which the
  completed zeta respects (`Zeta/Seam.completedRiemannZeta_swing_half`).
- A zero is a face attained by the prime currents. RH asks that every attained face lie on the
  Swing's fixed line.
- The surviving candidate law (the global prime-part sign) and its missing implication stay as the
  [zero-gas record](2026-09-26_THE_ZERO_GAS_IS_A_COMPLEX_BURGERS_FLOW_AND_RH_NEEDS_A_SOURCE_LAW_AT_TIME_ZERO.md)
  states them.

## 9. What it asks of the construction

- **The egg population.** Extend the receiving tree's mixture over standings to a mixture over
  eggs: tree sources, moiré gratings (the rings), rotor keys. Each egg is weighted by its
  prequential likelihood, which is the replicator of §2. The population is gauged on terrain whose
  true egg is known: it should select the moiré's gratings on the moiré and the tree on the tree
  source. This is the rings' measurement (egg packing §7), stated as selection.
- **The arithmetic terrain.** Products and primes in bases 2, 6, 10 and 16, emitted as digit
  vectors. The question is whether the population finds:
  - the trailing faces;
  - the leading faces with their carry fibre;
  - the gratings.

  This is the laboratory's prime-stream microscope, with its truth known.
- **Owed in #62** (Lean):
  - multiplication as the carry of the digit vectors' convolution at base `b`, joined to
    `Aeon/Clock/CarryWord`;
  - the grating law on digit positions, `p | b^m k + r ⇔ k ≡ −r b^{−m} mod p`;
  - the cheap faces of `b` and `b ± 1`;
  - Bayes' rule as the discrete replicator, joined to `Tree.own_kraft_and_dominance`.
