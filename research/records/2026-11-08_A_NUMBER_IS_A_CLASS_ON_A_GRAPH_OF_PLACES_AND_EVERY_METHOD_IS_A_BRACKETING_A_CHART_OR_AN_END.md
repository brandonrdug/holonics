# A number is a class on a graph of places, and every method is a bracketing, a chart or an end

Status (2026-11-08): derived from Brandon's November 8 lens, with the number owner's design and build
order handed to the design thread (§9, §10). Refs #76, #73, #410.

The lens, paraphrased (his words stay out of the repository):
- Bit, tensor and matrix operations are one operation, which reduces to topology: graphs with dynamic
  bit registers.
- The theory's numbers need a bitwise system of their own, apart from native integers of every size and
  used throughout the code, built deliberately rather than assembled piecemeal.
- Addition by XOR and shifted carries is one route among others that transistors realize, which is the
  question of parallelization and associativity.
- Number theory and cryptanalysis are reversibility, reconstruction and analysis (RH, Hodge, elliptic
  curves, fluids). Division points at Newton–Raphson inversion, modular inversion, Diophantine matrix
  equations and the Moore–Penrose pseudoinverse; mapping a target onto a basis operator looks like the
  sigmoid and the habits around negative or fractional exponents (roots, radicals).
- The methods differ but share fractal signatures, like a Doppler spectrogram, while the commutativity
  and associativity between the operations are obfuscated. Information in general is reverse engineered
  to reproduce its structures or to analogize their interior and origin.
- In a comment on the first version: the native types themselves, unsigned or signed, are bit registers
  whose sign is a state they occupy and whose digit face is cut into coordinated partitions; the same
  holds for how digits disperse with the radix and the operation, which is a calculus. The first
  version had treated native integers as foreign limbs; §2.4, the digit calculus in §4 and N8 answer it.

Receipts: [`number_graph.py`](2026-11-08_A_NUMBER_IS_A_CLASS_ON_A_GRAPH_OF_PLACES_AND_EVERY_METHOD_IS_A_BRACKETING_A_CHART_OR_AN_END_receipts/number_graph.py),
63 checks, all pass, about 6 s, stand-in Python on integers and Fractions (output in
[`number_graph_output.txt`](2026-11-08_A_NUMBER_IS_A_CLASS_ON_A_GRAPH_OF_PLACES_AND_EVERY_METHOD_IS_A_BRACKETING_A_CHART_OR_AN_END_receipts/number_graph_output.txt)).
Grades: [standard] a classical result, [checked] a receipt, [derived] derived here, [reading] an
interpretation, [design] a choice for the code.

**Joins.** The carry, its rings and the arithmetic contract were already in the repository; this
record joins them.
- The carry's class and its bit face `a + b = (a ⊕ b) + 2(a ∧ b)`: `face.carry-bockstein`, beside the
  carry cocycle `winding.carry-cocycle` (Lean `Geometry/PhaseCarry`), which is the associativity of
  §3's carry product.
- The producer and its consumer: `radix.digit-convolution` and `radix.carry-cascade-consumer` (Lean
  `Mathematics/RadixWindowReceiver`, `Mathematics/ArithmeticContract`): every producer is a carry-free
  combination followed by one carry cascade. §2 reads the cascade as the boundary of the place
  complex, and N4 (§9.2) keeps the carry-free combination as a held fibre form.
- The cheap rings: `radix.cheap-ring-path-collapse` closes the place graph after one place
  (`q | b − 1`) or with a half or quarter turn (`q | b + 1`, `b² + 1`); §2.2 closes it after `n` places
  with any weight, and with two closing edges.
- The carry's chain: `radix.carry-chain-eulerian` (generate, kill, propagate; base 2's AND and XOR).
- Coprime lanes: `radix.residue-address`, `winding.crt-diagonal` and the
  [branch-register record](2026-11-03_A_STORED_FACE_AND_ITS_NAVIGATOR_ARE_TWO_ENDS_OF_ONE_EXCHANGE_AND_A_WIDTH_IS_A_BRANCH_REGISTER.md)
  (a width is parts and lanes).
- Faces an operation keeps: the
  [association record](2026-10-23_ASSOCIATION_IS_EVALUATION_A_NUMBER_IS_A_WORD_OF_TURNING_DIGITS_AT_A_LEVEL_OF_THE_BASES_TOWER.md);
  §7 reads obfuscation as composing laws whose kept faces sit in different charts.
- Release with its residue: `release.carried-residue` (Lean `Foundation/CarriedRelease`), which N5
  makes the only narrowing. Newton as residual release: `analytic.residual-release`,
  `analytic.admitted-newton`; the bottom end: `tower.hensel-thread`; Diophantine systems:
  `linalg.smith-normal-form`, `linalg.lattice-cokernel`.
- Merges and heat: `standing.erasure-is-merge`, `floor.landauer-erasure`. Shears: `motion.iwasawa-sl2`.
- The precision law: the
  [precision record](2026-11-07_PRECISION_IS_A_COUNT_A_MACHINE_NUMBER_IS_A_GRAPH_AT_COUNTED_WIDTHS_AND_THE_CARD_IS_A_SURFACE_OF_THREAD_POTENTIALS.md).

What is new here: the integers as the zeroth homology of the place complex with the modulus as its
closing edge, and every native type as a register whose type is its cuts, closing, section and
field charts (§2); every adder as a bracketing of one associative product, and the limb lookahead
`((g | p) + g) ⊕ p` (§3); the digit face's calculus and radix-dependent dispersal (§4); inversion as one map at either end with the target width's halvings as its
schedule (§5); each operation's merge cost (§6); the distributivity boundary of mixed rings (§7); the
number owner's laws, types, card realization, lint and build order (§9, §10). The new rows are
`radix.place-complex`, `radix.closing-edge`, `radix.register-presets`, `radix.digit-face-calculus`, `radix.adder-bracketing`, `radix.redundant-fibre`,
`radix.product-decomposition`, `arith.inversion-two-ends`, `arith.shear-merge-cost` and
`arith.mixed-ring-boundary`.

## 0. The answer

1. **A number is a class on a graph of places.** Places are joined by carry edges weighted by the radix.
   Two digit strings name the same number exactly when they differ by a boundary: `d − c = (2 − x)·t`,
   where `t` is the carry vector. The integers are the zeroth homology of `Z[x] --(2−x)--> Z[x]`
   [checked A1].
2. **Bitwise operations are that graph with its carry edges cut** (XOR is addition on `(Z/2)^n`, the
   cokernel of `2I`); placewise AND is the entrywise product; shifts, rotations and NOT are the graph's
   own maps. Integer addition, multiplication and matrix products are contractions with the edges
   switched on. **The modulus is the graph's closing edge**: an open path gives `Z/2^n`, a ring
   `Z/(2^n − 1)`, a Möbius ring `Z/(2^n + 1)`, a closing weight `c` gives `Z/(2^n − c)`, two closing
   edges give `Z/(2^n − 2^m − 1)` [checked B1, Smith normal form].
3. **Every way of computing one result is a bracketing, a decomposition or an end.** All adders are
   bracketings of one associative product (ripple, Kogge–Stone, Sklansky, Brent–Kung and random trees
   give the same carries [C1]); fast multipliers are decompositions of one tensor (Karatsuba 3^k leaves,
   Strassen 7^k [E2]); inversion converges from the top end of the place graph (Newton) or the bottom
   end (Hensel), by one map `x ↦ x(2 − ax)` whose residual squares [F1, F2]. The result is
   method-invariant. The method leaves a **signature**: depth, work, similarity dimension, convergence
   order, toggles.
4. **The reversible primitive is the shear** `(x, y) ↦ (x, y + f(x))`, invertible for any `f`, rounded or
   not. Addition is a shear, the quarter-turn is three shears, Euclid is a word of shears [G1, F6]. The
   only irreversible event is a **merge**, and its least cost is the log of its fibre (Landauer's
   `kT ln 2` per bit) [G3].
5. **Obfuscation is composing laws that are additive in incompatible charts.** Analysis (cryptanalysis,
   compression, learning) is finding the chart and bracketing in which the composite factors, plus the
   key. IDEA's addition and multiplication agree on distributivity on every triple where no carry reaches
   a closing edge and on none where one does [B4].
6. **So every number in the code must carry** its places, its carry edges (cut at its field boundaries),
   its closing edge, its section (which representative of each class it reads), its width as a need, its
   fibre form and its releases. Native types already are such registers, with those choices fixed and
   unnamed: `u64` and `i64` are one ring with two sections, lanes and bitfields are cut carry edges, a
   float's fields are three charts [L1–L4]. So the owner holds them as presets of one register, never as
   foreign limbs. §9 is the design, §10 the build order with parity at each step.

## 1. The four sources

All four links are on the thermodynamics of computation.
- **Cambridge SoC D/M power pack** (Landauer limit and reversible computation): wire capacitance
  dominates switching energy; computers run about six orders of magnitude above the Landauer limit;
  adiabatic logic returns charge to the supply; Toffoli logic goes below the limit; encryption and
  lossless compression are reversible at large scale, and the method is to avoid deleting intermediate
  results.
- **arXiv 2506.10876** (Chattopadhyay, Misra, Pandit, Paul; a review): `k_B T ln 2 ≈ 0.018 eV` per bit
  erased at room temperature; Reeb and Wolf's equality `βΔQ = ΔS + I(S′:R′) + D(ρ_R′‖ρ_R) ≥ ΔS`;
  finite-time erasure costs more; correlations with a kept memory lower the cost. The reading reached only
  its §III.1.
- **Bennett 1982**: the linked PDF is a scan with no text layer, so this record works from the paper:
  logically reversible computation keeps its history and uncomputes it; Brownian and ballistic
  computers; dissipation per step falls with the driving force (slower costs less); Maxwell's demon pays
  when it erases its record.
- **MacLennan, LNUC II.B**: the server's robots rule refused the fetch, so this record works from the course's
  published content: conservative logic (the Fredkin gate conserves the count of ones), the
  billiard-ball model, Toffoli universality, ancillae and garbage.

What they give the theory: the merge is the only necessary cost (§6); the cost falls when the merged
bits stay correlated with a kept memory (a key); and moving bits on wires dominates energy, so storing
and moving a width's need rather than a doubled word is an energy law as well as a memory law
[inferred].

## 2. The graph of places

**2.1 The complex.** Places `k` (from a lowest place `lo`, the grain `2^lo`). Chains `C₀ = Z[places]`
(digit vectors) and `C₁ = Z[carry edges]`; the boundary of the edge `k → k+1` is `2e_k − e_(k+1)`. A
value is a class in `H₀ = C₀/∂C₁ ≅ Z` (evaluation at `x = 2`). Adding chains is placewise: free,
commutative, associative and fully parallel, and it yields raw place sums. Normalizing to canonical
digits (one representative per class) is solving for the boundary `t` with `d − c = (2 − x)t`
[checked A1, 2,000 raw vectors]. `a + b = (a ⊕ b) + 2(a ∧ b)` is one boundary step (the AND moves up a
place); the XOR-and-shift loop repeats it and stops after `1 +` the longest carry chain, a chain being a
generate followed by propagates [checked A2, mean 6.31 iterations on 64-bit pairs].

**2.2 The closing edge is the modulus** [checked B1, Smith normal form, `n = 2..10`].

| Graph | Closing relation | Values | Where it lives |
|---|---|---|---|
| no carry edges | `2e_k = 0` | `(Z/2)^n` | XOR, `F₂` linear algebra, CRC, LFSR |
| open ray | none | `Z` | the integer, which widens |
| path of `n` places | top carry released | `Z/2^n` | wrapping words, two's complement |
| ring | `2e_(n−1) = e₀` | `Z/(2^n − 1)` | ones' complement, Mersenne (the repo's `2^61 − 1` fold) |
| Möbius ring | `2e_(n−1) = −e₀` | `Z/(2^n + 1)` | Fermat, Schönhage–Strassen, IDEA's multiply |
| closing weight `c` | `2e_(n−1) = c·e₀` | `Z/(2^n − c)` | pseudo-Mersenne, `2^255 − 19` |
| two closing edges | `2e_(n−1) = e₀ + e_m` | `Z/(2^n − 2^m − 1)` | Solinas, Goldilocks `2^448 − 2^224 − 1` |

A modulus is the holonomy of the radix connection around the closing circuit: once round multiplies by
`2^n`, and the closing edge says what that equals (`1`, `−1`, `c`) [derived]. Multiplying by the radix
is a graph map: on the path a shift that releases its top place, on the ring a rotation, on the Möbius
ring a rotation with the wrapped bits' sign flipped [checked B3]. That is why the Fermat ring turns an
FFT's twiddles into shifts: `2` is a 32nd root of unity mod `2^16 + 1` [checked E4]. Two rings are
coprime exactly when their lengths are, `gcd(2^a − 1, 2^b − 1) = 2^gcd(a,b) − 1` [checked K1], so
residues on rings of coprime lengths add and multiply lane by lane with no carry between lanes, and
the mixed-radix (CRT) reconstruction is the only carry between them [checked K2, rings of 19, 31 and 61
places]. This is the solenoid lens (independent circles close at their LCM) as arithmetic.

**2.3 The adder is a tensor network.** Each place's carry rule is a 2×2 transfer matrix on the carry
state (`c_in → maj(a_k, b_k, c_in)`). An open path contracts them in a row (a matrix product of bond
width one bit); a ring takes the trace. The trace is 1 for every pair except the `2^n` pairs with
`a + b = 2^n − 1`, where it is 2: ones' complement's two zeros are the two fixed points of the ring's
transfer product [checked B2, exhaustive at `n = 8`]. A product's network has a bond as wide as the bits
of the count of terms meeting in a column (the 11-05 width law appears as a bond width) [checked E1,
64-bit products: largest column 31, largest carry 28, 5 bits].

So bitwise, tensor and matrix operations are one picture: tensors on the place graph contracted along
carry bonds. The bond is the carry, its width is the need, the network's closing edge is the modulus,
and the contraction order is the method.

**2.4 A data type is a register, and the type is its choices** [checked L1–L4]. Every native type is
the place graph with four choices fixed: which carry edges are cut, where it closes, which section of
each class it reads, and the chart each field is read in.
- `u64` and `i64` are one ring, `Z/2^64`, with two sections, `[0, 2^64)` and `[−2^63, 2^63)`. The sign
  is not a parameter beside the digits: it occupies the top place with weight `−2^63`, which is the
  2-adic tail of ones (`…1111 = −1`) summed into one place, `2^63 + 2^64 + … ≡ −2^63`. So wrapping
  sums, differences and products are the same bits under either reading, the two orders differ exactly
  when the top places differ, and sign extension writes the tail back out [L1, 20,000 pairs].
- Ones' complement is the ring `Z/(2^n − 1)`: its end-around carry is the closing edge and its two zeros
  are the ring's two consistent carries (B2); its sign is still a place. Sign and magnitude holds the
  sign as a separate half-turn state beside the digits, so it too has two zeros: 255 values in 8 places
  against two's complement's 256 [L2, exhaustive].
- Lanes and bitfields are one register with carry edges cut at the field boundaries. A single native
  add realizes any partition: mask each field's top place, add, and restore the top places by XOR,
  `((x ∧ ¬H) + (y ∧ ¬H)) ⊕ ((x ⊕ y) ∧ H)` with `H` the fields' top places. With every edge cut it is
  XOR; with none, the 64-place add [L3, 2,000 random partitions]. XOR, packed lanes and the integer add
  are one formula with different `H`: the data type is the cut pattern.
- A float partitions its register into three fields read in three charts: a half-turn (the sign), a
  level (the exponent, the winding) and a phase (the mantissa), `(−1)^s 2^(e−127)(1 + m/2^23)`. That is
  the helix chart `log₂|x| = k + θ` laid out in bits [L4, against the platform's binary32]. The carry
  edge between the phase and the level is kept, so the bits read as one integer are `log₂` at a grain
  (within 0.0861), and adding two floats' bit patterns as integers multiplies their values (Mitchell
  1962: the mantissa's carry into the exponent is the helix's winding carry; within 8/9 of the product)
  [L4]. The inverse square root trick, `K − I/2` on the bit pattern, is the same chart [standard].

The coordinated partitions along the digit face are the type: a field boundary is a cut or a kept carry
edge, a section is a choice of representative, and a field's chart is how its places are read. A type
system for the theory names those choices instead of inheriting them unnamed from the hardware
[derived]. Floats stay out of the machine's storage; the float layout is a register reading at the
exterior boundary only.

## 3. Addition: one associative product, many bracketings

**3.1 The carry monoid.** Place `k` acts on the incoming carry by `c ↦ g_k ∨ (p_k ∧ c)` (generate
`g = a ∧ b`, propagate `p = a ⊕ b`): the Boolean matrix `[[p, g], [0, 1]]` on `(c, 1)`. Composition is
associative, so the carries are prefix products and every adder is a bracketing [checked C1, 64 bits]:

| Bracketing | Depth | Products |
|---|---|---|
| ripple | 63 | 63 |
| Kogge–Stone | 6 | 321 |
| Sklansky | 6 | 192 |
| Brent–Kung | 10 | 120 |
| random trees | varies | same carries |

Associativity, not commutativity, is what licenses parallel addition.

**3.2 Self-similarity.** The carry between limbs is itself one addition: with limb generate mask `g` and
propagate mask `p`, the carry into every limb is `((g | p) + g) ⊕ p` [checked C2, all `3^8` patterns; a
256-bit sum from 8 limbs in parallel plus one 9-bit addition]. On the card: 32 lanes each hold a limb,
a ballot gives `g` and `p`, and one 32-bit addition gives all 32 carries. The adder is the same
operation one scale up.

**3.3 Signatures.** The same sum leaves different traces.
- Settling: a ripple adder's carry front moves one place per gate delay; random 32-bit additions settle
  in 4.61 steps on average (largest 18), with 1.95 wire toggles per necessary change, the excess being
  glitches [reading C3, unit-delay model]. A prefix network's front moves `2^l` places at level `l`.
- Charts of a count: a binary counter toggles `2^(n+1) − 2` bits per cycle, a Gray counter `2^n`: the
  same count with half the switching [checked C3]. Dynamic energy is toggles × capacitance × V², so a
  count's chart shows in its power.
- A signature identifies the method's class without the data, and the data's carry runs modulate it.
  That is the lens's Doppler spectrogram: a time–place picture whose lines are carry fronts moving at
  the method's velocity [reading].

**3.4 Plural fibres buy locality.** A redundant digit set keeps several strings per number and pays
nothing in propagation. With signed digits `{−1, 0, 1}`, each output digit depends only on input places
`k, k−1, k−2` (perturbing every lower place never moves it), while a canonical binary carry can cross
all 64 places [checked D1]. Carry-save keeps two numbers for three in constant depth, and a column of
height 64 reduces to 2 in 10 stages [checked D2]. The non-adjacent form is the canonical section of the
signed-digit fibre with the fewest nonzero digits (0.369 per place below `2^16`, tending to 1/3, against
binary's 1/2) [checked D3]. **Law [derived]: locality is bought by keeping the fibre plural; every
collapse to canonical digits is paid in propagation where it happens.**

## 4. Multiplication and the matrix product: contraction, then boundary

- An integer product is the digit convolution (the tensor `T[i+j=k]`) followed by the carries
  [checked E1]; a matrix product is the contraction of the tensor `⟨n,n,n⟩`.
- Fast methods are decompositions of the tensor: Karatsuba (3 products for 4) has `3^k` leaves on `2^k`
  places, Strassen (7 for 8) has `7^k` [checked E2]; Toom evaluates at `2k−1` points; the FFT evaluates
  at roots of unity, which diagonalizes the ring's shift. **A method's exponent is the similarity
  dimension of its recursion** (`log₂3 = 1.585`, `log₂7 = 2.807`), and two methods with one exponent
  are one class [derived]: the fractal in the signature.
- The same dimension sits in the carries: pairs with no carry in `m + n` form the Sierpinski gasket,
  `3^k` of them below `2^k` (dimension `log₂3`), and `6^k` in base 3 [checked E3].
- **Carries are p-adic valuations.** Kummer: the carries of `m + n` in base `p` count
  `v_p(binom(m+n, m))` [checked E3, `p = 2, 3`]. Legendre: `v_p(N!) = (N − s_p(N))/(p − 1)`, all the
  carries of counting to `N` [checked]. Here the place graph meets number theory.
- **The digit face has a calculus** [checked M1–M3]. An increment moves the digit sum by
  `s_b(n+1) − s_b(n) = 1 − (b − 1)·v_b(n+1)` in every radix: the derivative of the digit face is 1, less
  `b − 1` per carry, so the carry run is the derivative's defect [M1]. Summing the increments is its
  integral: `Σ_(k≤N) v_b(k) = (N − s_b(N))/(b − 1)`, the carries of counting to `N`, which at a prime
  radix is `v_p(N!)` (Legendre) and at a composite radix is not [M2]. At a prime radix the difference
  calculus's basis `C(n, k)` factors place by place (Lucas, `C(n, k) ≡ ∏ C(n_i, k_i) mod p`; it fails at
  radices 4, 6 and 10), its valuations count carries (Kummer), and every continuous `p`-adic function
  is a series `Σ a_k C(x, k)` with `a_k → 0` (Mahler), as `(1 + p)^x = Σ C(x, k) p^k` [M3]. The
  finite-difference calculus and the place graph are compatible place by place exactly at prime
  radices [derived].
- **How digits disperse depends on the radix and the operation** [checked M4]. Under multiplication
  the leading digits move as the phase `θ = {k log_b m}` on the log chart's circle. The leading digit of
  `2^k` cycles 1, 2, 4, 8 in base 16, where `log₁₆ 2 = 1/4` closes the phase, and spreads by Benford's
  `log₁₀(1 + 1/d)` in base 10, where `log₁₀ 2` is irrational and the phase fills its circle (within 1% at
  `k < 3000`). The trailing digits move on the residue rings, periodically, and the carries between
  them relax by `1/b` a place (`radix.carry-chain-eulerian`). The leading digits of `m^k` cycle exactly
  when `m` and `b` are powers of one integer, and otherwise fill the circle (Weyl) [standard]:
  dispersal is commensurability.

## 5. Inversion: one map, two ends, many completions

**5.1 The map.** `X ↦ X(2 − AX)` with residual `E = 1 − AX` satisfies `E′ = E²` identically in any ring
[checked F2, F4]. The completion (the sense in which `E` is small) decides which digits come right first.
- **Top end** (the lattice `2^−L`): top digits first. Released to the lattice at each step,
  `e′ = e² − a·r`, with the release remainder `r` accounted [checked F2].
- **Bottom end** (modulus `2^n`, 2-adic): low digits first. From `x = a` the correct low bits run 3, 6,
  12, 24, 48, 64 on every sampled odd 64-bit `a`; `(3a) ⊕ 2` starts at 5 [checked F1].
- **Matrices**: Newton–Schulz (the repo's `hnn::chart` owner).
- **Rank-deficient**: the same map from `X₀ = Aᵀ/(‖A‖₁‖A‖∞)` converges to the Moore–Penrose
  pseudoinverse while the null direction stays zero at every step, identically: a silent mode [checked
  F5, error `2^−2.8 → 2^−436` in 10 steps].
- Division `a/b = a·(1/b)` works from either end. Barrett reduction is division from the top with a
  Newton reciprocal; Montgomery reduction is division from the bottom (it cancels low places): one
  identity, two ends [standard].

**5.2 The width schedule is the target width's binary expansion.** To reach width `w`, Newton works at
`⌈w/2^k⌉ = ((w − 1) >> k) + 1`, read from the top: `w = 11` runs 1, 2, 3, 6, 11; `w = 100` runs 1, 2, 4,
7, 13, 25, 50, 100 [checked F3]. Each step works at the width it needs, never the final one, and the cost
is a geometric series dominated by its last step. **This is the 11-05 register law (a width kept as its
own binary expansion, read by place) as the schedule of inversion** [derived].

**5.3 Modular inversion and Diophantine systems are the discrete form.** Euclid on `(m, a)` is a word in
`SL(2, Z)`: each step `[[q,1],[1,0]]` is the shear `[[1,q],[0,1]]` times a swap, the product has
determinant `±1`, and its convergent gives `a⁻¹ mod m` [checked F6, 37.6 steps on 64-bit moduli against
Heilbronn's 37.1]. For matrices, the same shears bring `A` to Smith normal form, whose invariant factors
are the cokernel (homology) of `AX = B`: they divide in a chain and multiply to `|det A|` [checked F6].
The modulus table of §2.2 is this computation on the place graph's own relations.

**5.4 "Mapping a target onto a basis operator" is choosing the chart where the operator is diagonal**
(becomes addition or scaling).
- The logarithm: in the repo's `log2_face`, squaring the mantissa in the value chart is a left shift in
  the log chart, and each squaring reads one binary digit of the logarithm, the digit being the carry out
  (mantissa ≥ 2) [read from `keyed_modes.rs`]. `Exponential` is the inverse register: `2^f` as the
  product of the roots `2^(2^−i)` its digits select.
- The logit: a sigmoid update multiplies the odds; `p ↦ kp/(kp + 1 − p)` is the Möbius map
  `[[k, 0], [k − 1, 1]]`, updates compose by product (a boost), and `tanh(x/2)` is the Cayley transform
  of the odds [checked F8]. `tanh` addition `(t₁ + t₂)/(1 + t₁t₂)` is the product of boost matrices
  [checked F8].
- Roots: `x^n = a` by the same family; the inverse square root's residual runs `e′ = ¾e² + ¼e³`, and
  Heron's error squares over `2x` [checked F7].
- Negative and fractional exponents: `a^t` is the one-parameter group, diagonal in `t = log a`;
  `e^(iπ) = −1` is the half-turn in the log chart with its winding branch.
- The Fourier chart diagonalizes the ring's shift; the valuation chart (prime exponent vectors, the
  repo's `ratio::places`) turns multiplication into addition; the discrete log does it mod `p`; the
  elliptic logarithm does it on a curve.

Over the reals these charts are cheap at a declared width. Over `Z` and `F_p`, entering them is the hard
problem itself: the valuation chart is factoring, the discrete-log chart is the DLP, the elliptic log
over `F_p` is ECDLP [standard]. **Cryptography lives exactly where the diagonalizing chart exists but is
expensive to enter** [derived]; when the chart is cheap (anomalous curves, where the formal group's
p-adic logarithm is computable: Smart's attack) the system falls [standard].

**5.5 Convergence order is the other line of a method's spectrogram.** Long division and CORDIC add a
digit per step; Newton doubles (slope 1 on `log₂` width per step); Halley triples. Order and similarity
dimension are the two numbers a method's spectrogram shows [reading].

## 6. Reversibility, merges and heat

- Shears invert for any `f`, rounded or not: the integer lifting step and Feistel rounds with a
  non-invertible round function invert to the last bit, and the quarter-turn `[[0,−1],[1,0]]` is three
  integer shears [checked G1].
- A reversible adder computes and uncomputes every carry in place: `(a, b) ↦ (a, a + b)`, the ancilla
  returns to 0, and only the top carry (the winding) is written out; 129 CNOT and 64 Toffoli gates at
  32 bits [checked G2, exhaustive at 5 bits].
- **Landauer cost of an operation is `log₂` of its fibre.** On two uniform 8-bit inputs: `a + b` merges
  7.28 bits, `a·b` 2.29, `a ⊕ b` 8.00, collapsing a carry-save pair 6.64, the in-place add 0
  [checked G3].
- Addition's fibre is large but a line (`b = s − a`); multiplication's fibre is small but navigable only
  in the valuation chart. **Landauer prices a fibre's size; cryptanalysis prices its navigability**
  [derived].

The Holonics reading [derived]: a carried remainder keeps a step reversible, and a release at a declared
tolerance is the one merge, which should be the only place the machine's arithmetic loses bits. Rust's
`wrapping_add` is an undeclared release of the winding; checked arithmetic refuses; the integer widens.
Reeb and Wolf's mutual-information term is the key: merged bits that stay correlated with a kept memory
cost less, and Bennett's uncomputation is the limit where the memory holds a full copy. The adjoint of a
step built from shears needs no tape: run the inverse shears (the "adjoint without tape" law, in
arithmetic).

## 7. Obfuscation and analysis

- **The carry is the only nonlinearity of addition over `F₂`.** Sum bit `k` has algebraic degree `k+1`,
  and its best linear approximation has correlation 1 at `k = 0` and 1/2 above [checked H2]. Its cone is
  one-way: an input bit reaches only its own and higher places [checked H1]. Rotation closes the cone
  into a ring: in a 16-bit ARX toy every output bit depends on every input bit after 9 rounds (rotation 3)
  or 5 (rotation 7), and never without rotation [checked H1].
- **IDEA mixes three closing edges on the same 16 places**: XOR (no edges), add mod `2^16` (path),
  multiply mod `2^16 + 1` (Möbius ring). Distributivity holds on all 4,905 of 20,000 triples where no
  carry reaches a closing edge and on none of the 15,095 where one does [checked B4]. Each law is
  associative and commutative alone; between them only the boundary differs. Linear cryptanalysis seeks a
  Walsh character the composite nearly keeps, differential cryptanalysis a difference group it nearly
  keeps, algebraic attacks low degree: each is a search for a chart in which the composite is nearly
  additive [standard].
- **Side channels read signatures.** Square-and-multiply (double-and-add on a curve) runs the scalar's
  binary register, so a power or timing trace shows the key's bits (Kocher's timing attack, simple power
  analysis) [standard]. The non-adjacent form needs fewer additions (21.8 against 32.4 per 64-bit scalar
  [checked J1]); a Montgomery ladder makes the signature uniform. The method's spectrogram carries the
  data's register.
- **Reconstruction is finding the register.** With no carry (over `F₂`), `2L` output bits give a
  register's closing edges (its feedback) by Berlekamp–Massey and regenerate everything after [checked
  H3, 40 registers]. With the carry (2-adic), `2 log₂q + 2` low bits give `p/q` by Euclid, and `−1/19`
  repeats with period `ord₁₉(2) = 18` [checked H4]. The smallest register that regenerates a stream is
  its description: compression. Learning is locating its graph, closing edges, chart and key (the
  Holonics law that learning is locating keys, in arithmetic) [derived]. Grokking modular addition is a
  learner finding the ring's Fourier chart: trained networks compute `a + b mod p` through cosines and
  sines of a few frequencies (Nanda et al. 2023) [standard].
- **At the least, the interior's class.** Behind a horizon the outside keeps the quotient: the conserved
  charges (no hair) and the entropy `A/4`, the log of the fibre over that quotient. Unitarity says the
  fibre coordinate is scrambled into the radiation, not merged; Hayden and Preskill say it decodes after
  the scrambling time only for whoever holds the earlier radiation, a key. Class without the key,
  interior with it [reading].

## 8. The crossings the lens names

- **RH.** The explicit formula makes the primes a sum of tones in `log x`: each zero `ρ = β + iγ`
  contributes `x^ρ/ρ`, a tone of frequency `γ` growing like `x^β`. RH says every tone grows at
  `β = 1/2`: the primes' spectrogram in the log chart has all its lines on one envelope [standard;
  the spectrogram reading is this record's]. Square-root cancellation of the Möbius function is the same
  statement. Mauduit and Rivat proved `μ` cancels against the carry parity `(−1)^(s₂(n))` (Thue–Morse):
  the primes do not see the carry; at `N = 10^6` the sum is 172 (0.172√N) beside Mertens' 212 [reading
  I2].
- **Elliptic curves.** Near the identity the group law is a formal group `F(X, Y) = X + Y + …`, a carry,
  and its formal logarithm makes it addition locally. The binary carry itself is `p = 2` Witt addition,
  `S₁ = a₁ + b₁ + a₀b₀ mod 2` (the AND); for `p = 3` the Teichmüller digits are `{0, 1, −1}`, so balanced
  ternary is the 3-adic Witt chart and its carries are the 3-typical Witt polynomials [checked I1].
  Scalar multiplication is the scalar's register, the non-adjacent form its signed section [checked J1].
- **Fluids.** The Navier–Stokes nonlinearity in Fourier space is the convolution tensor `T[p+q=k]`, the
  same tensor as integer multiplication before its carries. The energy cascade moves energy to higher
  wavenumber as a carry moves value to a higher place, and viscosity is the release at the bottom of the
  scales [reading]. In the dyadic shell model energy passes shell to shell as a carry flux,
  `u_n·du_n/dt = Π_n − Π_(n+1)`, with the total conserved [checked I3]. Tao's averaged Navier–Stokes
  blows up by sending energy through the shells faster each step: a carry that reaches infinite place in
  finite time [standard; the carry reading is this record's].
- **Hodge.** A question of sections: whether every rational class of type `(p, p)` has an algebraic
  interior (a rational combination of algebraic cycles). In the carry complex a section exists by
  construction (canonical digits); Hodge asks whether a boundary reading of a given kind always has an
  algebraic origin [reading, no claim].
- **The field** [reading]. Athena's rings are cyclic place graphs; their modes are the ring's Fourier
  chart, and locking is finding the chart in which the passage's shift is diagonal. The card's
  integer-associative realization (parity bit for bit because each term is released at a declared grain
  before summing) is §3.1's parity by construction already at work.

## 9. The number system's design

**9.1 What exists.**
- Design's inventory: i128 2,974; u128 1,291; i64 2,722; u64 5,982; i32 502; u32 2,845; BigInt 4,194;
  BigUint 1,156; BigRational 18 uses; concentrated in `hnn` (about 7,200 lines, 2,600 in `tower/field`),
  `holonics-cuda` (about 3,400) and `ratio` (570).
- Widths picked to fit a carrier: `keyed_modes::Grains` ("chosen so every product stays inside `i128`":
  P 30, L 32, S 30, X 24, m 8, Q 16), `UNIT_BITS 62`, `PUSH_BITS 2`, `SQUARE_BITS 8`, `LN2_BITS 30`;
  `tower`'s `FACE_BITS 16`, `MATERIAL_BITS 24`; the field's `SHARE_BITS 63`, `CONTACT_BITS 40`,
  `STATE_BITS 16`, `LN2_FACE_BITS 30`, `WEIGHT_BITS 62`, `LOCK_BACK_BITS = 2·FACE_BITS + 1`,
  `PACE_BITS`, `TEMPER_TOP 7`. The precision law calls a picked width arbitrary precision.
- Partial owners to build on: `ratio::{Rat, Presentation}` (the undivided pair); `ratio::linear`
  (inversion with its fibre, the fraction-free integral chart); `ratio::ring::{ExactRing, ModularWords,
  CheckedIntegers}` (the Mersenne 61 fold; refusal rather than wrapping); `ratio::places` (prime-valuation
  series); `ratio::exponentiated::CarriedPower`; `keyed_modes::{release, Exponential, log2_face,
  ln2_face}`; the field's `div_nearest`; `hnn::chart` (lattice charts, certified Newton–Schulz,
  `ceil_log2`); `hnn::word` (carried remainders, released). On the card: `exact_integer.cuh` (`Z/2^128`,
  carrier refusal), `hnn_inverse_exact.cuh` (runtime-width Newton–Schulz), `hnn_word_exact.cuh`,
  `field.cu`'s `Big<L>` limbs.
- Laws already proved that the owner realizes: `release.carried-residue` (Lean
  `Foundation/CarriedRelease`, a release that carries its residue conserves) for N5;
  `radix.carry-cascade-consumer` (Lean `Mathematics/ArithmeticContract`, a carry-free combination and
  then one cascade) for N4; `winding.carry-cocycle` (Lean `Geometry/PhaseCarry`) for §3's
  associativity; `linalg.lattice-cokernel` (Lean `Foundation/LatticeTransport`) for N6's Euclid end.
- What they lack together: one type that carries places, closing edge and width; `release(x, bits)`
  returns no remainder; widths are picked, not derived; wrapping, refusal and widening are scattered
  choices rather than a property of the value.

**9.2 The laws the owner enforces** [design].
- **N1 Places.** A value occupies places `[lo, lo + w)`: `lo` its grain `2^lo`, `w` its width. Both
  belong to the value.
- **N2 Closing.** Each value declares its closing edge: `Ray` (the integer, which widens), `Path`
  (a residue mod `2^w` whose winding is returned, never silently dropped), `Ring`, `Twist`,
  `Weighted(c)`, `Solinas(returns)`, and `Rings(coprime lengths)` (residues lane by lane, §2.2, the CRT
  as the one carry). No wrapping or saturating form exists inside; a `Path` overflow returns its winding.
- **N3 Width is a need.** Every operation derives its result's width from its operands: a sum, the
  wider plus one; a sum of `n`, the widest plus `⌈log₂ n⌉`; a product, `w_a + w_b` at grain
  `lo_a + lo_b`; a shift moves places. The only widths from outside are declared receivers' grains and
  the exterior boundary (a byte enters at width 8). A width is kept as its own binary expansion: an
  array of width-11 values stores and moves an 8-place plane, a 2-place plane and a 1-place plane,
  11 places a value, never a 16-bit word [design, from the 11-05 law].
- **N4 Fibre form.** A value is canonical (digits) or held redundant: an accumulation of place or limb
  sums with its term count, a carry-save pair, signed digits, or ring residues. Normalization (the
  carry) happens at a declared point, and any bracketing gives the same bits.
- **N5 Release.** The only narrowing. It names its rounding rule (floor, nearest with a tie rule,
  ceiling: each chooses a different Euclidean descent, ELEMENTARY_OBJECTS §9) and returns the remainder
  at the released places. Dropping a remainder is a second declared step: the merge.
- **N6 Inversion.** One map with its residual, at a declared end (`Top`: lattice reciprocal; `Bottom`:
  inverse mod `2^w`; `Euclid`: inverse mod `m` as a shear word; `Matrix`: Newton–Schulz; `Range`: the
  pseudoinverse on the range), scheduled by the target width's halvings, returning `(X, E)` with its
  certificate (`|E| < 2^−w` or `v₂(E) ≥ w`).
- **N7 Shears.** In-place updates `y ← y + f(x)` are the reversible primitive and carry their inverse,
  so an adjoint built from them needs no tape.
- **N8 Presets.** A native type is a register with its choices fixed, so it enters the owner as a named
  preset, never as a foreign limb: `u64` (64 places, no cut, a path, section `[0, 2^64)`), `i64` (the
  same ring, section `[−2^63, 2^63)`), packed lanes (cuts at the lane boundaries), bitfields (fields with
  their own sections). Moving between presets is a declared map: a section change, a sign extension
  (the tail written out), a cut or a join of carry edges, a release. Limbs are a preset's realization in
  machine words, inside the owner; outside it no primitive integer type carries a value of the theory,
  and storage addressing (`usize`) is not a number of the theory and never mixes with values. The float
  layout is a preset only at the exterior boundary, where foreign data arrives and is converted.
- **N9 Charts are receivers.** Log, odds, Fourier, valuation and discrete-log charts are navigators or
  receivers built on the owner, with their own grains, never inside it.

**9.3 Host types (Rust)** [design sketch; names in the objects' vocabulary are design's call].
```rust
// crates/holonics/src/number/  (the one owner)
pub struct Width { places: u32 }        // a count of places; registers at its set bits
pub struct Grain { lo: i32 }            // the lowest place, 2^lo
pub enum Closing { Ray, Path, Ring, Twist, Weighted(Coefficient), Solinas(&'static [Return]), Rings(&'static [u32]) }
pub enum Section { Low, TwosComplement, Balanced, SignMagnitude }  // which representative of each class
pub struct Cuts { places: Limbs }      // field boundaries where carry edges are cut (lanes, bitfields)
pub struct Register { width: Width, cuts: Cuts, closing: Closing, section: Section }  // a native type is one
pub struct Value<C: ClosingLaw> { grain: Grain, width: Width, section: Section, limbs: Limbs }  // canonical in its section
pub struct Accumulation { grain: Grain, terms: Count, sums: Limbs }           // before its boundary
pub struct Released<C> { value: Value<C>, remainder: Value<Ray>, rule: Rounding }
pub enum Rounding { Floor, Nearest(Tie), Ceiling }
pub struct Winding(Value<Ray>);         // what a Path returns when a carry leaves its top place
pub struct Inverse<C> { x: Value<C>, residual: Value<C>, end: End, certified: Width }
pub enum End { Top, Bottom, Euclid, Matrix, Range }
pub trait Shear { fn apply(&mut self); fn undo(&mut self); }
```
`Limbs` is a realization: inline words at small widths (it must cost no more than today's `i64`/`i128`
at the same width, measured), heap words beyond. `Rat` later moves onto `Value<Ray>`, replacing `BigInt`
where it is the integer of the theory.

**9.4 Card (CUDA)** [design sketch]. A header `number.cuh` with the same layout and laws. A value is
`V` lanes × `L` limbs of 32 bits, with `(V, L)` derived from the plan's width (the batch's longest bound,
as the width law's `C` was), instantiated for the widths the plan needs, refusing any other (the
existing carrier refusal). Per-thread operations for small `L`: add with its carry chain, Comba product,
release with remainder, Newton inverse. Lane-cooperative add for wide values: each lane its limb, a
ballot gives `g` and `p`, carries `((g | p) + g) ^ p` (receipt C2), one 32-bit addition for 32 limbs.
Values narrower than a word pack several to a word with carry edges cut at their boundaries (receipt
L3), so the width law's planes (11 places as 8 + 2 + 1) ride 32-bit words without a 16-bit carrier.
Accumulations stay as place sums until the declared normalization, which keeps the card's parity by
construction. Wide accumulations may also sit on coprime rings, one ring a lane, carry-free between
lanes, with the CRT at the release [inferred: measure before adopting].

**9.5 The lint** [design]. In `tools/gate.sh`: refuse primitive integer types (`i8`…`i128`,
`u8`…`u128`; `usize` only for addressing) in `crates/holonics/src/hnn/**` and
`crates/holonics-cuda/src/**` outside `number/` and declared exterior modules (codecs receiving
bytes), with an allowlist of unmigrated files that only shrinks; `compile_fail` doctests that `Value`
has no public `From<i128>`, no public limbs and no wrapping operation; for kernels, a check that `.cu`
and `.cuh` files outside `number.cuh` declare no `__int128` and no products of values in native words.

## 10. Build order: owner by owner, parity at each step [design]

Two kinds of step. A **realization step** keeps every release point and must reproduce bits
identically, host and card. A **width step** replaces a picked width by a derived one, so it moves
release points: it is a law change, judged by a paired read on the theory's measures, not by parity.

0. **Census** (read-only, no code change): every declared width and stored carrier with its consumer,
   its derivation from an operation or "picked to fit", and its measured need on the card over a run's
   opening (largest bits actually used) beside the word it occupies. One dated record with receipts.
1. **Host owner** `holonics::number`: N1–N8 types and operations, the native presets and the maps
   between them (section change, sign extension, cuts and joins); property tests bit for bit against
   native arithmetic inside native range (each preset against its native type, each cut pattern against
   lane-by-lane adds) and against `BigInt` beyond; cost measured against the code it replaces at the same
   widths. Lean obligations named in #410: the carry-complex identity, Kummer, Legendre and Lucas
   (Mathlib has them in digit form; confirm the names), the increment's digit-sum identity, the Newton
   residual square.
2. **Card header** `number.cuh`: host parity per operation on random inputs at the census widths,
   including the lane-cooperative add; the GPU suite on an idle card.
3. **First consumer** (realization): `keyed_modes::release` and the field's `div_nearest` become the
   owner's release, returning their remainders; identical bits on the unit tests and on one card read at
   a boundary.
4. **The field and the energy law**, module by module (realization), each with a paired read at a
   boundary (same sections, card, identical writes and reads); the lint's allowlist shrinks per module.
5. **Width steps**: `Grains`, `FACE_BITS`, `MATERIAL_BITS`, `SHARE_BITS` and the rest replaced one at a
   time by widths derived from operand widths and term counts (N3), each judged by its paired read.
6. `hnn::word`, `hnn::chart`, `ratio::linear` and `ratio::places` onto `Value`; `Rat` over `Value<Ray>`.
7. **The lint at full strength**: no primitive integer carries a value of the theory outside the owner.

Steps 0 and 1 can start at once and touch nothing in lap 14; step 3 is the smallest end-to-end proof.

## 11. Not claimed

- No new theorem about RH, Hodge, BSD or Navier–Stokes; §8 locates where carries meet those objects.
- The spectrogram, side-channel, field and black-hole statements are readings; the receipts check only
  the identities named.
- The ARX, IDEA and settling numbers are small toys.
- The design's cost (no slower than native words at the same width) is owed to step 1's measurement.
- The float layout is a register reading at the exterior boundary; nothing here puts floats in the
  machine's storage.
