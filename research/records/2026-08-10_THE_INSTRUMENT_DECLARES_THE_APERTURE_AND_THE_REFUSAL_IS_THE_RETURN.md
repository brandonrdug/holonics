# The instrument declares the aperture, and the refusal is the return

**Date:** 2026-08-10
**Truth status:** `proved-standard` for the classical theorems, each with its attribution and its
source caveat; `established-bounded` for every code measurement, each from a source read;
`interpretation` for the ladder, which is this project's and is stated so it can be refused.
**Provenance:** Brandon, 2026-08-10, naming the sources and the frame: *"Be holistic and utilize the
breadth in my thought patterns."* The parenthetical he attached to the neusis line —
*(biology, primes, cells, membrane transport, physical gates, crystals, lattices)* — is what this
record is organised around.

**Sources fetched 2026-08-10 and their state is part of the evidence.** Eight MathWorld pages and
two arXiv papers were retrieved in full. **One source was NOT retrieved** and nothing below rests on
it; see §6.

---

## 0 · The one sentence

> **An instrument is a declared receiver family. Its aperture is an index condition on a group. What
> the instrument cannot reach it must refuse by name, and adjoining a further instrument is
> purchasing a channel.**

That is `H.0420`'s *recovery adjoins a channel* and `CLAUDE.md` §2's *realization pays*, arriving
from a direction neither was derived in — Greek geometry — and landing on two organs this body
already runs.

---

## 1 · The ladder, and the two rungs the machine already implements without naming them

| instrument | what it reaches | aperture condition | owner here |
|---|---|---|---|
| rational chart | `ℚ` | degree 1 | `Rat` |
| **straightedge and compass** | towers of quadratic extensions | `[ℚ(α):ℚ] = 2ⁿ` | **`crates/holonic-engine/src/multiquadratic.rs`** |
| **neusis / marked ruler** | + cubics and quartics | 2,3-towers | **absent from both repositories** |
| **radicals** | solvable Galois group | wall at degree four | **`crates/holonic-engine/src/quintic_chart.rs`** |
| **periodic lattice** | rotations of order `n` | `n ∈ {1,2,3,4,6}` | **`crates/holonic-engine/src/winding_inertia.rs`** |

### 1.1 The compass rung is built and has never been named

`multiquadratic.rs` carries `ℚ(√k₁,…,√kₙ)` as `2ⁿ` rational coefficients indexed by subset, with
the module's own words at `:33` — *"That is the twisted group algebra of `(ℤ/2)ⁿ` over `ℚ`"* — and at
`:42-45`, *"the `2ⁿ` sign choices are the Galois group `(ℤ/2)ⁿ` acting on the field."*

**Degree `2ⁿ`, elementary abelian 2-group, one square root adjoined at a time.** That is the
construction field of straightedge and compass. Measured by a full sweep of both repositories on
2026-08-10: the strings `straightedge`, `compass` (in the instrument sense), `Wantzel`, `trisect`,
`constructible number` and `constructible polygon` return **zero files in the live tree and zero at
`a07ff376`**.

### 1.2 The radical rung is built, named, and driven

`quintic_chart.rs` with `QuinticTransitiveGroup::solvable_by_radicals()`, and
`examples/the_degree_is_a_rung.rs` whose first declared control is ***"the wall is at four and the
ladder crosses it"*** — twelve inputs at degrees two through seven, every input of degree ≤ 4
returning and at least one of degree ≥ 5 refusing, with the driver stating the configuration that
would make the control fail. `canon/TABLET_THE_CHART.md:184-194` already carries Abel–Ruffini and
Galois.

**The two rungs have never met.** `git grep` for each over `crates/holonic-engine/src/`: the only
file naming both is `lib.rs`.

### 1.3 The lattice rung is built and named after the wrong theorem

`winding_inertia.rs:62`:

> *"By Niven's theorem `2cos(2πm/n)` is rational exactly when `n/gcd(m,n) ∈ {1,2,3,4,6}`, with values
> `2, −2, −1, 0, 1`."*

**That set is the crystallographic restriction.** A rotation of order `n` preserving a lattice has an
integer matrix in a lattice basis, so its trace `2cos(2π/n)` is an **integer**, forcing
`2cos(2π/n) ∈ {2,1,0,−1,−2}` and `n ∈ {1,2,3,4,6}` — the same set with the same five values the
module lists. `proved-standard`. The word `crystallographic` occurs nowhere in the live tree outside
vendored mathlib.

**So the crystal that `2026-08-09_THE_COLOR_IS_A_RECEIVER_QUOTIENT_THE_CRYSTAL_IS_THE_COMPREHENSION…`
builds its whole reading on — *"a crystal is not a container light passes through, it is a receiver
that selects by phase"* — has its admissibility law already computed in a different module, under a
different name, cross-checked against an independent Sturm isolation.**

### 1.4 The demonstration — CORRECTED 2026-08-10 by the driver that tested it

| `n` | straightedge and compass | periodic lattice |
|---|---|---|
| 3, 4, 6 | admitted | admitted |
| **5** | **admitted** | **forbidden** |
| **7** | **forbidden** | **forbidden** |
| 17 | admitted | forbidden |

The pentagon is constructible and crystallographically impossible. **Two classical theorems disagree
about the same object, and both are right, because an aperture belongs to the instrument.**

**This section read *"neither aperture contains the other"* until
`examples/the_pentagon_divides_the_instruments.rs` was run and its control FAILED on the first
attempt.** The claim is false, and provably so: every crystallographic order has `φ(n) ∈ {1,2}`, a
power of two, so **the lattice aperture is contained in the compass aperture.** The pentagon
witnesses that the containment is *strict*; there is no witness the other way, and the driver walked
`n = 3..24` to look for one. Measured: compass-only `[5, 8, 10, 12, 15, 16, 17, 20, 24]`,
**lattice-only `[]`**, both `[3, 4, 6]`, neither `[7, 9, 11, 13, 14, 18, 19, 21, 22, 23]`.

**The corrected statement is stronger.** With the neusis rung above — every power of two is 3-smooth
— the polygon ladder is a **chain**:

```text
   lattice  ⊊  compass  ⊆  neusis  ⊆  radicals
```

which makes the ladder an actual ladder rather than a set of incomparable instruments, and it is
`CLAUDE.md` §8's rule working as intended: the control was written to fail, and it did.

**The table above is unaffected** — all four of its rows already showed lattice ⊆ compass, and the
summary sentence contradicted the table it was summarising.

Quasicrystals are the same sentence one move on: drop periodicity — adjoin a channel — and five-fold
symmetry is admitted. The instrument changed; the pentagon did not.

---

## 2 · What the fetched sources do and do not support

**This section exists because the automated first pass got two of them wrong, and the corrections are
load-bearing.**

- **MathWorld contradicts itself on Gauss.** `GeometricConstruction.html`: *"In 1796, Gauss **proved**
  that the number of sides of constructible polygons had to be of a certain form involving Fermat
  primes."* `ConstructiblePolygon.html`: Gauss *"gave a **sufficient** condition… which he also
  **conjectured (but did not prove) to be necessary**."* **The second is the historically correct
  one.** Carry both; do not silently pick.
- **The criterion `n = 2^k·p₁⋯p_t` is on NONE of the fetched pages**, and neither is any degree or
  field-extension condition. A grep of the raw HTML for `2^k`, `distinct Fermat`, `degree`,
  `extension`, `power of 2` returned zero. The only structural statement given is indirect and is
  worth having in its own right — Gardner (1977) and Watkins: *"the number of sides for constructible
  polygons with **odd** numbers of sides are given by the **first 32 rows of the Sierpiński sieve
  interpreted as binary numbers**"*, giving `1, 3, 5, 15, 17, 51, 85, 255, …` — *"every row is a
  product of distinct Fermat primes, with terms given by binary counting."*

  **That is the fork counting itself.** A Fermat prime is `F_n = 2^(2ⁿ) + 1` — the fork of the fork,
  plus one — and the admissible odd polygon population is the Boolean lattice on the known Fermat
  primes, read off Pascal's triangle mod 2. `H.0150`'s membership words, in Gauss's problem.
- **Wantzel appears only in the bibliography** of `ConstructiblePolygon.html`. `CubeDuplication.html`
  credits the impossibility proof to **Descartes 1637**, which is a minority attribution; flag it
  wherever it is cited.
- **Neusis has no stated degree reach in MathWorld.** The page is a stub: *"a **verging
  construction**, which allows the classical geometric construction rules to be bent in order to
  permit **sliding of a marked ruler**. Using a Neusis construction, cube duplication, angle
  trisection, and construction of the regular heptagon are soluble."* **It does not say cubics.** The
  cubic reach is standard mathematics and is asserted here on that basis, not on MathWorld's.
- The one quantitative anchor across the whole neusis/heptagon pair is
  `RegularHeptagon.html`'s **`8x⁶ − 20x⁴ + 12x² − 1 = 0`** for `x = √2·cos(π/7)` (Bankoff and
  Garfunkel 1973) — an even sextic, i.e. a cubic in `x²`, which is the degree-three obstruction in
  the only form MathWorld actually prints.
- **Cube duplication, verbatim:** *"the problem cannot be solved because the Delian constant `2^(1/3)`
  … **is not a Euclidean number**… The problem **can** be solved, however, using a Neusis
  construction."* That is the ladder in two sentences from the source itself.
- **`Elements.html`** supplies the structure: 13 books, 465 propositions, **23 definitions, five
  postulates, five common notions**, and *"Euclid's postulates were **not rigorously complete**…
  **Hilbert needed a total of 20 postulates**."* The fifth is independent. The laboratory already
  formalised its dissolution — `a07ff376:src/labyrinth/mathematics/lean/Derive_Euclidean.lean:94-99`:
  *"the parallel postulate is NOT an independent axiom — it is the abelian law `u ⊕ v = v ⊕ u`,
  equivalently **gyr = 0**."* **Flatness is gyration zero**, in Lean, uncited by anything live.

---

## 3 · Huffman is condensation, and the fork is the codeword

`HuffmanCoding.html`, verbatim: an algorithm that *"works on a list of weights by building an
**extended binary tree with minimum weighted external path length**… finding the two smallest `w`s…
and replacing them with an internal node of weight `w₁ + w₂`… An individual external node can then
be encoded by a binary string of **0s (for left branches) and 1s (for right branches)**."*

Three readings, each checkable:

1. **The merge is condensation.** Replacing the two least by their sum is exactly §11's *far
   population → compact realizer*, iterated. The remainder is certified because the tree is retained.
2. **The codeword is the membership word.** A leaf's code is its path as a `{0,1}` string — the same
   `2ⁿ` Boolean-lattice indexing as `H.0150`'s crossing words and `multiquadratic`'s `(ℤ/2)ⁿ`
   grading. **The prefix tree and the crossing-word algebra are the same combinatorial object.**
3. **Huffman prices the half.** MathWorld: it *"**approximates the probability for each character as a
   power of 1/2** to avoid complications associated with using a nonintegral number of bits."* That
   is a receiver forcing its quotient onto the dyadic lattice, and **the price is measured** by
   Devillers–Gandoin (§4): `log₂(p+1)` achievable with arithmetic coding against `⌈log₂(p+1)⌉` with
   integral bits, so *"the gain for each point would be `log₂ n − 3` instead of `log₂ n − 2.402`"* —
   **0.598 bits per point, paid for rounding to a power of one half.**

**And the laboratory already deposited the consequence, in Lean, uncited here.**
`a07ff376:src/labyrinth/mathematics/lean/Derive_Eaten.lean:205-230`:

> *"A perfect code (an entropy layer — a compressed/encrypted stream) is INCOMPRESSIBLE: relating it
> admits no simpler handle within the register, so the swing BREAKS → None = FOUND (irreducible
> here). This is the lean-trap signature: **the entropy layer reads as a PRIME, not a structure to
> grind.**"* — with `theorem perfect_code_founds (lo hi : Holonics.Swing.Q) : Found lo hi 0 := rfl`.

**An optimally coded stream is a prime to this machine.** Huffman and Kraft appear nowhere in the
live tree.

---

## 4 · Devillers–Gandoin: the order is worth `n log n` bits, and that prices our own front

`arXiv:cs/9909018`, Olivier Devillers and Pierre-Marie Gandoin, INRIA, 28 Sep 1999, *Geometric
compression for progressive transmission*.

Prior art spends the vertex **order** on the topology and predicts coordinates from coded
neighbours. **They invert it**: discard the topology, spend the order entropy on the coordinates,
and reconstruct the topology afterward by Delaunay. For a kd-tree cell holding `p` points the count
in the first half-cell costs `log₂(p+1)` bits, and for `n` uniform points in `Q` bits per point:

```text
separation   ≤ 2.402 n
localization  = n (Q − log₂ n)
TOTAL         = n (Q − log₂ n + 2.402)
```

Their sentence: *"the **gain is `log₂ n − 2.402` per point**… which corresponds exactly to the
**order information** over the points… **the algorithm saves the encoding of the order
information**."* And the bound is the right way round: *"this theoretical gain is a **lower bound**:
the uniform distribution is the '**worst-case**'… the **most structured is the distribution, the most
efficient is the algorithm**."*

**This prices a question this repository has been treating as purely a correctness question.**
`research/records/2026-08-10_THE_SPINE_ASSESSED_BY_ITS_OWN_LAW…` §3.4 asks whether host arrival order
in `merge_witnesses` is receiver-visible, and states the two outcomes. Devillers–Gandoin adds the
third fact: **order costs `n log₂ n` bits.** Carrying apparatus completion order into a returned
population is therefore not merely a possible contaminant — it is a **measurable overpayment**, and
dropping it is a measurable gain that grows with the population. The law *"apparatus completion order
never enters semantic lineage"* has a price tag.

Measured results are honest in both directions: they **lose** on `shape` (12.7 vs 9.3 bits/vertex
against Touma–Gotsman) and marginally on `cow`, and win by a wide margin on `dumptruck` (4.7 vs 7.6)
— consistent with their own structure claim. Stated limitation, verbatim: *"Its originality (**and
most important limitation, too**) is to **drop the topology**… and so to be useful **only when
coupled with a reconstruction technique**."*

---

## 5 · The third source is not the paper it was taken for, and it is more useful than expected

`arXiv:2607.17146v1` is **not** a grokking or compression paper. It is **Zhihua Liang** (INFN
Cagliari, single author, 19 Jul 2026, `cond-mat.dis-nn`), ***The Geometry of Semantic Space: A
Continuous Geometric Framework for the Transformer Architecture***.

**Its Table 1 is a correspondence card written by an outsider**, and it is the vocabulary atlas this
repository lacks, for one domain:

```text
sequence index        → base manifold coordinate μ ∈ ℳ
embedding dimension   → fiber dimension ℱ_μ ≅ ℝ^d
hidden state          → section of the bundle Ψ ∈ Γ(E)
RMSNorm ε             → topological mollifier
RoPE                  → GAUGE CONNECTION / path monodromy
Softmax attention     → Urysohn–Volterra operator
FFN                   → Hodge reaction field
residual stream       → depth-parameterised flow Ψ(z,μ)
layer index l         → algorithmic depth z ∈ ℝ⁺
weight decay λ        → Tikhonov gauge mass penalty
```

Four joins to standing holonics, each with the paper's own measurement:

1. **Loss is non-commutation, measured in a real transformer.** The Lie–Trotter operator-splitting
   error carries a **torsion term `−[𝒯,ℛ]Ψ`**, and the residual's alignment with that commutator is
   measured at `cos = +0.717` mean (Qwen3) and `+0.623` (GPT-2) against a random baseline of `0.031`
   / `0.036` — **23× and 17× excess, positive on 127 of 128 and 81 of 96 layers.** `H.0420` says loss
   is the failure of a square to commute; this is that failure measured as a commutator in a
   production model.
2. **Deleting the hand destroys the body.** Symmetrising the FFN (`W_out = W_in^⊤`) **drives the
   imaginary part of the Jacobian spectrum to exactly zero at every layer** and takes amplification
   from 93× to **142,955×** — an instability factor of **1,541×** on Qwen3-0.6B. §2b: a sign keeps the
   magnitude and discards the turn. Gemma-3-1B survives at ~1× because its Post-Norm supplies the
   other half of their Dual-Law — **two independent ways to keep the turn.**
3. **Attention is a global constraint, not a boundary flux.** Their Lemma 8: attention
   *"fundamentally lacks a local spatial Laplacian `Δ_g`."* That is `H.0219`'s classification handed
   over by an independent author: no local operator ⟹ it does not decompose over a partition.
4. **Weight decay is a structure-group reduction.** Their Theorem 13: `L²` decay *"breaks non-compact
   scaling symmetries (like `GL(1,ℝ)`)… it definitively fails to break `SO(d)` symmetries [but] this
   is inconsequential; because `SO(d)` is a strictly compact Lie group."* `canon/TABLET_THE_MANIFOLD.md`
   §16 — every geometry is a reduction of the structure group — with a measured consequence.

**Its own boundary, verbatim, and it is the honest one:** *"We classify this framework explicitly as
a **Classical Lattice Field Theory on a rigid Galilean background**… The framework fundamentally
lacks the diffeomorphism invariance of a true relativistic field theory… **the geometry is the map,
not the territory.**"* And Remark 5 refuses its own error bound: with `Δz = 1` the step *"formally
exceeds the convergence radius of the infinite Hausdorff series,"* so the `𝒪(Δz³)` remainder *"cannot
be interpreted as a strict analytical bound."*

**That is a NON-EQUIVALENCE line written by the source about itself**, which is exactly what a
correspondence card requires and what this repository has to supply for its own claims.

---

## 6 · One source was not retrieved, and nothing here rests on it

**`https://openreview.net/forum?id=27fc8hXB5N` — Lei and Xu, *Geometric Compression in Grokking: The
Three-Stage Modular Dynamics of Transformers* — was NOT fetched.** OpenReview returned
`ChallengeRequiredError` (HTTP 403) to every route: the forum page, both API versions, three direct
PDF paths, a reader proxy, and the Wayback Machine, which has **no snapshot**. Semantic Scholar
rate-limited three attempts.

What is available is search-engine snippets, and they are recorded here **as snippets, not as the
source**, with two discrepancies that themselves need resolving: the indexed date is **October 2025**
against the 2026 in the citation, and the indexed PDF carries a **different title**
(`CONSTRUCT-THEN-COMPRESS: GEOMETRIC DYNAM…`), suggesting a retitle between versions.

The snippets name three stages — *Coherence Collapse*, *Asynchronous Construction and Compression*
(a *"silent phase where Attention initiates geometric reorganization, followed by MLP with temporal
offset"*), *Post-Grokking Refinement* — and a **Geometric Coherence Score** measuring *"directional
alignment of local Jacobian transformations across the data manifold."*

**No claim in this record depends on any of that**, and nothing from §6 may be cited as established
until the paper is read. The practical route is a browser session that completes the challenge.

**What the sweep did establish about grokking is stronger and is ours already:** the frozen
laboratory holds **22 files and two runnable experiments** (`experiments/byte-lm/sidecar/arith_grok.py`,
`code_exec_grok.py`), Power et al. 2022 with the memorisation-circuit → algorithmic-circuit phase
change, and — the part the live tree lacks — a **measured order parameter**:
`a07ff376:experiments/byte-lm/sidecar/totality/susceptibility.py:5`, *"susceptibility
`χ = Var_window(φ)` **PEAKS** at a phase transition."* Live holonics has phase transition as a typed
topological object (`TABLET_THE_FLOW` §7) and **no detector**. Grokking and Huffman are the two
subjects that exist only at `a07ff376` and were never carried forward.

---

## 7 · What this changes

| | before | after |
|---|---|---|
| `multiquadratic.rs` | the tower's turn carrier | **also the straightedge-and-compass field**, aperture `2ⁿ`, unnamed until now |
| `winding_inertia.rs`'s Niven set | a rationality special case | **the crystallographic restriction**, which is the admissibility law of `THE_COLOR_IS_A_RECEIVER_QUOTIENT`'s crystal |
| `quintic_chart.rs` | the Tschirnhaus organ | **one rung of an instrument ladder** whose lower rung is `multiquadratic` and whose middle rung (neusis) is absent |
| aperture | a declaration a caller makes | **an index condition on a group, with two classical theorems that disagree** |
| order in `merge_witnesses` | a possible contaminant | **priced: `n log₂ n` bits** (Devillers–Gandoin) |
| Huffman | absent | **condensation whose codeword is a membership word, pricing the half at 0.598 bits/point** |
| a perfect code | — | **a prime**, already proved in the laboratory's Lean and uncited here |
| flatness | a geometric condition | **`gyr = 0`**, already dissolved in the laboratory's Lean and uncited here |
| loss is non-commutation | a holonic theorem | **measured at 23× baseline as a Lie bracket in production transformers** |

---

## 7b · BUILT AND MEASURED, 2026-08-10 — the two rungs meet and disagree

**Truth status:** `implemented-exact`; `measured` for every figure, from
`crates/holonic-engine/examples/the_two_instruments_disagree.rs`.

`multiquadratic.rs` now states its **structural aperture** in its own source, distinguished from
`DECLARED_KERNEL_BOUND`: the bound limits a *search*, the aperture limits the *field*, and no bound
can move it. `Multiquadratic::tower_degree` returns `2ⁿ`, read off the element.

`quintic_chart::{CompassVerdict, read_compass_rung, LadderReading, read_ladder}` joins the rungs, and
the positive verdict is named `NecessaryConditionHolds` because that is all a degree test earns —
a degree-four irreducible with Galois group `A₄` or `S₄` passes it and is not constructible. **There
is deliberately no `is_constructible` method.**

Measured on seven declared polynomials, one receiver family, both instruments:

```text
polynomial                       deg  compass          radical
x^3 - 2   (the doubled cube)       3  REFUSES          RETURNS   ← RUNGS DISAGREE
x^3 - 3x - 1 (trisection cubic)    3  REFUSES          RETURNS   ← RUNGS DISAGREE
x^2 - 2                            2  NECESSARY-ONLY   RETURNS
x^4 - 2                            4  NECESSARY-ONLY   RETURNS
x^5 - x - 1                        5  REFUSES          REFUSES
x^6 - x - 1                        6  REFUSES          OPEN
x^7 - 7x + 3                       7  REFUSES          REFUSES
```

**Two of the three Greek problems of antiquity appear as a disagreement between two instruments over
one object, and both verdicts are correct.** The compass refuses `∛2` because the Delian constant is
not a Euclidean number; radicals return it because every cubic is solvable. The trisection cubic does
the same. Neither instrument is better and neither object changed.

Controls: the compass refuses somewhere and not everywhere (5 / 2); the radical wall is real and
crossed (4 returned / 2 refused); the tower degree is read off a real element rather than declared.
### 7b.1 The neusis rung — roadmap item 2

A marked ruler reaches `{2,3}`-towers, so a reachable degree is `2^a·3^b` (3-smooth) —
`proved-standard`, Videla 1997. MathWorld's `NeusisConstruction` names the three problems it settles
and **states no degree**, so the condition is asserted on the standard literature and not on that
page.

**The rung's asymmetry with the compass rung is the honest part and is stated in the type.** The
compass rung has a *carrier* — `multiquadratic` computes in `ℚ(√k₁,…,√kₙ)` exactly. **The neusis rung
has none**: nothing in either repository does arithmetic in a `{2,3}`-tower, so `NeusisVerdict` states
an aperture and computes no root, and its doc says so.

Measured on nine declared polynomials, one receiver family, three rungs:

```text
polynomial                                    deg  compass          neusis           radical
x^3 - 2   (the doubled cube)                    3  REFUSES          NECESSARY-ONLY   RETURNS  ← crosses
x^3 + x^2 - 2x - 1  (2cos(2π/7), the heptagon)  3  REFUSES          NECESSARY-ONLY   RETURNS  ← crosses
x^2 + x - 1  (2cos(2π/5), the pentagon)         2  NECESSARY-ONLY   NECESSARY-ONLY   RETURNS
x^3 - 3x - 1  (a trisection cubic)              3  REFUSES          NECESSARY-ONLY   RETURNS  ← crosses
x^2 - 2                                         2  NECESSARY-ONLY   NECESSARY-ONLY   RETURNS
x^4 - 2                                         4  NECESSARY-ONLY   NECESSARY-ONLY   RETURNS
x^5 - x - 1                                     5  REFUSES          REFUSES          REFUSES
x^6 - x - 1                                     6  REFUSES          NECESSARY-ONLY   OPEN     ← crosses
x^7 - 7x + 3                                    7  REFUSES          REFUSES          REFUSES
```

**All three Greek problems of antiquity are refused by the compass and admitted by the neusis rung**,
computed rather than recited: MathWorld's stub names exactly cube duplication, angle trisection and
the regular heptagon as soluble by a marked ruler, and those are the three that cross.

**The heptagon row is the one that carries the method.** The 7-gon's constructibility is a question
about a **degree-three** number, not a degree-seven one: `[ℚ(2cos(2π/n)):ℚ] = φ(n)/2`, and
`φ(7)/2 = 3`. Its minimal polynomial is `x³ + x² − 2x − 1`. The pentagon's is `x² + x − 1`, degree
`φ(5)/2 = 2`, which is why 5 — a Fermat prime — holds at the compass and 7 does not.

**And two instruments agreeing is not two instruments being the same instrument.** `x⁵ − x − 1` is
refused by neusis **and** by radicals, for different reasons: 5 is not 3-smooth, and `S₅` is not
solvable.

Controls: the neusis rung refuses somewhere and admits somewhere (2 / 7) — a rung that admits
everything is not a rung; the pentagon does not cross and the heptagon does.

### 7b.2 The lattice rung — roadmap item 3

`winding_inertia::{lattice_admits_order, polygon_turn_degree}`, the first **derived from
`niven_value`** so the crystallographic restriction and Niven's theorem cannot drift apart, the
second `φ(n)/2` by trial division with no table. Driven by
`examples/the_pentagon_divides_the_instruments.rs` over `n = 3..24` against all three rungs.

**The compass test is decisive for polygons and only necessary in general**, and the driver says why:
a cyclotomic extension is **abelian**, so its Galois group is its own closure and a 2-power degree
makes it a 2-group automatically. That is Gauss–Wantzel, and it is the reason
`the_two_instruments_disagree` must report `NECESSARY-ONLY` where this driver may decide.

**Its first run falsified §1.4** — see the correction there. Roadmap items 1, 2 and 3 are closed.

### 7b.3 The order has a price — roadmap item 4, first half

`interchange::{order_price_bits, OrderPrice}`. An order over `n` items costs **`⌈log₂(n!)⌉` bits**,
computed exactly over `BigUint` with the factorial built and its bit length read off. No Stirling on
the path; `n log₂ n` appears only as a scale column.

**The two halves are kept apart on purpose.** The price is arithmetic and always correct. Whether
those bits buy anything is a measurement against **one declared receiver family**, which
`interchange.rs` already decides by exhibiting a distinguishing word. `OrderPrice::overpayment()` is
zero unless the certificate itself says the family is blind.

Measured on four declared materials by `examples/the_order_has_a_price.rs`:

```text
material                       staged  verdict        bits  overpayment
TwoGadgets (independent pair)       2  INTERCHANGE       1  1
TwoGadgets (whole order)            2  ORDERED           1  0
CoupledJunctions                    1  ORDERED           0  0
SameEndpointDifferentPath           2  ORDERED           1  0
```

**So `"apparatus completion order never enters semantic lineage"` now has a magnitude**, and
Devillers–Gandoin's *"the algorithm saves the encoding of the order information"* is the same
quantity from the other side: what a coder gains by dropping an order is what a front loses by
carrying one.

**The second half is BLOCKED, and the blocker is a defect the roadmap already forbids.**
`examples/the_front_is_ordered_until_a_certificate_unorders_it.rs` runs the certificate on
`soma/formal` and **SIGKILLs at HEAD — exit 137**, measured 2026-08-10 and confirmed against a clean
checkout of that file, so it is not caused by this session's work. Until it completes, the
real-material order price is unavailable and is **not guessed**. `blueprint/THE_ROADMAP.md`'s own
prohibition — *"No aperture-less organ in the corpus path"* — already names `eros_resonant_corpus_current`
SIGKILLing at 10,963 MB; **this is a second instance and it was not on the list.**

### 7b.4 The five cuts, named — roadmap item 5

`crates/holonic-engine/src/spine_cut.rs`. The spine states the chain law and then
*"circulation `j ≠ 0`, rest, accumulation, leak, and short circuit are distinct cuts"*, with the
reading rule *"report which of rest, accumulation, leak, or short circuit applies."*

**The missing object was the classifier, not an organ.** Four cuts had owners; naming which one a
reading is at is a measurement, and nothing was making it.

```text
r ≠ 0 anywhere                             LEAK
j = 0                                      REST
q_n ≠ q_m                                  ACCUMULATION
j ≠ 0, closed, vanishing on the load       SHORT CIRCUIT
j ≠ 0, closed, reaching the load           CIRCULATION
```

The order is stated rather than left implicit: a leak outranks the closed cuts because a body with a
source is not at one, and accumulation outranks the two closed cases because a stored residual is not
a circulation however the current is supported.

**A short circuit is defined without resistances or cost.** It is the exact statement that a closed,
source-free, non-zero current is supported **entirely off the declared load**. The load is the
caller's declaration and is never inferred, and an **empty load is refused by name** — with no load
every closed current is trivially a short circuit, which would make the cut a property of the
declaration rather than of the material. That is `CLAUDE.md` §8's vacuous-gauge defect, refused at
construction.

Six controls, one of which reaches **all five cuts on one incidence** — a theta graph with the third
parallel edge as the load — so the return is a classification and not a predicate wearing five names.

---

## 8 · Bounds

- §1's ladder is `interpretation`. The individual apertures are `proved-standard`; that they form one
  ladder, and that an instrument is a receiver family, is this project's reading.
- **No claim here rests on MathWorld for the `2^k · (distinct Fermat primes)` criterion**, which is
  not on the fetched pages. It is standard mathematics and is used as such, with Wantzel credited for
  necessity against MathWorld's own two conflicting attributions.
- The neusis cubic reach is standard mathematics; MathWorld does not state it.
- **Nothing is built.** This record identifies two organs, names a missing rung, and prices one open
  question. `multiquadratic`'s structural aperture is not yet stated in its own source, the neusis
  rung does not exist, and the `n log₂ n` price has not been measured on this body's front.
- §5's four joins are the paper's measurements, not ours, on five model families at 124M–8B
  parameters. Its own scope statement is quoted rather than softened.
- §6 is unfetched and is fenced. §3's laboratory Lean and §2's `Derive_Euclidean.lean` are read at
  `a07ff376` and are `HUNCH`/`OPEN`-graded in their own repository; they motivate and do not grade.
