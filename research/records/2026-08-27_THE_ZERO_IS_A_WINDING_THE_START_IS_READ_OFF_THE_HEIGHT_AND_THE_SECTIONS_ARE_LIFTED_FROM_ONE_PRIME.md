# The zero is a winding, the start is read off the height, and the sections are lifted from one prime

**Date:** 2026-08-27 (session continuing into 2026-08-28 UTC)
**Kind:** two exterior arithmetic deeds over existing owners — the exact eta-zero winding atlas and
the Mestre realizer/section owner — with their drivers, artifacts, and measurements. **Schedules
nothing.** [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities;
the MEM6 line and the Hodge/Navier–Stokes Lean lines held by the other cursors are untouched.
**Provenance:** Brandon's direct request opening the session: *"Observe Sol's active Lean campaign,
both by reading the files and observing provenance. I want you to continue finding the Riemann Zeta
zeros and high lower bound rank elliptice curves, I want you to use Holons as computational &
mathematical objects to do so algorithmically."* Provenance cursor: `Arithmetic Realizer
Cartographer` (`OBJ-5331132c-7954-4de0-8b22-5f65bcab8db9`), objective
`OBJ-3d80b70a-22a5-479c-8abf-be8a5be0e410`, board messages local sequence 37–48.
**Truth grades:** each claim carries its own; `proved-derived; formal-checked` is claimed only for
the two Lean theorems cited by name, which were already standing.

---

## 0. What was observed before anything was built

[measured] Sol holds two live cursors: `Hodge Cartographer` (realization
`sol-lean-millennium-2026-08-27`), objective *Hodge common-star to exact prism / uniform carrier
and lateral cancellation*, whose newest file is
`ElementaryHolonics/Millennium/HodgeTriangleHomotopyPrism.lean` (1,287 lines, 32 `#print axioms`,
mtime 19:32); and `Athena Membrane Cartographer` (`sol-athena-membrane-mem6-2026-08-27`), at
MEM6-R4Q2B (resident factor-leg transport) per its messages of 2026-08-28 02:14 UTC. Its
in-progress `crates/holonic-engine/src/factored_moment.rs` test module references a field
`pivot_gram` that does not exist, so `cargo test -p holonic-engine --lib` did not compile during
this session; that is Sol's live edit and was routed around, not repaired. Neither cursor owned the
eta-zero atlas or the Mordell–Weil realizer owner, so a fresh pivot was spawned for them.

---

## 1. The zeta line — a zero is a winding, and the start was an authored level

### 1.1 The object

[definition] The atlas certifies, for a receiver box `[2/5, 3/5] × [τ, τ+1]`, the winding of its
boundary's image under `η(s) = (1 − 2^{1−s}) ζ(s)`, in exact rational interval arithmetic
(`relational_geometry::exact_analysis`). The winding is the zero count. A box symmetric about
`σ = 1/2` with winding one holds its zero **on** the line, because reflection carries zeros to
zeros and fixes only that line —
`RH.theZeroSetIsReflectionStable` and `RH.theOffLineZeroIsNeverAlone` in
`soma/formal/elementary-holonics/ElementaryHolonics/RH/Xi.lean` [proved-derived; formal-checked,
standing before this session]. No zero ordinate is accepted as input; the atlas locates each by
splitting the box.

### 1.2 The convicted level, and its measurement

[counterexample; measured] The atlas driver carried `euler_maclaurin_start: 12` since 2026-08-08.
The certified Euler–Maclaurin remainder is

```text
|R| ≤ |B_2m|/(2m)! · ∏_{i<2m}(|σ+i| + |τ|) · N^{1−σ−2m} / (σ+2m−1)
```

which grows like `((|τ|+2m)/N)^{2m}`. Measured 2026-08-27 with the built binary of 2026-08-18:
band `[60,61]` failed in 24.6 s and band `[100,101]` in 2.2 s, both with *"a boundary segment
remained unresolved at depth 14"*. The atlas had reached height 36 and could not go further.
**A start that is declared is an authored level; the height is the material.**

### 1.3 The repair — the start is derived, and the card carries the head

[established-bounded; implemented-exact; measured]
`relational_geometry::derive_euler_maclaurin_start(receiver, base, grain_bits)` returns the least
start whose exact remainder (`euler_maclaurin_remainder_bound`, the shared exact bound) is at most
`2^{-grain_bits}`, by doubling then bisection — the remainder is strictly decreasing in the start,
so the least one is well defined. The grain is the one declaration and travels with every band's
receipt; the verifier re-derives every band's start and requires equality. Integer logarithms are
memoized per thread (`log_integer_interval`). Measured single-threaded at grain 48: `[36,37]` start
40 in 19.9 s; `[100,101]` start 96, 57.7 s; `[200,201]` start 186, 117.2 s; `[500,501]` did not
close under the 175 s aperture. Cost law read off those returns: about 10 ms per
`(boundary point × head term)` in `BigRational`.

[established-bounded; implemented-exact; measured] The `O(N)` head `Σ_{n<N} n^{-s}` and its
`s`-derivative are therefore formed on the card. `crates/holonic-engine/kernels/exact_eta_head.cu`
computes them for every pending boundary midpoint of one certification depth in one launch, in
**Q31.96 fixed-point interval arithmetic** — signed 128-bit integers standing for dyadics with 96
fractional bits, 128×128→256 limb products, every lower end rounded down and every upper end up,
`exp(−x)` and `sin/cos` by the serial owner's own halving/series/tail/squaring laws, and the sum
over terms as exact integer addition in a block tree. `crates/holonic-engine/src/cuda_eta_head.rs`
hands the head to `relational_geometry::eta_evaluate_jet_with_head`, so the tail at `N`, the
Bernoulli corrections, the certified remainder disc, the `η` factor, the transport disc and the
winding remain the serial law. **The card returns enclosures and decides nothing.** Control
(`the_card_returns_the_eta_boundary_and_the_zero_is_a_winding control`): at `[36,37]` and
`[100,101]` the resident winding and boundary-point count equal the serial ones (46 and 60
points), the corner enclosures of both apparatus are 49 and 48 octaves wide and intersect, and the
card itself takes 1–2 ms of the 4.4–5.8 s per band — the serial tail is the remaining cost.

### 1.4 The law moved into a library, and refinement became transport along the cut

[established-bounded; implemented-exact; measured] `relational_geometry::eta_atlas` now owns bands,
lineages, relations and verification, parameterized by an `EtaJetSource` (`SerialJets`, or the
resident head). Certification is breadth-first — one batch of midpoints per depth — and with
serial jets it reproduces the depth-first owner's receipt **bit for bit** (control at `[36,37]`
and `[60,61]`). Refinement is `split_winding`: the two children share the parent's bottom and top
edges and each keeps its half of the parent's certified sides; the only new boundary is the cut,
one short horizontal edge, certified once and traversed in opposite directions. Measured at
`[60,61]`: the split returns windings `(0,1)` in 0.499 s against 4.102 s for a fresh child, and
both children verify. A band whose boundary winds `k` times descends as a lineage tree: a split
whose children both wind is a separation and the lineage branches; the verifier requires
additivity at every step, a selected child that winds, `k` lineages per winding-`k` band, and
every lineage ending at winding one. Two defects were found by verification and repaired: a cut
landing on an existing segment endpoint must carry that endpoint's stored image (the serial source
encloses corners and midpoints through different paths), and `[150,151]` holds two zeros.

### 1.5 The scan

[established-bounded; implemented-exact; measured] Verified compact artifacts under
`output/the_card_returns_the_eta_boundary_and_the_zero_is_a_winding/`, twelve workers each owning
one card context, grain 48, six grains, boundary depth 14, every artifact re-verified by
`... verify <artifact>` (which re-derives every start, every stored winding from its own polygon,
every partition and selection, and the relations):

| range | bands | closures | cumulative closures (= N(upper)) | seconds | artifact bytes |
|---|---|---|---|---|---|
| [12,36] | 24 | 5 | 5 | 18.0 | 3,196,063 |
| [36,100] | 64 | 24 | 29 | 56.3 | 17,081,046 |
| [100,200] | 100 | 50 | 79 | 131.9 | 43,838,353 |
| [200,300] | 100 | 59 | 138 | 168.9 | 59,312,064 |
| [300,350] | 50 | 31 | 169 | 93.6 | 33,521,097 |
| [350,400] | 50 | 33 | 202 | 100.3 | 37,369,832 |
| [400,450] | 50 | 33 | 235 | 111.8 | 39,449,749 |
| [450,500] | 50 | 34 | 269 | 138.3 | 41,848,676 |
| [500,550] | 50 | 36 | 305 | 134.7 | 45,318,742 |
| [550,600] | 50 | 36 | 341 | 136.1 | 47,905,604 |
| [600,640] | 40 | 29 | 370 | 132.9 | 39,420,739 |
| [640,680] | 40 | 30 | 400 | 139.6 | 42,001,489 |
| [680,720] | 40 | 30 | 430 | 118.3 | 41,741,280 |
| [720,760] | 40 | 30 | 460 | 143.5 | 44,275,120 |
| [760,800] | 40 | 31 | 491 | 151.5 | 46,741,925 |
| [800,840] | 40 | 31 | 522 | 131.8 | 45,913,721 |
| [840,870] | 30 | 23 | 545 | 104.1 | 35,042,389 |
| [870,900] | 30 | 24 | 569 | 126.6 | 37,568,204 |
| [900,930] | 30 | 24 | 593 | 111.3 | 37,141,220 |
| [930,960] | 30 | 24 | 617 | 110.1 | 38,935,315 |
| [960,990] | 30 | 23 | 640 | 146.2 | 37,938,332 |
| [990,1000] | 10 | 9 | 649 | 53.4 | 14,029,977 |
| **[12,1000]** | **988** | **649** | **649** | **2559** | **829,590,937** |

Every closure is one winding in a reflection-symmetric box, hence on the line; the running
closure counts at heights 100, 200, 300, 500 and 1000 are 29, 79, 138, 269 and **649**, which
are the classical `N(T)` there. The whole strip `[12, 1000]` closed in twenty-two chunks under the
175 s process aperture, about forty-five minutes of wall time on twelve workers sharing one RTX
4080 SUPER, 813 MB of compact verified receipts. No zero ordinate entered as input.

### 1.6 Boundaries and falsifiers

- The verifier re-derives the winding from the stored polygon and the starts from the stored
  boxes; it does **not** re-evaluate `η`. A card enclosure that lied consistently would pass it.
  The control mode is the check that reaches the card: serial and resident enclosures of the same
  point must intersect, and they do at every corner tested. **Falsifier:** any point where they do
  not.
- The serial tail is ~90 ms per boundary point and is now the whole cost; the card's head is 1–2 ms
  per launch. The chunk time grew from 94 s (50 bands at 300) to 140 s (40 bands at 640); the
  incremental Bernoulli rising products are the named next repair, and they change no law.
- Boundary depth 14 and the candidate splits `{1/2, 2/5, 3/5}` are declared apparatus; a zero pair
  closer than the depth resolves would refuse by name (`SEPARATION_LIMIT`).
- Nothing here is a statement about the Riemann hypothesis. It is an exact count and location of
  the zeros in the scanned strip, each certified on the line by the reflection theorem.

---

## 2. The rank line — the sections are solved by lifting from one prime receiver

### 2.1 The object

[definition] A Mestre family is the elliptic surface `y² = r(x,T)` over the variety
`e₁ = 0, 2e₅ = e₂e₃` of six values (`RealizerSextuple`, `crates/holonic-engine/src/mordell_weil_realizers.rs`,
built 2026-08-26). Twelve realizers `x = a_i ± T` are forced and carry rank eleven. A **section**
`x = αT + β` with `r(x(T),T)` a square in `Q[T]` is a realizer of every fibre at once; the family
rank over `Q(T)` is what every specialization inherits. `RealizerSextuple::linear_sections` solves
for them: the twelve linear forms split into complementary six-subsets, and the coefficient ladder
hands a quartic in the slope and a quadratic in the intercept to a rational-root finder.

### 2.2 The convicted cost, and its measurement

[counterexample; measured] The finder was `rational_root_census`: Sturm bisection on half-integer
endpoints from an absolute Cauchy bound of the monic companion `c^{n−1}A(z/c)`, which for the
degree-eight intercept polynomials is ~350 digits wide. `dbg_sections` (the previous session's
untracked debug driver) exited 124 at 175 s with no output on the first published family. The lib
test asserting the sections could not compile (Sol's live edit, above), so the claim was
unmeasured.

### 2.3 The repair

[established-bounded; implemented-exact; measured]
`holonic_engine::rational_polynomial::rational_roots_by_lifting`: residue roots of the squarefree
primitive form modulo one prime not dividing the leading coefficient (by exhausting the receiver);
every simple residue lifted by Newton's step to `p^k > 2|F₀||Fₙ|`; `a/b` recovered by Wang's
rational reconstruction; every candidate **verified by exact evaluation**. A prime at which any
residue root is not simple divides the discriminant, is refused by name, and the next is taken.
Reading: a rational number is a global object seen through one prime receiver as a residue; the
lift is transport along the `p`-adic direction; the reconstruction is the return to the global
chart; the exact evaluation is the receiver's check. Both published families return in 7.7 s.

### 2.4 The return

[established-bounded; implemented-exact; measured] Driver
`crates/holonic-engine/examples/the_sections_are_solved_and_the_family_rank_is_certified.rs`
(replaces `dbg_sections.rs`), artifact
`output/the_sections_are_solved_and_the_family_rank_is_certified/receipt.json`, 13.7 s:

| family (ICARM leaderboard) | linear sections solved | slopes | family rank over `Q(T)` |
|---|---|---|---|
| #159 (rank 17) | 6 in 3.0 s | ±79/53, ±35/53, ±31/53 | **≥ 12** at every probe |
| #161 (rank 18) | 6 in 3.0 s | ±5/3, ±7/15, ±1/15 | **≥ 12** at every probe |
| #280 (rank 19) | 6 in 5.7 s | ±91/101, ±11/101, ±149/101 | **≥ 12** at every probe |

Probe fibres `T ∈ {101, 1009, 2411, 3001}` fixed before any family was seen; independence by
reduction at primes below 4000 with torsion prime 5 (`independence_certificate`), torsion-freeness
witnessed at every probe; no height pairing, no regulator, no float. #161 and #280 had never been
solved. [interpretation] The six sections come in `±` pairs under `T ↦ −T` and span one direction
beyond the forced eleven; the three record curves are rank-twelve fibres plus five to seven
sporadic realizers.

[established-bounded; measured] Driver
`crates/holonic-engine/examples/the_section_census_walks_the_realizer_variety.rs` walks the
fundamental domain of `S₆ × {±1} × Q^×` on trace-zero integer heads (strictly increasing
coordinates, sup-norm shells up to 40, primitive content — scaling the six values is
`x ↦ λx, T ↦ λT` on the surface, one family), completed to the variety by `complete_to_sextuple`:
all 1,663,740 heads visited, **451 distinct families** in 79.8 s on 12 workers, linear-section
census `0:444, 4:6, 6:1`. Every four-section family certifies family rank ≥ 9 at all four probes.
The one six-section family, `[-23, -15, -10, -2, 27, 23]`, certifies only family rank ≥ 10 (T=101: 10, T=1009: 11, T=2411: 11, T=3001: 11) — small values, more relations among the eighteen realizers — so a section count is not a rank; the certificate is. **No family in that census exceeds the six linear sections the record families
carry**, and none reaches their certified twelve. Within Mestre's construction the linear-section
class saturates at family rank twelve on this population; rank beyond it in this construction
needs sections of higher degree in `T`, which is the named next construction and is not begun.
Artifact: `output/the_section_census_walks_the_realizer_variety/receipt.json`.

### 2.5 Boundaries and falsifiers

- The rank certificate is a **lower** bound; the analytic upper bound (explicit formula) is not
  touched. Nothing here is a statement about Birch–Swinnerton-Dyer.
- The census visited every head up to shell 40; most heads complete to no rational sextuple,
  and the population is integer heads only — a rational head off that lattice is outside it. **Falsifier of the saturation reading:** any family on the variety with more
  than six linear sections. The solver is complete for linear sections of a non-degenerate family
  (it refuses a sextuple with identically vanishing discriminant), so a counterexample is one
  `linear_sections()` call away.

---

## 3. What stands, by owner

| owner | what changed | grade |
|---|---|---|
| `crates/relational-geometry/src/exact_analysis.rs` | `derive_euler_maclaurin_start`, `euler_maclaurin_remainder_bound`, `log_integer_interval` (memo), `HeadJet`, `eta_evaluate_jet_with_head`, `polygon_winding` public | implemented-exact |
| `crates/relational-geometry/src/eta_atlas.rs` (new) | the atlas law: `EtaJetSource`, `certify_edges`, `boundary_winding`, `split_winding`, lineage-tree refinement, `build_atlas`, `verify_artifact`, schema v2 | implemented-exact |
| `crates/relational-geometry/examples/holonic_eta_ratio_atlas.rs` | thin serial driver over the library | — |
| `crates/holonic-engine/kernels/exact_eta_head.cu` (new) | the resident head in Q31.96 interval fixed point | implemented-exact |
| `crates/holonic-engine/src/cuda_eta_head.rs` (new) | `ResidentEtaHead`: mount, incremental log table, batched head jets, `EtaJetSource` | implemented-exact |
| `crates/holonic-engine/examples/the_card_returns_the_eta_boundary_and_the_zero_is_a_winding.rs` (new) | atlas / control / verify on the card | — |
| `crates/holonic-engine/src/rational_polynomial.rs` | `rational_roots_by_lifting` | implemented-exact |
| `crates/holonic-engine/src/mordell_weil_realizers.rs` | section solver uses lifting | — |
| `crates/holonic-engine/examples/the_sections_are_solved_and_the_family_rank_is_certified.rs` (new) | the certificate driver | — |
| `crates/holonic-engine/examples/the_section_census_walks_the_realizer_variety.rs` (new) | the census driver | — |

The v1 atlas artifact `output/holonic-eta-ratio-atlas/holonic-eta-ratio-atlas.ron` (declared start
12, height 12–36) is left in place: it is bound by content hash to
`holonic_zero_transport_complex`, and its schema is superseded, not rejected as evidence.
