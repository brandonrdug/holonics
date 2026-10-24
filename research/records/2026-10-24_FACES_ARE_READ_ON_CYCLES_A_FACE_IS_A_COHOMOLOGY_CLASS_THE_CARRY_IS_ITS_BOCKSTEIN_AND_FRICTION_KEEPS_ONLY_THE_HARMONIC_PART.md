# Faces are read on cycles: a face is a cohomology class, the carry is its Bockstein, and friction keeps only the harmonic part

Refs #404 #405 #410. Follows [the one face law](2026-10-24_ONE_FACE_LAW_A_FACE_IS_A_CONGRUENCE_SO_LANGUAGE_ARITHMETIC_AND_ANY_OPERATION_ARE_READ_BY_ONE_CONTACT.md).
Status:
- the laws are proved-standard: group and monoid cohomology, the Bockstein, Künneth, the Hodge
  decomposition, lattice gases and the replicator;
- the census is exact;
- the readings for Athena in §8 are [definition; agent-inferred, October 24].

Brandon's correction (paraphrased, October 24): language and arithmetic share their shape through
cycles, not through arithmetic. The cycles are homology and cohomology, Hodge and the spectra of RH,
with crossing and friction as causality, inside the unified physics. Conservation of faces together
with bitwise operations holds for fluid simulations of any model, and for meta-models (evolution
itself). The one-face-law record stated conservation as a congruence. This record states where the
congruence comes from: a face is read on a cycle, and its failure is a class on the cells the cycles
bound.

## 1. A conserved face is a class read on a cycle

A face valued on a circle, conserved additively by an operation, is a homomorphism into the circle:
a character, a class in `H¹(G; ℚ/ℤ) = Hom(G, ℚ/ℤ)`. Examples:
- the last digit (`a ↦ a/10`);
- a permutation's sign (`S_n → ℤ/2`);
- the parity of a length;
- an image's Fourier phase under translation;
- a pitch class under transposition;
- the valuation `v_p` under multiplication (`ℚ^× → ℤ`), whose free generators, the primes, are the
  primitive cycles of multiplication (`rh.primes-primitive-cycles`).

A class is read by pairing it with a cycle, and the reading of a closed passage depends only on the
class (`holon.pairing-descends-to-classes`). A coboundary reads zero on every cycle. Group cohomology
is the cohomology of the group's classifying complex, so `H¹` is read on its loops and `H²` on the
cells the loops bound.

## 2. The binding is the Bockstein of the face: the carry

The short exact sequence `0 → ℤ → ℚ → ℚ/ℤ → 0` connects the two degrees.
- The phase `a ↦ a/n` is a character of `ℤ/n`. Lifting it to the integer digit `a ∈ {0, …, n−1}`
  fails by the carry `c(a, b) = ⌊(a + b)/n⌋`, a 2-cocycle (`winding.carry-cocycle`). Its class is
  the Bockstein of the phase in `H²(ℤ/n; ℤ) ≅ ℤ/n`.
- **Read on the cycle.** The lap `a → a + 1` around `ℤ/n` carries exactly once:
  `Σ_a c(a, 1) = 1`. Every integer coboundary `δb(a, b) = b(a) + b(b) − b(a + b)` reads `n·b(1)` on
  that lap. So the class has order exactly `n`: no integer re-reading of the digit removes the carry,
  while `n·c` is the coboundary of the digit itself (census for `n = 2, 3, 10`).
- **A real chart erases it.** Over `ℚ` the carry is the coboundary of the phase `a/n`, so a real
  chart absorbs the carry and loses the winding. It is torsion, which a harmonic reading over `ℚ`
  cannot see (`constitution.harmonic-is-cohomology`: torsion invisible). This is the cohomological
  form of the exactness law: a float carrier is a real chart, and it trivializes the carry by dropping
  the lap.
- **Bits** (`n = 2`, all 65,536 pairs of bytes):
  - the carry is `c = a ∧ b`, and `a + b = (a ⊕ b) + 2(a ∧ b)`: the split part plus twice the
    cocycle;
  - the ripple sum `s_i = a_i ⊕ b_i ⊕ c_i`, `c_(i+1) = maj(a_i, b_i, c_i)` reproduces every sum.
    The majority is one locked sheet (`parametron.cellular-automaton-lock-face`), so binary
    addition is a chain of parametron locks carrying the class;
  - XOR conserves every bit (no plural fibre at any of the 8 bits), while `+` leaves bits 1 to 7
    plural on all 4 of their face pairs. XOR is the split extension, `+` the extension glued by the
    AND cocycle.
- **Multiplication's faces bind under addition by the same carries.** `v_p(C(m+k, k))` is the number
  of carries of `m + k` in base `p` (Kummer, `coupling.landmarks-and-moduli`, formal-checked).

## 3. Language's seam is a class, and a cycle certifies it

- The count of `th` obeys `n(xy) = n(x) + n(y) + s(x, y)`, with `s(x, y) = [x ends in t][y starts with h]`
  (exact on all 14,641 pairs of words of length 0 to 4 over `{t, h, a}`).
- `s` depends only on each operand's face, its first and last letter. It is a 2-cocycle on the face
  monoid `M = {ε} ∪ {t, h, a}²`, with product `(f, l)(f′, l′) = (f, l′)` (checked on all `10³`
  triples).
- **Upstairs it is trivial.** On words, `s` is the coboundary of the count itself: carrying the count,
  or the seam state that generates it, conserves the face (the one-face-law record).
- **On the faces it is a class**, even over `ℚ`: the coboundary system has rank 10 and its
  augmentation by `s` rank 11. The certificate is the 2-cycle `[at|ha] + [aa|aa] − [at|at] − [ha|ha]`
  (faces written as first and last letter). Every coboundary reads 0 on it and the seam reads 1 (the
  Fredholm alternative, `compression.fredholm-alternative`).
- **Torsion and rational classes.** The digit's carry is a torsion class, seen only with integers. The
  seam is a rational class, because the count of `th` never wraps. Read the count mod `n` and it
  becomes torsion like a digit.

Language and arithmetic therefore share one shape through cycles. Each face is a class. Where the
operation does not conserve it, its binding is a 2-class read on a certificate cycle, and carrying the
state that generates the binding trivializes it.

## 4. The contact's blocks are the Künneth summands

- Functions of two operands' faces split as `1⊗1 ⊕ V_X⊗1 ⊕ 1⊗V_Y ⊕ V_X⊗V_Y` (Künneth for functions,
  the analysis of variance). With `x̄ = (x, 1)` and `ȳ = (y, 1)`, the contact `W(x̄ ⊗ ȳ)` of
  `contact.face-table-blocks` has exactly these four blocks.
- The four-cycle annihilates the first three summands and reads the fourth: every unit four-cycle
  vanishes exactly when the interaction part vanishes (census, every table below).
- The interaction's rank over `ℚ` is the number of rank-one bilinear contacts that read the face
  from its operands' classes:

| Face table | Interaction rank |
|---|---|
| carry of a sum mod 10 | 9 = 3² |
| last digit of a sum, read as an integer | 9 = 3² |
| last digit of a product | 7 |
| product of 0..9 | 1 |
| sum of 0..9, no wrap | 0 |
| `tr(AB)`, 81 matrices over `{−1, 0, 1}` | 4 = 2² |
| `det(AB)`, the same matrices | 1 |
| contains `th`, the 11 `th`-free words of length 1 to 2 | 1 |
| count of `th`, the 13 words of length 0 to 2 | 1 |

**The chart decides.**
- Read as classes, the last digit of a sum costs rank 9. In the phase chart it costs nothing:
  `e^(2πi(a+b)/n) = e^(2πia/n) e^(2πib/n)` is one product of characters (`arith.binding-four-cycle`:
  `□((a + b)/q) ≡ 0` mod 1).
- The carry is then the lap count of the summed phase, `c = ⌊a/n + b/n⌋`: the section crossing of the
  phase (`navigator.jumps-are-carries`), not a table.
- A carry read as a bilinear table is the costly chart; read on the cycle, it is one crossing.

## 5. Hodge: the slip splits, and friction keeps the harmonic part

On a complex a 1-cochain splits exactly and orthogonally into three parts (`constitution.hodge-split`,
`fluid.pressure-elimination`):
- **exact:** a potential's difference, which re-reading the faces absorbs;
- **coexact:** circulation around local cells. A nonzero four-cycle is a unit cell's circulation,
  its curl;
- **harmonic:** the period around a cycle that no local cell bounds.

Census on a 6×6 torus grid (36 vertices, 72 edges, 36 squares):
- the harmonic dimension is 2, the torus's two cycles;
- the declared integer field splits exactly into orthogonal parts with energies `33,703/280`,
  `34,547/280` and `37/4`;
- six steps of viscosity, `u ← u − (1/8) Δ_H u`, leave the harmonic part exactly unchanged at every
  step, while the exact and coexact energies fall strictly;
- all 6 row-loop circulations change, while their mean, the harmonic period, stays 3.

**Friction is causality's filter.** The Hodge Laplacian dissipates what potentials or local cells
explain, and cannot touch what only a cycle reads. What survives dissipation is cohomology. This is
why retention is the harmonic (dormant) part (`constitution.harmonic-is-cohomology`), and why a face
read on a cycle persists through a lossy passage.

Crossing completes the picture:
- the order of two moves is a four-cycle in time, and moves that do not commute leave a commutator
  carry (order is torsion,
  [record](2026-10-22_ORDER_IS_TORSION_AND_SUBGRAIN_INFORMATION_DISSOLVES_INTO_THE_CARRIED_RESIDUE.md));
- independent cycles of coprime periods cross once per residue pair (the Chinese remainder theorem);
- a unimodular rechart conserves their intersection number (`lock.unimodular-rechart`);
- faces read on crossing cycles are jointly injective, which is the closure of the one-face-law
  record.

## 6. Spectra: the trace formula pairs cycles with faces

- Characters diagonalize a cycle's shift, so the faces are the spectrum and the cycles the orbits.
- The trace formula pairs them:
  - `tr(fᵏ)` counts the fixed points of `fᵏ` (`aeon.zeta-map-periodic-points`);
  - the Lefschetz number reads them through cohomology (`cell.lefschetz-number`);
  - the zeta is a product over primitive cycles (`aeon.a8-dynamical-zeta`).
- For `ζ(s)` the primitive cycles are the primes and their faces the valuations. The explicit formula
  pairs prime cycles, with weights `log p / p^(k/2)`, with the zeros (`rh.primes-primitive-cycles`;
  `rh.explicit-formula-receiver`, formal-checked). Addition binds the valuations by carries (Kummer,
  §2).
- In these terms RH is the positivity of this cycle–spectrum pairing on every autocorrelation (Weil),
  the repository's standing open target. This record adds the reading and no step toward it.

## 7. Bitwise emulation of a fluid, and meta-models

**A lattice gas emulates a fluid with bits.** The HPP gas carries four direction bits a site. Its
collision (a head-on pair turns a quarter) and its streaming are bitwise. Census on a 16×16 torus,
64 steps:
- mass and both momenta are conserved exactly at every site and every step, with invariants
  `(387, −1, 0)`, while 31,548 bits flip;
- the collision is an involution and changes 2 of the 16 site states.

Its conserved faces are additive over sites, characters of the site product. The hexagonal FHP
version yields Navier–Stokes at large scale (Frisch, Hasslacher, Pomeau 1986). The model computes
with bits and conserves faces exactly; its hydrodynamics is what those faces read at a coarser grain.

**Evolution is a model read the same way.**
- Selection by a likelihood is the discrete replicator (`norm.bayes-replicator`).
- A payoff splits into two parts:
  - a symmetric part, whose replicator flow raises mean fitness at twice the fitness variance
    (Fisher). This is a gradient, the exact part;
  - an antisymmetric part, which on rock-paper-scissors conserves `Σ log x_i` and cycles. This is the
    harmonic part.

  Both identities are exact at 3 rational points in the census.
- This is the Hodge decomposition of game flows (Candogan, Menache, Ozdaglar, Parrilo 2011). For
  pairwise comparisons it is HodgeRank (Jiang, Lim, Yao, Ye 2011): a global ranking (exact), local
  triangle inconsistency (curl), and cycles that no ranking explains (harmonic).
- Price's equation splits a trait's change into selection and a transmission term. The transmission
  term is the trait face's failure to be conserved by reproduction.

## 8. What it means for Athena

1. **Keep the lap beside the phase.** A mode is a character of the stream's clock: its phase is the
   face and its lap count is the carry. The phase chart drops the carry (torsion), so a ring face read
   without its lap cannot carry a digit. The tower's modes keep phase and modulus and count no laps
   (`crates/holonics/src/hnn/tower.rs`); the section lift counts laps for a section
   (`hnn.dynamic-section-lift`). The exactness law already forbids the real chart inside the machine,
   and this is its cohomological reason.
2. **The bilinear block is for interaction that no chart removes:** a product's ring face, typed
   application, a trace, language's seam. A carry is read as the crossing of the summed phase, not as
   a rank-9 table.
3. **The slip's Hodge split names what absorbs it:**
   - exact: re-reading the faces (the one-sided blocks and the encoding);
   - coexact: a contact at a local cell (a fast mode with a fast mode);
   - harmonic: a held mode that closes a long cycle (a held mode with a fast one).

   The per-section report of where the bilinear weight sits reads this split.
4. **Friction is lawful.** Dissipation removes exact and coexact slip and leaves the harmonic part,
   which retention keeps (the dormant classes). A pairwise comparison's harmonic part is the
   irreducible cycling between Holons. It is never collapsed into one ranking or a single scalar of
   progress.
5. **One mechanism across sections and models.** Text, arithmetic, bits, a lattice fluid and a
   replicator population are read by the same faces, classes, crossings and contact. No section,
   modality or model needs its own routine.

The recorded failures this avoids:
- an authored routine standing in for learning: nothing is authored, and the census only checks laws;
- text as the exception: the law is stated on algebras and their cycles;
- a design thought in arrays: classes, cycles and Hodge parts;
- bits read as progress: no bits are claimed.

## 9. Owed Lean

One box in #410:
- the carry's class has order `n` in `H²(ℤ/n; ℤ)`: `Σ_a carry(a, 1) = 1`, and every integer
  coboundary reads `n·b(1)` on that lap; over `ℚ` it is the coboundary of `a/n`;
- the `th` seam is a 2-cocycle on the face monoid and not a rational coboundary, certified by the
  4-term cycle;
- every four-cycle vanishes iff the Künneth cross part vanishes, and the interaction rank is the
  least number of rank-one bilinear terms;
- the Hodge Laplacian kills the harmonic part, so viscous steps fix it (extending
  `Foundation/HodgeReceiver`);
- the HPP collision conserves mass and momentum and is an involution;
- an antisymmetric payoff with zero column sums conserves `Σ log x_i` under the replicator, and a
  symmetric one raises `xᵀSx` at twice the variance.

## Receipts

[`2026-10-24_FACES_ARE_READ_ON_CYCLES_receipts/`](2026-10-24_FACES_ARE_READ_ON_CYCLES_receipts/):
`cycles.py`, its output `faces_on_cycles.json` and `RUN.md`. Exact integers and fractions; every test
field is a declared integer formula.
