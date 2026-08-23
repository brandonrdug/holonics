# The Mordell–Weil theorem holds at every modulus, and the algebraic side of the family chart is closed

**Date:** 2026-08-22
**Kind:** the family-chart summit of the algebraic side — under Brandon's goal to solve
the Birch–Swinnerton-Dyer conjecture by its Millennium statement.  Solo orchestrator
work, commits `51b9c54`, `a97e987`, `6fd8eb7` (on the day's earlier family arc).
**It schedules nothing.**
**Truth grades:** `proved-derived` with `formal-checked` evidence
(`[propext, Classical.choice, Quot.sound]`, zero `sorryAx`) throughout.

---

## 1. The headline

**`theMordellWeilTheoremAtEveryModulus`** — on every congruent-number curve
`y² = x³ − n²x` with `n ≥ 1`, the group of rational points is finitely generated.
One kernel-checked theorem, the modulus universally quantified: a formal
Mordell–Weil theorem for an infinite family of elliptic curves.  To our knowledge
nothing of this shape exists in any proof assistant.

## 2. The three laws that closed today, and the assembly

- **`theFaceIsAHomomorphismAtEveryModulus`** (`51b9c54`) — the descent face is a
  homomorphism into square classes on the whole point group at every modulus: the
  generic chord landings assembled through the group law, the three half-turn
  translations by their classical closed forms (`x ↦ −n²/x`, `x ↦ n(x+n)/(x−n)`,
  `x ↦ −n(x−n)/(x+n)`) with exhibited square-root witnesses, the six Klein chords
  settled symbolically with constants `1, 1/n, 1/(2n)`.
- **`theSlotClassesAreSupportedAtEveryModulus`** (`a97e987`) — every point's slot
  classes are supported on divisors of `2n`: off the primes of `2n` the curve forces
  both slot valuations even, so each squarefree part divides `2n`.  The face image is
  finite per twist, uniformly.
- **The assembly** (`6fd8eb7`) — one representative chosen per realized class (the
  finiteness makes the choice set finite, with height ceiling `H₀`); the homomorphism
  cancels a point's class against its representative's; the exact kernel halves the
  difference; duplication's quartic growth against translation's quadratic growth
  contracts the half strictly below the point once the height clears
  `16n⁶·C + 4n + H₀` with `C = 2((1+n²)(H₀+1))²`; strong descent generates from the
  bounded-height points, which are finitely many.

With the earlier family laws — exactness `ker(face) = 2E_n(ℚ)` both ways, the two
growth laws, the halving certificates, the family Gauss engine — **the algebraic side
of the family chart is closed**: no theorem on the descent side of rung 2 mentions an
instance any more.

## 3. What the coarse-graining measured today

The five-instance descent consumed three kinds of five-specific data: the eight
explicit representatives, the numeric thresholds (`163000`, `105800`, `250000`), and
the slot tables.  The family versions replaced all three with **existence produced by
finiteness** — representatives by choice over the finite face image, thresholds as
functions of the modulus and the chosen ceiling, tables by the support law.  The
instance's numerics were the compressed shadow of a uniform mechanism, exactly as the
certificates were; the descent's entire content coarse-grains with zero remainder.

## 4. What remains on the ladder, named

1. **The family theta functional equation** — the analytic side's remaining
   rung-2 assembly, over the standing family engine, with the sign law on residues
   mod 8.
2. **Per-twist rank pincers** — with Mordell–Weil and exactness family-wise, the
   per-twist rank upper bound is `|image|`-counting against the realized classes: a
   uniform certified computation per twist.
3. **The rank-zero ledger at one** — the AGM convergence from the mean step
   (`LandenLattice`) to the lemniscatic period, `L(1) = Ω/8`.
4. **The tower** — the norm relation at one prime step; then Rubin's mechanism closes
   analytic rank ≤ 1 for the whole CM family, which is where the Millennium
   statement's universal quantifier over this family is carried by growth rather
   than enumeration.
5. **The universality transport** — modularity, carrying the tower to every curve
   over ℚ; then the frontier rung at the knot's shared crossing.
