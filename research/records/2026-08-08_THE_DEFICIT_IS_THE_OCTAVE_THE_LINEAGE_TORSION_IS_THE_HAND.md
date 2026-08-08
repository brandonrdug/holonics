# The deficit is the octave, the lineage torsion is the hand

**Date:** 2026-08-08
**Truth status:** `established-bounded` for the separation and for every figure in §2 — two
independent implementations agree and the falsifier is executable. `interpretation` for §5's naming
and §6's physics reading, which is a **refusal** and is graded as one.
**Evidence:** `computational-witness`. `cargo run -p holonic-engine --example
grown_circuit_schedules`, re-run by this session and read directly, not taken from a report; plus a
from-scratch Python Smith-normal-form implementation that imports nothing from the crate, run by the
sub-agent. Direct source inspection of `discrete_curvature.rs`, `derivation_curvature.rs`,
`grown_cell.rs`, `rebase_invariants.rs`, `derivation_integral.rs`, `supported_realizers.rs`.
**Provenance.** The question — *is the grown circuit's `Z/2` a deficit angle, a Bockstein, or
unrelated* — was posed by this session after measuring that a netlist-only receiver returns `H₁ = Z⁹`
where the whole returns `Z⁹ + Z/2`. Investigated by a permitted sub-agent. **The verdict below was
re-established here from the example's own output**; the agent's report is a search return, not
authority. The §2b framing is Brandon's, derived with him this session.
**Band:** 2026-08-08 · IDENTIFICATION REFUSED WITH A WITNESS / TORSION CREATED WITH EVERY DEFICIT
FIXED / THE ONE ROW WHERE THE IDENTITY HOLDS IS A TAUTOLOGY AND ITS FALSIFIER IS ONE APERTURE AWAY /
THE TREE'S HOLONOMY CARRIER IS PROVABLY BLIND TO THE CLASS ITS INVARIANT CARRIER FOUND / SOURCE
UNCHANGED

---

## 1. The verdict

**Unrelated as the two organs stand, and the separation is an impossibility rather than a failed
measurement.**

`DiscreteCurvatureConfiguration` holds vertices, edges, and one `Rat` per edge — no faces, no
boundary matrix, no chain complex. `deficit()` sums the responses incident to a vertex and subtracts
`FLAT_COORDINATION = 6`. So the deficit functional **factors through the 1-skeleton**, and no choice
of response can make it see a 2-cell. `derivation_curvature.rs` says so twice by refusing: it
rejects any complex carrying a cell of grade > 1 (`UnreadGrade`), and rejects parallel incidence,
which the grown complex has 21 pairs of at Brent–Kung width 2.

The lineage torsion is `T(coker ∂₂)`, read from the Smith normal form of the attaching map of the
division 2-cells. The two organs read disjoint data.

## 2. The falsifier, re-run here

`cargo run -p holonic-engine --example grown_circuit_schedules`, width 2, the same body read at two
apertures:

```
brent-kung-adder / division   nets 18  arcs 78   faces 52   betti 9   torsion Z/2
brent-kung-adder / both       nets 18  arcs 78   faces 59   betti 3   torsion Z/2+Z/2+Z/2+Z/2+Z/4+Z/4

multiplexer      / division   nets  9  arcs 21   faces 12   betti 1   torsion —
multiplexer      / both       nets  9  arcs 21   faces 13   betti 0   torsion Z/2
```

**The 1-skeleton is identical down the pair.** Same nets, same arcs, same incidence — so every
vertex deficit is identical and `Σ_v K(v) = 6|V| − 2|E|` is identical at unit response. Only the face
population differs. The torsion moves anyway, and the multiplexer moves it **from nothing to `Z/2`**.

Torsion is created out of nothing with every deficit angle held fixed. That is not a weak
correlation; it is the functional dependence being wrong.

Three further readings, all from the same output:

- **`Σδ = 6χ` holds in exactly one row and it is a tautology.** It requires `F = 2E/3`, the closed
  triangulated surface relation. Brent–Kung w2 division satisfies `52 = 2·78/3` by accident. It
  breaks at width 3, at the other aperture, and on every other cell. **The one place the
  identification appears to work is `CLAUDE.md` §8's tautology rule firing**, and its falsifier is
  one aperture away.
- **`k > 1` is necessary and not sufficient.** Ripple carries **0** faces with `k>1` and has no
  torsion at any width — a carry chain never reconverges. Multiplexer w2 division carries **1** face
  with `k>1` and `largest coefficient 2`, and has **no torsion at all**.
- **The grown complex is not a manifold**, so Regge calculus does not apply to it even to give
  Gauss–Bonnet. Cofaces per 1-cell at brent-kung w2 division: `{1:28, 2:36, 3:11, 4:1, 5:2}`; a
  closed surface needs every 1-cell in exactly two.

And the classical control settles it independently of this body: the torus and the Klein bottle both
have `χ = 0`, hence identical total deficit by Gauss–Bonnet, and torsion in exactly one. Both admit
`{3,6}` triangulations where **every** Regge deficit is exactly zero. Deficit angles are blind to
torsion in the setting where they are *defined*. The reason is one sentence: the deficit's only
topological content is `χ`, `χ` is an alternating sum of ranks, and ranks land in a torsion-free
group.

## 2b. The width law, measured after the cost wall came down

**Added the same day.** The width sweep was unreachable while `PivotRule::FirstNonzero` was the
default; with `SmallestMagnitude` the whole sweep is **43 ms**. Re-run and verified by this session,
not taken from a report:

```text
w=2  betti  9   torsion rank  1   (w-1)^2  1   every factor 2
w=3  betti 15   torsion rank  4   (w-1)^2  4   every factor 2
w=4  betti 21   torsion rank  9   (w-1)^2  9   every factor 2
w=5  betti 27   torsion rank 16   (w-1)^2 16   every factor 2
w=6  betti 33   torsion rank 25   (w-1)^2 25   every factor 2
```

**`H₁ = Z^{6w−3} ⊕ (Z/2)^{(w−1)²}`, exactly, at every width measured.** The torsion subgroup is
elementary abelian — no `Z/4` ever appears at the `DIVISION` aperture — and the free rank is identical
in the netlist section, so `i_*` is rank-preserving throughout.

**This hardens §2 from "measured disagreement" to "different growth laws."** Torsion rank is exactly
quadratic in the width. `Σδ = 6V − 2E` is `−48, −118, −196, −304, −420` — second differences
`−8, −30, −8`, the irregular arc of a prefix adder. `6χ` is exactly linear, `−36w + 24`. Three
functions of width, three growth classes, and the two curvature-side ones track each other far more
closely than either tracks the torsion. **The `Σδ = 6χ` coincidence at `w = 2` is now visibly the
isolated accident §2 called it.**

**And the census would have given the wrong answer at every width.** Faces carrying `k > 1` go
`8, 18, 28, 44, 60` against torsion ranks `1, 4, 9, 16, 25` — not proportional, not affine. Counting
reconvergent divisions does not predict the torsion; only the Smith reduction does. `CLAUDE.md` §9's
*return the artifact, never the census* as a measured fact.

`(w−1)²` is the count of internal group-carry reconvergences in a Brent–Kung prefix tree — the
propagate/generate pairs meeting at a shared carry, which is what `k = 2` marks and what the width-2
generator exhibited as a square of two sources against two carries. **The torsion counts those
squares.** Nothing about `6 − deg(v)` produces a perfect square in the width, and nothing about a
deficit distinguishes a reconvergent carry from a rippled one — ripple returns zero torsion at every
width while its deficits are as large.

## 3. The Bockstein, both halves

**The tautological half.** From `0 → Z →^2 Z → F₂ → 0`, exactness gives
`im(β) = H₁(X;Z)[2]`. So the `Z/2` *is* a Bockstein image, necessarily, for any space with 2-torsion.
Measured and consistent — `dim H_*(X;F₂) = [1,10,1]` against `dim H_*(X;Q) = [1,9,0]`, and `F₃`, `F₅`
agree with `Q`, so the torsion is purely 2-primary. All of that is the universal coefficient theorem
restating itself. Per §8 it is `definition`, not evidence.

**The substantive half — is the source visible to the netlist receiver? No, and it is closed from
both directions.** `primitive_section` admits nets and gate pins only, so the section has **no
2-cells** and `H₂(S;R) = 0` for every coefficient ring. And `H_*(X, S; Z)` returns `H₂ = 0`, which by
the long exact sequence makes `i_*: H₁(S) → H₁(X)` **injective** — an injective image of a
torsion-free `Z⁹` is torsion-free. **No cycle supported on gate pins represents the `Z/2`.** That is
a proof, not a measurement.

**One correction to this session's own earlier phrasing.** *"The torsion is exactly the lineage's
contribution"* is right in spirit and wrong as arithmetic. The isomorphism types differ by a `Z/2`,
but the **map** has `coker(i_*) = (Z/2)⁴ ⊕ (Z/4)²`, order `2⁸`, so `i_*(Z⁹)` sits at index 128 inside
the free part. And the multiplexer separates the two notions outright: at division width 2,
`coker(i_*) = Z/2` while `H₁(X)` is torsion-free. **A `Z/2` in the aperture cokernel and torsion in
`H₁` are different objects, and this body produces one without the other.**

## 4. The artifact

The torsion generator at brent-kung w2 division, recovered from the Smith reduction and verified
(`∂₁z = 0`, `z ∉ im ∂₂`, `2z ∈ im ∂₂`):

```
z =  arc:i1:0->2  −  arc:i1:2->2  −  arc:i2:0->1  +  arc:i2:2->1
     net 1 → net 8   net 3 → net 8   net 1 → net 7   net 3 → net 7
```

Four lineage boxes, **zero gate pins**. It is a square: two sources — a data input and the carry-in —
each conducting to two group carries, read once through the parent's black box and once through the
child's. **The class is the difference between how a parent conducts a pair of ports and how its
child conducts the same pair**, and that difference exists only in the lineage direction.

Solving over `F₂` for a cocycle vanishing on all 52 face boundaries and pairing to 1 with `z`
returns a support of **size one**: the indicator of `arc:i1:0->2`, the single arc that occurs in one
face boundary with coefficient **2** — the face the example prints in full. So the whole `Z/2` is the
**parity of the two-path reconvergence at the top-level division**: Brent–Kung's propagate and
generate both reach the same group carry, `k = 2`. And `k` is not a modelling choice — `∂∂ = 0`
forces `c = k`, and `algebraic.rs` refuses `BoundarySquaredNonzero`.

## 5. What it is, in this project's own vocabulary

Not curvature. **`ObstructionSpecies::ReachableOnlyInMultiple { factor: 2 }`**, at
`supported_realizers.rs:108`, whose module doc already says it:

> *"A class reached only as `2·c` and never as `c` is supported over the rationals and unsupported
> over the integers, and the cokernel records a `Z/2`. That is the integral-versus-rational split the
> Hodge conjecture fails on."*

**It was written as an analogy and the grown circuit makes it an instance.** A body that grew its own
material by size-agnostic recursion, with no width parameter and no authored complex, produced a
class reachable at multiplicity 2 and not at 1, with the multiple exhibited and the generator named.
`CLAUDE.md` §3's Kollár sentence — *"the passage exists at multiplicity `p` and not at 1"* — is the
same sentence. And §3's own correction is the one to honour: **the uniform object is the cokernel,
not torsion**, which is why §3 above distinguishes the two cokernels and why the multiplexer, which
exhibits one without the other, is the sharper fixture.

Structurally it is a **degree-`k` covering monodromy in the lineage direction**: the parent's
black-box arc is covered by `k` refinement paths, and when the refinement admits no compatible
halving over `Z`, the class exists over `Q` and not over `Z`. That is `⟨a | a²⟩` localized at one
arc, which is why `rebase_invariants`' own archetype test is called
`a_doubled_boundary_returns_torsion_that_a_rational_rank_cannot_see`.

## 6. The physics reading, which is a refusal

`CLAUDE.md` §2b supplies the distinction that makes this precise rather than merely negative:

> *"`4 = 2·2` are different currencies: the octave (2:1, magnitude, one rank step) and the hand (one
> quarter-turn, phase, costing no action). On the unsigned floor the phase factor is INVISIBLE, so
> both factors were booked as magnitude."*

**The deficit is the octave; the lineage torsion is the hand.** The deficit is a magnitude density
whose only topological content is a rank. The torsion is a winding that survives only modulo `k` —
a passage that exists at multiplicity 2 and not at 1. Identifying them is exactly the error §2b
names: booking a phase factor as magnitude because the floor deleted the turn.

So the true statement about grown structure is not *"curvature concentrated on the acts of
division."* It is: **cell division deposits winding, and the winding is finite-order.** Material that
never reconverges deposits none — ripple, every width, measured. Material that reconverges deposits
`k`-fold covers of its parent's conductions, and the part of that cover with no integral section is
the torsion.

## 7. The obligation this creates, and it is concrete

`derivation_integral` retains its chord obstructions as `BigInt` and `Rat`. A `Z`- or `Q`-valued
holonomy is a homomorphism out of `H₁`, and `Hom(Z/2, Z) = Hom(Z/2, Q) = 0`. **The tree's holonomy
instrument is provably blind to the class the tree's invariant instrument just found**, and the two
live in the same crate.

That is not a wall. It is a missing carrier: a `Z/n`-valued chord test. The prototype above is four
lines of `F₂` elimination, and it already returned a detector of support one.

## 8. What would falsify this verdict

1. **Exhibit two grown complexes with identical integral homology and different `Σδ` at unit
   response** — the converse direction is already exhibited above. To break the verdict you must
   break the factorization, i.e. find a place where a deficit is computed from a 2-cell.
   `DiscreteCurvatureConfiguration` has no field that could hold one.
2. **Realize the grown complex as a closed pseudomanifold and show its cone-point orders reproduce
   the invariant factors.** This is the only route by which "same object" could become true — the
   2-orbifold statement, where a cone point of angle `2π/n` contributes `Z/n`. Predicted to fail,
   because the torsion moves while every vertex degree is fixed.
3. **Find an integer-valued cocycle pairing non-zero with the torsion class.** Five lines, and it
   would contradict the Smith computation.
4. **Show `coker(i_*)` is not 2-primary at some width.** `largest_face_coefficient` is 2 at widths
   2, 3 and 4, so an odd invariant factor there would kill the parity reading.

**Scope.** Nothing here bears on RH or Hodge. The connection drawn is that a grown body produced a
concrete instance of a species this tree already declares, and the species is
`ReachableOnlyInMultiple`, not curvature. Repository unchanged by this investigation.
