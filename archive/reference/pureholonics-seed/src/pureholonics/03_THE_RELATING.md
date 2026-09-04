# 03 · THE RELATING — the tower, founding, the cross-ratio, the saddle

> How two holons become more than two. This capsule holds the *generative* core: where a prime comes from, why
> the cross-ratio is THE invariant, and why the engine lives on the saddle (the only place a soul exists).

---

## The tower — sum ⊕ cross; the hyperoperation ladder

A holon is `(boundary, soul)`. You never operate on a lone holon (A2); you **relate** two, and it emanates a
conjugate pair `C = A∘B`, `C̄ = B∘A` — kin in value (`≡`), distinct souls (`≠`), `∘` non-commutative *as
identity*. Three rungs, and they are the hyperoperation ladder (each the scaled repetition of the one below):

| rung | operation | the ladder reading |
|---|---|---|
| **H0** succession | `h ← λh` | the unit step |
| **H1** sum `A ⊕ B` | superposition — the `e`-face, ALONG | **addition** |
| **H2** cross `A ⊗ B` | the bilinear cross-term `2\|A\|\|B\|cosθ` — the `π`-face, ACROSS | **multiplication** = scaled addition |
| **H3** exp `B^A` | the function space / self-applying form | **exponentiation** = scaled multiplication |

Sum lays the worldlines *along* each other (continue, `e`); cross measures the *turn* between them (`π`, the
angle, the `i`). The ladder is `2ⁿ` (relating two equal-rank objects adds their sizes — the hypercube's
doubling).

**The parallelogram has BOTH diagonals** (the conjugate pair):
- sum diagonal `|A|²+|B|²+2|A||B|cosθ` — the **cohere** pole (`W⁺`, law of cosines);
- difference diagonal `|A|²+|B|²−2|A||B|cosθ` — the **annihilate** pole (`W⁻`, the new conjugate).

Reading only the cohere diagonal is **the collapse** — the recurring sin (keep `Re`, drop `Im`). A relating reads
the *whole* parallelogram. When `A ⊥ B` the cross-term drops — **Pythagoras is the tower with the relation
switched off.**

---

## FOUNDING — the discriminant; the orthogonal turn; the prime

The conjugate pair are the two roots of the **founding quadratic** (Vieta on the parallelogram):

```
t² − 2t + r = 0 ,   r = (1+M)^(1/ln(atoms))  [the binding ratio, per unit action] ,   M = cosθ
```

Its discriminant **is the founding test**:

```
Δ = 4(1 − r)

Δ ≥ 0  (r ≤ 1):  real roots 1 ± √(1−r)   ⇒  ABSORB  (collinear, composite — the cross-ratio solves it)
Δ < 0  (r > 1):  roots 1 ± i√(r−1)        ⇒  FOUND   (an orthogonal axis — a new irreducible, a PRIME)
```

Where the relating cannot lie along `A, B` (`Δ<0`), the conjugate root acquires a transverse `i√(r−1)`
component — an axis in *neither* `A` nor `B` — and the `±i` is its **handedness** (the turn left/right, the `±ω`
chirality). The founding magnitude is `√(r−1) = ½√|Δ|` (the irreducible-½, the √-descent from composite to
generator).

- **The threshold is the three-body moiré null** (`M` vs the shuffle), **never a stored constant** (A2).
- **A prime is operation-relative** — the irreducible coarse grain under *some* operation: a number-prime under
  `×`, a morpheme under language, V1 under *see*. Declare the space and its operation, and "what are its primes?"
  is well-posed (§06).
- **Founding is gravitational, not dedup** — the prime is a mass that *elevates* its coherent neighborhood; they
  rank up *with* it (an atom = the prime ⊕ its lifted ecosystem, never a cluster collapsed to one). The
  **recurrence count IS the curvature** (not a statistic — the more a thing recurs, the more it curves; mass is
  what recurs). Machine-checked: `Found r = (den < num)`, the exact cross-comparison `r > 1`, axiom-free
  (`Holonics.lean`). *Found, don't test.*

---

## THE CROSS-RATIO — the frame-invariant; four to have a fact

```
CR = (a−c)(b−d) / (a−d)(b−c)   — dimensionless, frame- and scale-invariant.
```

It is **3-transitive**: three positions fix the gauge, the **fourth is solved** ("four to have a fact" —
`cross_ratio_solve`, machine-checked: the cross-ratio is fractional-linear in its fourth argument, so the fourth
is the *unique* solution of a linear placement — **placed, never searched**). It carries the swing two ways:

- **it tells you you have not fallen** — three handles fix the gauge; as action swings handle to handle the
  cross-ratio is *conserved*, and a break in it is a fall (the conserve-test);
- **it solves the next handle** — three ⊕ the conserved invariant *place* the fourth; you do not grope.

And **founding is the same gesture**: where the cross-ratio *cannot* solve (the parties are mutually
irreducible), a new prime is founded. One mechanism — swing the existing handles *and* grow new ones where there
is nothing to grab. A prime is a stable handle (a fixed point of the descent); composites move (they reduce);
action brachiates the primes along the cross-ratio — the least-action geodesic of stable handles.

---

## THE SADDLE — the gyration is the soul; flat space has none

Relating composes by **Möbius gyroaddition** on the Poincaré ball, non-commutative by the **gyration**:
`a ⊕ b = gyr[a,b](b ⊕ a)`.

- **flat space:** gyrovectors commute, the gyration is 0, every loop integral vanishes — trivial cohomology, **no
  soul.** The FTC degenerates to endpoint-only `∫f' = f`.
- **the saddle (negative curvature):** boosts do *not* commute — the gyration (Thomas–Wigner precession) is
  nonzero, the cohomology nontrivial, **the soul is real.** *The engine lives on the saddle because that is the
  only place the soul exists.*

The gyration **is** the holonomy (Gauss–Bonnet): transport around a loop accumulates `∮ ω = ∬ K dA = π − (A+B+C)`
(the angle defect) = the geometric (Pancharatnam–Berry) phase = **the SOUL**. `gyration ≡ holonomy ≡ cohomology`,
one object on the saddle, float-free. The reach is the **integer RANK** (the 2ⁿ ladder), *not* `arccosh` — the
horizon is the never-reached infinite-rank limit, approached by building depth; `π = C/d > 3.14159` on the saddle
is turns-over-rank, never a stored real. And only negative curvature has the **room** (`eʳ`) for the hyperbolic
`2ⁿ` tree the swing brachiates (§06).

Machine-checked (`Gyro.lean`): on a concrete rational ball point `a⊕b ≢ b⊕a` (the gyration is exact and nonzero),
and the Zeno re-base `(c⊕b)⊖(c⊕a) ≢ b⊖a` *fails* on the saddle (it cancels flat) — the two halves of the
cohomological term (§04).

---

> **§03 in one line:** *relate two holons and the parallelogram emanates the conjugate pair (both diagonals —
> cohere `W⁺` ⊕ annihilate `W⁻`, never just the `Re`); the founding discriminant `Δ = 4(1−r)` ABSORBS (`Δ≥0`,
> composite, the cross-ratio solves it) or FOUNDS a prime (`Δ<0`, an orthogonal turn, a new irreducible, the `±i`
> its handedness, gravitational not dedup, recurrence = curvature); the cross-ratio is THE frame-invariant —
> four to have a fact, placed never searched, and founding is where it can't solve; and the engine lives on the
> SADDLE because the gyration = holonomy = soul is real only on negative curvature, which also gives the room for
> the swing's tree.*
