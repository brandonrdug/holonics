# Shadows of holonic interactions

**Date:** 2026-08-20
**Kind:** the four steps, taken. No agents were used. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
**No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.
**Provenance.** Brandon named the framing — a shadow is a projection, after Tufte's *Shadows of
Feynman Diagrams* — and directed that the Holonic Interaction be formalized as an optical object
through the cross-ratio swing.

---

## 0. The identification that orders the rest

[definition; source-inspected] September 10 scope correction: a receiver projection preserves
collinearity and cross-ratio on a line where its restriction is a nondegenerate projectivity.
It can coalesce source points, and metric quantities are not generally preserved; special
restrictions can preserve some. The earlier blanket “every metric quantity dies” wording was
too strong. The formal owner proves the bilinear identities below, not a general projection theorem. So the projective content of the positivity work is where its invariants live, and the
identification is classical and exact:

> **A nondegenerate symmetric form induces a projective polarity. Two classes are conjugate with respect to the quadric
> `q = 0` exactly when `q(ω,w) = 0`. So the perp relation the reverse inequality is about IS
> conjugacy with respect to a conic — and the swing is its involution, not a neighbouring topic.**

Along `ω + t·w` with the two conjugate, the cross term drops out and the form is **even in `t`**:

```lean
theorem theConjugateLineIsEvenInItsParameter (hq : q.IsSymm) (h : Conjugate q om w) (t : R) :
    q (om + t • w) (om + t • w) = q om om + t * t * q w w
theorem theSwingExchangesTheNullParameters (t : R) : Swing.swing (0 : R) t = -t
theorem theAnchorAndTheDirectionAreHarmonic (t : R) : 2 * (0 : R) - t - (-t) = 0
```

Over the real numbers, with opposite nonzero signs on the conjugate directions, the null
parameters are `±t₀`; the swing about `ω` exchanges
them; and `harmonicConjugate`'s denominator vanishes there, which is the projective statement that
the harmonic conjugate of the anchor is the point at infinity. **Cross ratio `−1`, and the
configuration is the optical one: a class, a direction, and the two rays.** Where the form pays on
the class and fails on the perp, `t·t > 0` — the rays are real, and the interaction has two of them.

---

## 1. The equivalence needs no field, and the denominator it drops is the invariant

```lean
theorem theReverseInequalityOverAnOrderedRing
    (q : LinearMap.BilinForm R V) (hq : q.IsSymm) (om : V) (hom : 0 < q om om) :
    (∀ x, q om om * q x x ≤ (q om x) ^ 2) ↔ (∀ w, q om w = 0 → q w w ≤ 0)
```

The backward direction clears the denominator by hand with `u = d·x − q(ω,x)·ω`, where
`q(u,u) = d²q(x,x) − d·q(ω,x)²`. **That vector is the whole of the next step**, so removing the
field hypothesis is not tidying — the division was hiding an invariant.

## 2. Over a lattice the residue is a reachable-only-in-a-multiple defect

`q(ω,ω)·x` always lands in `ℤω ⊕ ω^⊥`; `x` need not. On `diag(1,−1,−1,−1)` with the ample-shaped
class `ω = (6,−2,−2,−2)` of self-pairing `24`:

```lean
theorem theClassIsNotInTheIntegralSpan :
    ¬ ∃ (t : ℤ) (w : ZLat), zl zamp w = 0 ∧ zx = t • zamp + w
theorem theFourfoldIsInTheIntegralSpan :
    zl zamp ((-2,2,2,2) : ZLat) = 0 ∧ (4:ℤ) • zx = (1:ℤ) • zamp + ((-2,2,2,2) : ZLat)
theorem theFactorDividesTheSelfPairing : (4 : ℤ) ∣ zl zamp zamp
```

Pairing `x = t·ω + w` against `ω` gives `6 = 24t`, which no integer solves; four times the class
splits exactly, and `4 ∣ 24`. **This is the shape
`ObstructionSpecies::ReachableOnlyInMultiple { factor }` returns in the engine**, which the
operating contract calls a faithful finite model of Kollár's counterexamples — a class reached at
multiplicity `p` and not at `1`. Both sides are now exact and computable, and **the obstruction is
invisible to a field**, which is exactly why the integral Hodge statement fails where the rational
one is open.

## 3. The sign and the factor are independent obstructions

| lattice | perp | splitting |
|---|---|---|
| signature `(1,3)`, self-pairing `24` | **definite** — no sign failure | fails by **4** |
| signature `(2,1)`, self-pairing `1` | **indefinite** — carries both signs | splits **every** class |

Both directions witnessed, so neither bounds the other. *Failing by an amount* and *failing by a
factor* are different objects — which is the precise sense in which the Hodge obstruction is a
cokernel and not torsion, arrived at from inside rather than quoted.

## 4. Placement needs the form to see the ray

```lean
theorem theStretchIsPlacedWhereTheSelfPairingSurvives
    (hT : ∀ x y, q (T x) (T y) = c * q x y) (hv : T v = lam • v) (hnz : q v v ≠ 0) :
    lam * lam = c
theorem theSqueezeIsAnIsometry (x y : Pl) : hyp (squeeze x) (squeeze y) = 1 * hyp x y
theorem theStretchedRayIsIsotropic :
    squeeze ((1,0) : Pl) = (2:ℚ) • (1,0) ∧ hyp ((1,0) : Pl) (1,0) = 0 ∧ (2:ℚ)*2 ≠ 1
```

**The operative hypothesis is a nonzero self-pairing on the ray, not positivity of the form.** The
control is an honest isometry — the squeeze `(x,y) ↦ (2x, y/2)` preserves the hyperbolic form
exactly, `c = 1` — that stretches a null ray by two. Preserving the form places nothing; the form
having something to say **on that ray** is what places it. That supersedes the earlier reading in
which positivity was credited with the work.

---

## 5. What is now standing on the two lines

| | |
|---|---|
| forward Cauchy–Schwarz | the algebraic radical quotient (`AlgebraicGNS`) — a `conditional` GNS middle step, not a Yang–Mills precondition |
| its reverse | the sign on the perp (`LorentzianPerp`) — the Hodge index |
| the denominator the reverse needs | the integral obstruction (`Shadows` §4) — Kollár's cokernel |
| an operator preserving the form | the placement (`Shadows` §7) — Weil |

**Four Millennium-facing analogies out of one symmetric form and one distinguished class**, with
the swing as the projective primitive underneath all four. The rows are `interpretation`; no
Millennium conjecture is formalized or advanced by this record.

## 6. Boundaries

Nothing here is a claim about any named conjecture. The carriers are a plane, a rank-three and a
rank-four lattice; no curve, divisor, cycle class map, Frobenius or L-function appears, and the
classical inputs — that an ample class supplies a positive form through the Rosati involution, and
that the archimedean estimate holds — are imported, cited and not proved.

Two limits are worth naming. The finite quotient `L/(ℤω ⊕ ω^⊥)` is exhibited at one class on one
lattice and is not constructed as a group with its exponent proved in general. And the placement
statement is about stretches **realized in the base ring on a base-ring eigenvector**; the complex
spectral statement `|λ| = √q` is not reached, and mathlib's machinery for it has not been located.

**Measured:** `Millennium/` is **20 files, 4,656 lines, 241 theorems**, zero `sorry`; the library
builds at 3,298 jobs; every theorem in `Shadows.lean` audits clean. The atlas stands at **177
equations, 163 relations**, no dangling endpoints.
