# The index statement is the reverse of Cauchy–Schwarz

**Date:** 2026-08-20
**Kind:** a consolidation, written at Brandon's direction to cool and sharpen after two waves. No
agents were used. It schedules nothing.
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction authorities.
**Position under the active plan.** Exterior mathematical material for Deed M2 of
[`blueprint/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md`](../../archive/plans/THE_SINGLE_CARD_PASSAGE_CARRIES_PHOENIX_AND_THE_MATHEMATICS_CODEC.md).
**No engine source is touched.**
**Truth status:** `proved-derived` throughout, kernel-checked and audited free of `sorryAx`.

---

## 0. The result

The two lines this consolidation focuses on turn on the same statement, and it is the **reverse** of
the inequality that makes the quotient work.

```text
Cauchy–Schwarz          <u,v>² ≤ <u,u><v,v>     positive semidefinite forms;
                                                 makes the null cone the radical, hence the quotient
the reverse inequality  <ω,v>² ≥ <ω,ω><v,v>     against a class of positive self-pairing;
                                                 IS non-positivity on that class's perp
```

```lean
theorem theReverseCauchySchwarzIsNonpositivityOnThePerp
    (q : LinearMap.BilinForm K V) (hq : q.IsSymm) (om : V) (hom : 0 < q om om) :
    (∀ x : V, q om om * q x x ≤ (q om x) ^ 2) ↔ (∀ w : V, q om w = 0 → q w w ≤ 0)
```

**An equivalence, not an analogy.** The index statement and the reverse inequality are one
hypothesis written twice. The backward direction is where the work is: decompose `x = tω + w` with
`t = q(ω,x)/q(ω,ω)`, which is why the statement needs a field.

Owner: `soma/formal/elementary-holonics/ElementaryHolonics/Millennium/LorentzianPerp.lean`, **12
theorems**, zero `sorry`, every one audited and depending only on `propext`, `Classical.choice`,
`Quot.sound`.

### And the two lines are the two instances

**The cycle line.** The Hodge index theorem says a surface's intersection form has signature
`(1, ρ−1)` — definite of one sign on an ample class and of the other on its perp — and the
Hodge–Riemann form on a matroid's Chow ring is the same shape on the primitive part, which
`crates/holonic-engine/examples/matroid_hodge_riemann.rs` prints as `P^k = ω^⊥`. Witnessed here on
a signature-`(1,3)` lattice with an ample-shaped class of self-pairing `24` that is not a basis
vector:

```lean
theorem theAmpleClassPays : lat amp amp = 24
theorem theAmplePerpIsNonpositive (w : Lat) (hw : lat amp w = 0) : lat w w ≤ 0
```

**And the proof is the forward inequality doing the reverse one's work.** `6w₀ + 2w₁ + 2w₂ + 2w₃ = 0`
forces `3w₀ = −(w₁+w₂+w₃)`, and then ordinary Cauchy–Schwarz on the three spacelike coordinates —
`(a+b+c)² ≤ 3(a²+b²+c²)` — gives `9·q(w,w) ≤ −6(a²+b²+c²) ≤ 0`.

**The arithmetic line.** The archimedean estimate `⟨ξ, N₂ξ⟩ ≤ γ|⟨ξ₀,ξ⟩|²` has a right-hand side
that vanishes on `ξ₀^⊥`, which is the whole mechanism, and the general form of that is a separate
theorem because **the bound is stated against a second form**:

```lean
theorem theBoundedFormIsNonpositiveOnThePerp
    (q p : LinearMap.BilinForm K V) (om : V) (g : K)
    (h : ∀ x : V, q x x ≤ g * (p om x) ^ 2) {w : V} (hw : p om w = 0) : q w w ≤ 0
```

No symmetry, no non-degeneracy, and no relation between `q` and `p`. **That is exactly why a
compression rather than a restriction is required** — the record this comes from says so in its own
words, *"the estimate does not require `N₂` itself to preserve `ξ₀^⊥`"* — and the finite instance
carries it, with the operator exhibited leaving the perp and the estimate's slack an exact square.

### The two inequalities genuinely point opposite ways

```lean
theorem theReverseInequalityHoldsOnThePlane (x : Plane) :
    mink tau tau * mink x x ≤ (mink tau x) ^ 2
theorem theForwardInequalityFailsOnThePlane :
    ¬ ((mink tau ((0,1) : Plane)) ^ 2 ≤ mink tau tau * mink (0,1) (0,1))
```

One carrier, one form, one pair. The reverse is not a weakening of the forward one, and the first
is obtained from the equivalence rather than recomputed.

---

## 1. What this consolidates

| held before | now |
|---|---|
| the archimedean compression, read but unmerged | merged as an instance of a general bound |
| the Hodge–Riemann primitive part, computed in Rust and described in prose | the same statement, kernel-checked on a lattice |
| Cauchy–Schwarz as the lemma used by the algebraic radical quotient | its **reverse** identified as the index statement, and the two proved to be opposite; this is not the full GNS construction |
| RH and Hodge as two lines that "share a shape" | one theorem with two named instances |

**Measured 2026-08-20** over `Mathlib` at `v4.27.0`:
`grep -rl "Lorentzian" Mathlib --include='*.lean'` returns **0 files**, and a sweep for a reverse
Cauchy–Schwarz returns nothing. Sylvester's law is present only over `ℝ`, for nondegenerate forms,
as a diagonalization in `Mathlib/LinearAlgebra/QuadraticForm/Real.lean` — not as a signature
invariant. Over `research/` and `canon/`, `grep -rlni "reverse cauchy\|reversed cauchy"` returns
nothing, and no document joins the Hodge index to the Weil/Sonin material. Those commands measure
those names over those scopes and are not claims that no related content exists under other names.

**No Cauchy–Schwarz is proved here.** The forward direction is mathlib's
`apply_mul_apply_le_of_forall_zero_le`; this file proves only its reverse and the equivalence.

---

## 2. Boundaries

Nothing here is a claim about any named conjecture. The instances are a two-dimensional Minkowski
plane and a four-dimensional lattice; no curve, divisor, correspondence algebra, Frobenius,
L-function or cycle class map appears, and neither the Hodge conjecture nor the Riemann Hypothesis
is approached. What is formalized is the linear algebra that both classical arguments pass through,
and the classical inputs — that an ample class supplies a positive form through the Rosati
involution, and that the archimedean estimate holds — are imported, cited, and not proved here.

The equivalence needs a field, because its backward direction divides by `q(ω,ω)`; the version over
an ordered ring is not stated. `Millennium/` stands at **19 files, 4,376 lines, 222 theorems**, zero
`sorry`; the library builds at 3,297 jobs; the atlas at **173 equations, 161 relations**, no
dangling endpoints.
