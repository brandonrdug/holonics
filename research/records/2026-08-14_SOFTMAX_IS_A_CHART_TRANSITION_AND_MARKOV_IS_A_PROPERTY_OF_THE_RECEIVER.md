# Softmax is a chart transition, and "Markov" is a property of the receiver

**Date:** 2026-08-14
**Genre:** research record
**Truth status:** `proved-standard` for the group law and the fundamental theorem it rests on;
`implemented-exact` and `measured` for everything returned; `interpretation` for the reading of
softmax's statistical use as a receiver face.
**Occasion:** Brandon directed that our chains be recognized as Markov chains and that softmax be
read ontologically so a holonic analogue could be derived. He then corrected the first framing —
which had softmax as *a statistic with the division removed* — to the right one.

---

## 0. The correction that set the ontology, verbatim

> *"softmax doesn't actually seem like a statistics function to me, it seems like it's merely
> associated with statistics and got grouped in. That seems like a valid mathematics invariant
> property, like how we recognize pi and e, no? It's not that you're doing something invalid, you're
> literally setting the invariant property to be that `f(x) = softmax(x) = (chart of Λ) /
> (infinitesimal discrete paths/arcs that compose Λ)`, because of the exponentiation, no? Like `C/r`
> in our modifications of Einstein's equations. … It's a rebasing thing, it's not a statistics
> thing."*

The first framing had the mechanism right and the **species** wrong. Getting the species right
changes what the organ is for.

---

## 1. The exponential is the arc-to-whole map

```text
e^x = lim_{n→∞} (1 + x/n)^n
```

is exactly *compose `n` infinitesimal arcs of size `x/n` multiplicatively and return the whole*. So

- `x` lives in the **additive chart** — the per-step, the infinitesimal, the tangent;
- `e^x` lives in the **multiplicative chart** — the accumulated, the whole, the group element;
- **`exp` is the transition between them**, which is the Lie exponential `𝔤 → G`.

Nothing statistical is involved anywhere in that.

**`C/r` is the same species, and this is why the analogy is an identity rather than a resemblance.**
For the circle the additive chart is the angle and the multiplicative chart is `e^{iθ}` on the unit
circle. `2π` is **the additive extent that closes the multiplicative loop.** So:

> **π and `e` are the two constants of one chart transition.** π is how much extent closes it; `e` is
> the base that makes it natural, the one for which the transition is its own derivative.

Neither is a statistic, and the framework already recognises them as invariants of exactly this kind.

---

## 2. Why the transition closes exactly on this body's carrier, which is not luck

**`ℚ⁺` is the free abelian group on the primes.** That is the fundamental theorem of arithmetic
stated as a group law: the multiplicative chart of the positive rationals has the primes as its
generators, and every positive rational is one word in them.

`log₂` is the isomorphism onto the additive chart — a ℚ-vector space with `{log₂ p}` as a basis —
and the ℚ-linear independence of that basis is precisely what makes the additive chart's zero test
exact, which `surprisal.rs` already states and proves by unique factorization.

**So `SymbolicSurprisal` is not a Shannon organ. It is the additive chart of `ℚ⁺`**, and `−log p` is
one receiver's reading of it. The corollary:

```text
   additive chart          log₂           multiplicative chart
   Σ q_k · log₂ p_k     <---------->      Π p_k^{q_k}
   ℚ-linear form           exp            an exact rational

   a + b                                  exp(a) · exp(b)
```

**The homomorphism law is the whole content**, and it is what distinguishes a chart transition from a
statistic: a statistic has no such law. Built and checked —
`exp(a+b) = exp(a)·exp(b)`, `exp(0) = 1`, and the same law read backwards as `S(pq) = S(p) + S(q)`.

A **fractional** coefficient does not fail; it lands in a **finer chart**, the algebraic extension,
which is what a root is. The organ refuses it by name rather than enclosing it, because an enclosure
would be a magnitude standing in for a chart it has not entered.

---

## 3. Softmax, read in that chart

```text
softmax(x)_i = e^{x_i} / Σ_j e^{x_j}
```

Three facts, and only the last is usually said:

1. **Invariant under `x → x + c`** — the absolute position in the additive chart is **gauge**, and
   only differences transport.
2. **`p_i/p_j = e^{x_i − x_j}`** — the transition applied to a difference. That is the whole of its
   work.
3. **`Z` is a declared null** fixing the total at one. It enters no ratio and it is the only division.

So **softmax factors as a chart transition, then a gauge fixing.** Its statistical use is one
receiver's face of that; the content is the rebase. And by this project's own law the transition is
the invariant while the normalisation is the absolute-volume violation — *every measure must be a
ratio against a declared null so the Jacobian cancels*. **Softmax divides by `Z`; the holonic analogue
holds the pair.**

**Temperature is a root on the ratio.** `softmax(x/T)` sends `r → r^{1/T}` — a rebase of the winding,
and the *same* operation that carries a fractional coefficient into the finer chart. `T = 1` is the
identity; `T → ∞` sends every ratio to one, which is no distinction at all; and **`T → 0` sends
ratios to zero or infinity, which is argmax.**

> **That limit is exactly where softmax becomes a governor**, and the standing ban on a privileged
> scalar chooser is the ban on taking it. The organ never takes it: every member's ratio against
> every other is returned and none is discarded.

---

## 4. "Markov" is a property of the receiver, not of the material

`receiver_exact_compression::compress` refines a one-shot reading to the coarsest partition for which
conduct is determined by the block. **That is the causal-state construction** — a state is a set of
histories with identical futures — so **the machine already computes the minimal Markov model of its
material.** It simply never used the word.

And the memory order follows without a new organ. A one-shot reading merges two items; conduct
separates them; the **shortest word that does it** is how far ahead the reading had to look. So

> **the memory order is the longest shortest-distinguishing-word over the collapsed population**, and
> it is the Markov order of the pair `(material, receiver family)` rather than of the material.

A process is not Markov or non-Markov by itself. It is Markov **relative to a declared state map**,
and the collapsed-pair population **is** the non-Markovianity, already exhibited by name with its
depth attached. `memory_order`, `is_markov_at` and `beyond_order` are readings on what was already
returned.

`None` for the order is a **genuine zero and not a missing measurement** — nothing collapsed, so no
history was needed — which is why it is `None` rather than `0`.

---

## 5. What was built, and what it returned on real material

| owner | what |
|---|---|
| `crates/holonic-engine/src/exponentiated_ratio.rs` | the chart transition. `exponentiate`, `probability_ratio`, and `RatioFamily` — every member's exact ratio against every other, normalising only when a caller **names a null**. |
| `crates/holonic-engine/src/receiver_exact_compression.rs` | `memory_order`, `is_markov_at`, `beyond_order` — readings, no new computation. |
| `soma/life/examples/the_chain_is_markov_and_the_softmax_is_a_ratio.rs` | both, on one real chain. |

The chain is this repository's own tablets decomposed at a declared grain: part follows part.

**Reading one.** The same material read through two declared receiver families — one seeing a part's
length, one seeing length and first symbol — **returned different memory orders.** The material did
not change, so the order is saying something about the receiver and not about the chain.

**Reading two.** The widest transition row has **102 distinct successors**. Its ratio family:

```text
  the ratios compose over every triple                     true
  the declared null does not move the induced distribution true
  the weights sum to exactly one over the rationals        true
  a temperature rebase moves the family and stays a cocycle true
```

with exact rationals throughout — `p(declared␣)/p(material␣) = 1/2`, and so on — **no float, no
logarithm evaluated, no enclosure, and no normalisation until a null is named.**

The return is a **cocycle**, not a distribution: `r(i,j)·r(j,k) = r(i,k)` identically, which is the
algebraic statement that the absolute values were gauge — any two value assignments consistent with
these ratios differ by one overall factor and nothing else.

---

## 6. What this does not claim

Not that softmax is *wrong* — it is a chart transition composed with a gauge fixing, and both halves
are lawful. What is refused is reading the composite as a statistic and then letting its `T → 0`
limit select.

Not a Millennium result, and not a claim about any learning grade. The Markov reading adds no
computation: it names what the collapsed population already carried.

And one bound worth stating: the exact closure is a property of **`ℚ⁺` and the primes**. A carrier
whose multiplicative chart is not free abelian on a known basis would not close this way, and the
organ would owe an enclosure there rather than an exact ratio.
