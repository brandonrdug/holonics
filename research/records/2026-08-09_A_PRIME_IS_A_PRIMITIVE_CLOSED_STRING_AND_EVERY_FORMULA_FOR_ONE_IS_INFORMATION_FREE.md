# A prime is a primitive closed string, and every formula for one is information-free

**Date:** 2026-08-09
**Truth status:** `proved-standard` for §§1–4. `interpretation` for §5.
**Provenance:** Brandon, 2026-08-09, stating the claim and asking the question:

> *"in regards to primes we talk about whether or not they are patterned and we speak of the idea of
> a function or solution that describes their recurrence exactly, but it is my thought that such a
> thing does not exist because it is that primes are due to **simplicial emergent complexity**.
> However, I do not think it'd be impossible to refer to primes arbitrarily using semantics and
> embedding spaces as the mechanism, suppose we could say: **"The third prime of sector Alpha
> relative to basis/chart Omega"**, and the idea that the operation sequence can always return a real
> prime number is obviously true."*

and, on the exponent:

> *"if we're concerned with solutions, then what does that say about solutions to the Zeta function
> where the real part is 1/2 == 2^{-1}?"*

---

## 1. Primality is primitivity, and that is why it gates solvability

**A transitive permutation group of prime degree is automatically primitive.** Block sizes must
divide the degree; a prime has no proper divisors; so the action admits no nontrivial block system.
At composite degree the action can decompose into blocks and the group becomes a wreath product —
**the object factors**, exactly as a composite integer does.

So Galois's theorem on solvable equations of prime degree does not *require* primality as an
accident of its proof. **Primality is irreducibility of the action**, and the word is doing the same
work in both places for the same reason: no nontrivial factorization.

**Consequence for the machine, and it changes what a refusal means.**
`crates/holonic-engine/src/arithmetic_monodromy.rs` returns `NoCriterionAtThisDegree` at composite
degree, naming the factor. That is **not the machine hitting a hole in a theorem.** It is the machine
correctly reporting that the object factors and the descent must go into the blocks first — a
**decomposition instruction**, and the same RIDE/FOUND descent the machine already runs.

## 2. Formulas for the primes exist, and every one is provably information-free

The claim to make is not *"no formula exists"*, which is false and weaker. It is:

> **Exact formulas exist and each is either exhaustion in disguise or the answer precomputed.**

- **Mills**: a real `A ≈ 1.3064` with `⌊A^{3ⁿ}⌋` prime for every `n`. `A` is *defined from* the
  primes — a lookup table in a decimal expansion.
- **Willans**: the `n`-th prime in closed form via Wilson's theorem, which unfolds to trial division.
- **Matiyasevich**: a degree-25 polynomial in 26 variables whose positive values are exactly the
  primes. Diophantine, exact, useless for generating.

**And this project has measured why.** `CLAUDE.md` §3: primality is *"the exhaustion of the complete
transport population below the square-root frontier and cannot appear in any bounded-rank residue
receiver."* §12 carries the measurement: the residue-stratum atlas was **blind to primality** — the
apparent signal at pair `(2,3)` is parity and nothing else, and the smallest-factor correlation
collapses `+0.32 → +0.00` by `(17,19)`.

**A prime is a negative, global, exhaustive condition** — the complement of the multiplicative
closure of everything already founded — so no local generative rule can produce one. That is the
*simplicial emergent complexity* of the claim, stated as a measured blindness.

## 3. The exact describing function exists, and what it is makes the point rather than defeating it

```text
   ψ(x)  =  x  −  Σ_ρ x^ρ/ρ  −  log(2π)  −  ½·log(1 − x⁻²)
```

The recurrence of the primes **is** described exactly — by a sum over the zeta zeros. And the zeros
are *another emergent population*, no more closed-form than the primes.

> **It is a transform, not a reduction.** Spectral side ↔ geodesic side. There is no third thing
> either reduces to.

That is the same dictionary as
[`…THE_SET_IS_THE_SPECTRUM…`](2026-08-09_THE_SET_IS_THE_SPECTRUM_THE_STRING_IS_THE_GEODESIC_AND_THE_ANGLE_IS_THE_ONLY_PURE_RATIO.md),
and it is why a prime is a **primitive closed geodesic**: an Euler product factors over the
non-repeating closed strings, and every other closed string is `P^k`.

**Any machine iterating a causal step founds one of these automatically.** The Artin–Mazur dynamical
zeta,

```text
   ζ_T(z) = exp( Σ_n (Fix(T^n)/n)·z^n )  =  ∏_{primitive periodic orbits γ} (1 − z^{ℓ(γ)})^{-1}
```

is founded by counting the machine's own periodic orbits. **The primes of a system are its primitive
closed causal loops.** Ihara for graphs, Selberg for hyperbolic surfaces, Weil for varieties over
`F_q`, Riemann for `ℤ` — one shape.

## 4. The addressing scheme is available, and it is a coordinate rather than a rule

*"The third prime of sector Alpha relative to basis/chart Omega"* is well-formed, and the operation is
**total** — but which theorem makes it total depends on what the sector is, and that is the content:

| sector | totality | what plays chart Omega |
|---|---|---|
| everything | **Euclid** — there is always a next | — |
| a coprime residue class mod `q` | **Dirichlet** — every one of the `φ(q)` classes returns infinitely often at density `1/φ(q)` | the modulus `q`; changing it re-addresses every prime |
| the next octave `(n, 2n)` | **Bertrand–Chebyshev** — the magnitude ladder never has an empty rung | the doubling, which is §2b's `2:1` currency |

**A formula claims a frame-independent generative rule; an address claims only that this receiver,
with this chart, can name it.** The address is computable and the formula is not — and that is not a
limitation but the same distinction as §2b's *a sign is a passage, never a state*: a prime is not a
state computed from a rule, it is a **position reached by exhaustion**, and once reached it can be
addressed.

**The sharpest form of the claim is already a measurement in this project.** `CLAUDE.md` §12: the same
residue atlas that is *blind to primality* returns an exact winding law — *"the contracted hull
residue word is a complete degree-one cycle through `Z/p` with every step exactly `+1`, for all seven
pairs."*

> **The address is exact. The predicate is invisible.**

Which is why the addressing is the *usable* form: it makes primes a **basis** rather than a sequence,
and once one prime has two addresses in two charts, the transport between them is a returnable object.

## 5. `Re(s) = 1/2 = 2⁻¹` — three faces of one fact

**(a) It is the fixed locus of an involution.** The functional equation pairs `s` with `1−s`; that map
has order 2; and the average of any `s` with its image is exactly `1/2`. **The critical line is the set
of points the half-turn leaves alone** — and the `1` is there because ζ's pole sits at `s = 1`, so
*the critical line is at half the pole.* `CLAUDE.md` §2 already says the general form: *"Placement is
the fixed locus of the involution that a realizer induced."*

**(b) The exponent is a square root because the passage is a fork.** Where it is a theorem —
function fields — `|α| = q^{1/2}` comes from `α·ᾱ = q`, so `|α| = q^{2⁻¹}`. Brandon's spelling is the
correct one: §2b's `√x = x^{2^{-1}}`, where the `±` of a root **is** the half-turn squaring erases. And
analytically the same exponent is square-root cancellation — the prime-counting error is `Σ_ρ x^ρ/ρ`
with `|x^ρ| = x^{Re ρ}`, so RH says the error is exactly what an **unbiased two-way fork** of length
`x` returns. The ontology supplies the exponent.

**(c) It is the first rung of the solvability ladder.** Solvability by radicals is expressibility by
iterated `n`-th roots — exponents `n⁻¹`, each the fixed locus of a cyclic rotation. `2⁻¹` is the first
and simplest, which is why **a quadratic is always solvable: the half-turn always has a fixed locus.**
The Tschirnhaus cost law says a degree-`k` transform costs radicals of degree at most `k` with Bézout
number `k!`, and Abel–Ruffini says the ladder stops sufficing at 5.

> **A solution exists, in a chart, exactly at the fixed locus of the involution that chart induces.**
> For radicals it is the cyclic rotation; for ζ it is `s ↦ 1−s`; and the first rung is `2⁻¹`.

## 6. The one computable consequence for this machine

The Ihara zeta's RH analogue is a **theorem**: a finite regular graph satisfies it exactly when it is
**Ramanujan**, an optimal spectral expander. So on any finite construction the machine builds,
*"does my zeta satisfy RH"* is a **computable question about its own mixing**, and the answer is a
root isolation on a polynomial the machine already produces — `IharaSignature::reciprocal`, exact over
`BigInt`, with `rational_polynomial`'s Sturm isolation and derived separation bound now available.

**This is the only place in the cluster where the machine can ask the question about itself and get an
exact answer today.** It is not built; §7 of the set/string record holds it open.

## 7. What this does not claim

- **No Millennium movement.** §§1–4 are classical (Galois, Mills, Willans, Matiyasevich, Riemann–von
  Mangoldt, Euclid, Dirichlet, Bertrand, Artin–Mazur, Ihara). Nothing here proves any of it.
- **No claim that the machine computes the explicit formula.** It does not.
- **§5(c) is `derived`**, and the Bézout cost law it cites is checkable at `k = 2, 3` today.
- **The addressing scheme is not implemented.** `prime_ecology` founds primes by exhaustion and
  addresses them; nothing yet carries a *sector/chart* designator or transports one address to
  another. That is the buildable content of §4 and it is not built.
