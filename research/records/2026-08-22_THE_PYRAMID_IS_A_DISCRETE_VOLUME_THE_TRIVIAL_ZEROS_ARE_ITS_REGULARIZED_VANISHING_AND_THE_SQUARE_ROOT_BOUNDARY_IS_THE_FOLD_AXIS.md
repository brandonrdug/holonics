# The pyramid is a discrete volume, the trivial zeros are its regularized vanishing, and the square-root boundary is the fold axis

**Date:** 2026-08-22
**Kind:** framing deposit — Brandon's question: how pyramidal numbers relate to the
area distributions/partitions about primes and the Riemann zeta function, to volumes,
integration by reflection, and sphere/fractal-packing.  **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../docs/plans/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Truth grades:** `proved-standard` for every classical statement, cited;
`interpretation` for the typings, marked.

---

## 1. The pyramid is a discrete volume, and its regularized shadow is a zeta value

A square pyramidal number `P(n) = Σ_{k≤n} k² = n(n+1)(2n+1)/6` is squares stacked into
a pyramid: **discrete integration of areas into a volume**.  The general stacking —
the Faulhaber sums `Σ_{k≤n} kˢ` — is governed by the Bernoulli numbers, and the bridge
to zeta is an identity, not an analogy:

```text
ζ(−s) = −B_{s+1}/(s+1)          (proved-standard)
```

So the regularized pyramidal volume of degree two **is** `ζ(−2) = 0` — a trivial zero.
**The trivial zeros of ζ say exactly that the regularized even-degree pyramid volumes
vanish**, and they vanish through the reflection formula
`ζ(s) = 2ˢπ^{s−1} sin(πs/2) Γ(1−s) ζ(1−s)` — the `sin(πs/2)` factor kills the even
negative integers.  The reflection formula is proved by **theta and Poisson
summation** — the heat-kernel-by-images mechanism this corpus already owns as
integration by reflection — and the same theta functions are the generating series of
lattice shell counts, which is where sphere packing enters as the same object rather
than a neighbor: the Fourier-interpolation proofs in dimensions eight and twenty-four
are modular arguments on exactly these series.  One chain:

```text
pyramidal numbers → Faulhaber/Bernoulli → ζ at negative integers
  → reflection formula → theta/Poisson → lattice shell counts / packing
```

## 2. The square-root boundary appears three ways, and they are one fold

- **The hyperbola fold** (Dirichlet's divisor method): the divisor area under
  `xy = N` is counted by folding across the diagonal — the fold axis is `√N`, and the
  correction term is the square `⌊√N⌋²`.  Integration by reflection, literally: fold,
  integrate one half, repay the double-counted boundary.
- **The trial-division frontier**: a composite's divisor pair reflects across `√N` —
  the machine's own RIDE/FOUND reading of prime founding, already in the operating
  contract as the landmark law.
- **The Riemann fluctuation scale**: the prime area under the von Mangoldt staircase
  is `x` to leading order, and the explicit formula writes the fluctuation as a sum of
  reflection waves `x^{1/2}·cos(γ log x)`, one per zero — RH is the statement that the
  partition's residual lives exactly on the boundary exponent `1/2`, the half-density
  whose three faces the contract already carries.

**The typing**: the square-root boundary is the fold axis of one reflection, read in
three charts — the divisor region's involution `d ↔ N/d`, the founding frontier, and
the critical line.  An area partition about the primes is a folded region, and its
residual is a boundary population, not noise.

## 3. Areas to volumes, aliasing, and the fractal note

The residuals of folded regions against the lattice — the Dirichlet divisor problem
and the Gauss circle problem, both conjectured at exponent `1/4` and both proved past
`1/3` — are controlled by Poisson summation against the transform of the boundary:
**packing counts and aliasing are the same computation**, the boundary's spectrum beat
against the lattice.  Passing from areas to volumes (pyramidal stacking, lattice
points in dilated bodies, Ehrhart counting) raises the dimension of the same object;
the Bernoulli corrections of Faulhaber are the lower-dimensional boundary terms, which
is why the same numbers govern the discrete/continuous defect at every degree.  The
fractal note: the folded hyperbola region's corner strips rescale self-similarly under
the Farey/`SL₂(ℤ)` structure — the modular group that already holds this corpus's
continued-fraction and theta deposits — so the "fractal-packing" intuition lands on
the modular orbit of the fold, not on a new object.

## 4. Boundaries

Every classical claim is cited literature (Faulhaber/Bernoulli, the functional
equation via theta, Dirichlet's hyperbola method, the explicit formula, the
circle/divisor error exponents, the Fourier-interpolation packing proofs); the typings
are `interpretation`; nothing here is enacted, and nothing about the Riemann
hypothesis is claimed.
