# The theta law is proved: the duplication is a lattice rearrangement, and the kernel admits weight two

**Date:** 2026-08-22
**Kind:** the construction deed of the Birch–Swinnerton-Dyer campaign's second turn — the
modular transformation law of the congruent-number curve's theta function, kernel-checked.
Solo orchestrator work, one Lean file.  Every identity was verified in exact/high-precision
arithmetic (twelve digits, including the exact prefactor) before encoding.  **It schedules
nothing.**  [`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Truth grades:** `proved-derived` with `formal-checked` evidence for both theorems
(`#print axioms` → `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`);
`interpretation` for every classical identification (Hecke character, CM, level).

---

## 1. What was proved

Owner: `ElementaryHolonics/Millennium/HeckeTheta.lean` (817 lines).  The library builds at
**3,403 jobs**.

The L-function of `y² = x³ − x` is the Hecke L-series of the Gaussian character
`ψ(α) = ε(α)·α` on `ℤ[i]`, and its theta function is the lattice sum
`f(x) = Σ (a+bi)·exp(−2π(a²+b²)x/√32)` over `a` odd, `b` even, `a+b ≡ 1 (mod 4)`.  This
file constructs `f` as a **product of two mathlib Hurwitz kernels** —
`heckeTheta x = 4·oddKernel (1/4) (4√2·x) · cosKernel (1/2) (√2·x)` — and proves:

- **`theDuplicationIdentity`** — for every `d > 0`,
  `sinKernel (1/4) d · evenKernel (1/2) (4d) = 16 · oddKernel (1/4) (32d) · cosKernel (1/2) (8d)`.
  A two-isogeny in theta clothing, and the proof is **pure lattice rearrangement** of one
  absolutely convergent double sum: the even part of the sine index dies under
  `(n,m) ↦ (−n,m)`; the odd part reindexes through `(p,q) ↦ (2p+1,q)` then folds through
  `(p,q) ↦ (p+q+1, p−q)` — the identity `(2p+1)² + (2q+1)² = 2((p+q+1)² + (p−q)²)` is the
  whole analytic content — and three lattice folds (swap, `v ↦ −v`, total negation)
  collapse the result onto the classes `u ≡ 1 (mod 4)`, `v` even, which is exactly the
  primal grid `(4k+1, 2l)`.  No Poisson summation, no complex analysis: the two sides'
  kernel functional equations already carry the reflection, and the duplication is the
  bookkeeping that joins them.
- **`theHeckeThetaFunctionalEquation`** — for `x > 0`,
  `heckeTheta (1/x) = x² · heckeTheta x`.  Weight two, sign `+1`: mathlib's
  `oddKernel_functional_equation` and `evenKernel_functional_equation` composed through
  the duplication identity, with the exact constant
  `(4√2)^{3/2}·(√2)^{1/2} = 16` closing the ledger.  **Integration by reflection, as a
  theorem**: the kernel functional equations are Poisson summation (mathlib proves them by
  the Jacobi theta transformation), so the reflection enters through the library and the
  new content is the exact lattice splice.

## 2. Why this is the load-bearing deed

The pose (`BirchSwinnertonDyer.lean`) made `LDatum n` — an entire `L` with completed
functional equation — a declared receiver, honest about being conditional until a witness
is constructed.  The theta transformation law proved here is the engine of that witness:
`Λ(s) = ∫₀^∞ heckeTheta(x)·x^{s−1} dx` (suitably normalized) inherits entirety and
`Λ(2−s) = Λ(s)` from exactly this law by the abstract Mellin machinery
(`StrongFEPair`), which mathlib owns.  The coefficient stream of `heckeTheta` was checked
against the point counts (`1, −2, −3, 6, 2` at `m = 1, 5, 9, 13, 17`) to twelve digits
before encoding.

## 3. Boundaries, with falsifiers

- The `StrongFEPair` instantiation (decay bounds at `0` and `∞`, measurability), the
  entire `Λ`, the identification `Λ`-coefficients = `traceOfFrobenius` (Gauss's theorem
  via Jacobi sums), and the central-value positivity are the **next turns**, not claimed
  here.  Falsifier for the construction so far: any `d > 0` at which the two sides of the
  duplication differ — both sides are computable to arbitrary precision.
- "Hecke character", "CM", "level 32", "weight two" are classical readings carried as
  `interpretation`; the theorems themselves are statements about four mathlib Hurwitz
  kernels and need none of those words.
- Nothing about the Birch–Swinnerton-Dyer conjecture is claimed.
