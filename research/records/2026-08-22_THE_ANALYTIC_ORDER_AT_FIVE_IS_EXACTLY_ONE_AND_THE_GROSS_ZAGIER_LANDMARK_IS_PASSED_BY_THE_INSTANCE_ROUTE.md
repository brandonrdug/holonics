# The analytic order at five is exactly one, and the Gross–Zagier landmark is passed by the instance route

**Date:** 2026-08-22
**Kind:** the analytic half of the rank-one coincidence at five, returned under Brandon's
goal *"Solve BSD, found pivots using the composition of the solution…"*.  Solo
orchestrator work, three Lean files across three commits (`217c64c`, `6164bdb`,
`036c63b`).  **It schedules nothing.**
[`blueprint/THE_ROADMAP.md`](../../blueprint/THE_ROADMAP.md) and
[`CONSTRUCTION_STATE.md`](../../CONSTRUCTION_STATE.md) remain the only construction
authorities.
**Truth grades:** `proved-derived` with `formal-checked` evidence for every named
theorem (`#print axioms` → `[propext, Classical.choice, Quot.sound]`, zero `sorryAx`);
`interpretation` for every classical identification.  The library builds at **3,413
jobs**.  No floating point anywhere; the compact-remainder arithmetic is rational
throughout.

---

## 1. The headline

**The completed L-function of `y² = x³ − 25x` has analytic order exactly one at the
center of its reflection, kernel-checked, with no Gross–Zagier input.**  Three theorems
carry it:

- **`theOddHandForcesTheCentralVanishingAtFive`** — `Λ₅(1) = 0`: the sign-`−1`
  functional equation kills the value by parity alone;
- **`theDerivativeIsTheOddSectorFirstMoment`** — `Λ₅′(1) = 2·∫₁^∞ θ₅(t)·log t dt`:
  the `t ↦ 1/t` fold at the Mellin level presents the derivative as one
  fundamental-domain integral — the parametric time-parity fold as a theorem;
- **`theDerivativeDoesNotVanishAtFive`** — the integral is strictly positive by
  certified exact arithmetic, so `Λ₅′(1) ≠ 0`.

With `FaceImageFive.lean`'s completed descent (image exactly eight: rank exactly one
in descent form, `Ш(E₅)[2] = 0`, committed previously), both halves of the rank-one
coincidence at five are now formal; the remaining work is the witness assembly
(`LDatum 5`) joining them through the identified coefficient stream.

## 2. The chain, by file

- **`FiveTheta.lean`** (~1,800 lines, `217c64c`) — the theta of the five-curve as
  fifty shifted Hurwitz-kernel products, conductor `800`.  The engine is finite:
  **`theGaussEigenIdentity`** (`Σ_{r,s<5} χ₅(r²−s²)ζ^{ξr+ηs} = 5·χ₅(ξ²−η²)` — the
  twist character is a finite Fourier eigenfunction, by the split-chart rotation
  `(r,s) ↦ (r+s, r−s)` and `g(1)² = 5`); **`thePhaseCollapse`** (all fifty phases
  return `10·iⁿ·[m odd]·χ₅(n²+m²)`); then the lattice ladder of level one transplanted
  with the character riding every fold.  **`theFiveDuplicationIdentity`** carries the
  sign: the fold `n²+m² = 2(a²+b²)` deposits `χ₅(2) = −1` — **the root number at five
  returned by finite arithmetic**.  `θ₅(1/x) = −x²·θ₅(x)`; the `StrongFEPair` with
  `ε = −1` returns `Λ₅` entire with `Λ₅(2−s) = −Λ₅(s)`; and
  **`theFiveThetaIsItsLatticeSum`** returns the theta as its `χ₅`-weighted Gaussian
  class `HasSum` for the receiver to integrate against.
- **`FiveDerivative.lean`** (`6164bdb`) — the Mellin transform differentiates under
  the integral (`mellin_hasDerivAt_of_isBigO_rpow`, the FE-pair supplying decay at
  both ends), and the fold runs at the Mellin level: `mellin_comp_inv` plus a `t²`
  shift carry the lower half onto the upper exactly, `log(1/t)·θ₅(1/t) = t²·log t·θ₅(t)`
  through the odd functional equation.
- **`FivePositivity.lean`** (~1,000 lines, `036c63b`) — the certified estimate.  The
  lattice series integrates term by term
  (`integral_tsum_of_summable_integral_norm`); the founding class `(0,0)` contributes
  `∫₁^∞ e^{−αt}·log t·dt ≥ e^{−3α}/α ≥ 5109/2222` (`α = π√2/20`, enclosed in
  `[0.2221, 0.2222]` by the π and `√2` bounds); every other class is dominated through
  `|w| ≤ N`, the `J`-law `∫₁^∞ e^{−βt}log t ≤ e^{−β}/β²`, and `N ≥ 9` — the two
  norm-five neighbours are silenced exactly by `χ₅(5) = 0`; the whole tail is bounded
  by the product of two one-dimensional Gaussian geometric majorants
  (`tsum_int_le_geometric`) with all eight exponentials enclosed by rational
  `(1+x/64)^{64}` certificates.  **Margin `≈ 0.47`; no float anywhere.**

## 3. What this establishes about the landmark

The general rank-one law (order one ⟹ a point of infinite order, via the height of a
Heegner point) is Gross–Zagier, and nothing here claims it.  What this campaign
establishes is that **at an instance the landmark is not a wall**: the analytic order
at five is decided by the sign (parity) plus a strictly positive folded first moment
(certified arithmetic), and the algebraic rank at five is decided by the completed
descent — each half independent, both kernel-checked.  The route generalizes to any
odd-sign twist whose theta the lattice machinery can build, which is the sign-`−1`
half of the congruent-number family.

## 4. Standing position

Committed and kernel-checked at five: the twist law (`FiveTwist.lean`), the theta with
sign `−1`, `Λ₅` entire and odd, `Λ₅(1) = 0`, `Λ₅′(1) > 0`, the completed descent with
image exactly eight.  **Open, named:** the witness `LDatum 5` (Dirichlet-series
identification of the twisted stream, agreement half-plane, bad primes at 2 and 5
through quadratic reciprocity) and the two-sided rank-one instance assembly; behind
it, the even-sector second chart at 34 (the ternary count), the ledger `L(1) = Ω/8`,
and the family-wise analytic mate of `StratumDescent` on `p ≡ 3 (mod 8)`.
