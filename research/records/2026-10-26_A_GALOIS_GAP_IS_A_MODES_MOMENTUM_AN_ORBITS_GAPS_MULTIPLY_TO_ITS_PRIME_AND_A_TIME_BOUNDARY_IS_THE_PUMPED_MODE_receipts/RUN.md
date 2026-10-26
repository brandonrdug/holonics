# Receipt: a Galois gap is a mode's momentum

The record is
[a Galois gap is a mode's momentum](../2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE.md).

## What runs

`colour_gaps.py` is self-contained. It uses only Python's standard library, integers and
`fractions.Fraction`. Gaussian rationals are held as pairs, and the polynomials are integer
coefficient lists. It reads no data, private or public, and builds no float.

Parts and what each checks:
- **A.** The cyclotomic polynomials `Φ_d` for `d ≤ 400`, by exact division of `x^d − 1`, and
  `Φ_d(1)`: `p` for `d = p^k`, `1` otherwise. For `d ≤ 20,000` it checks the Möbius product
  `∏_(e|d) e^(μ(d/e))`, and that a ring's orbits multiply to `m`. For `m ≤ 400` it checks
  `∏_(d|m, d>1) Φ_d = 1 + x + … + x^(m−1)`.
- **B.** For `m = 3, …, 60`, the cycle Laplacian's characteristic polynomial against
  `x (x − 4)^[m even] ∏_(d|m, d≥3) ψ_d(x)²`. It compares them by Bareiss determinants at `m + 2`
  integer points, and `ψ_d` is built from `Φ_d` through `y = z + 1/z`. It also checks
  `ψ_d(0) = Φ_d(1)`, that the nonzero eigenvalues multiply to `m²`, and that there are `m` spanning
  trees.
- **C.** For `m = 3, …, 300` and every unit `u`, that `x ↦ ux` keeps the ring's adjacency exactly
  when `u ≡ ±1`.
- **D.** For bases 2 to 40 and `m ≤ 300`, the characters fixed by `a ↦ ba` and those it mirrors; for
  base 10, `m ≤ 2000`.
- **E.** One LC mode at a step in space and at a step in time, for rational `L = l²` and `C = c²`:
  - continuity at each step;
  - power across the step in space;
  - the action across the step in time;
  - energy equal to frequency times quanta, and the work;
  - the time-mirror limit.
- **F.** The dilation-current divergence on 300 random polynomial tensors in four variables,
  signature `(−, +, +, +)`.
- **G.** Stieltjes' identity at every root of 400 random rational root sets. The Foster tank's sign
  on a grid of Gaussian rationals. `|Res(xⁿ − 1, n x^(n−1))| = nⁿ` for `n ≤ 10`.
- **H.** Every elliptic curve `y² = x³ + ax + b` over `F_p`, `5 ≤ p < 70`: `a_p² < 4p` (24,390
  curves).
- **K.** The arithmetic of the relaxed Fourier step's certified bound against the per-mode bound,
  for the last record's §11.

The last line is `all 153862 checks hold`.

## Command, projection and measured run

```bash
cd research/records/2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE_receipts
timeout 60 python3 -I colour_gaps.py > colour_gaps.txt
```

- **Projection.** About 10 s, from a first development run of 9,426 ms. The deadline is 60 s, fixed
  by an outer `timeout`.
- **Measured.** The committed output came from that command, run through a `runpy` wrapper that
  reads `resource.getrusage`. Wall time was 9,083 ms, with a peak resident set of 16,132 KiB on one
  thread; the script's own clock read 9,062 ms. Measured over the deadline: 9,083/60,000.

| File | SHA-256 |
|---|---|
| `colour_gaps.py` | `c6df8b2044dcd00ac48a0bb78cf5e11b0fbdc135dcbe15c6bbccd17b3ca95459` |
| `colour_gaps.txt` | `4b2f4f02557371cc72acf5356e1a4598067a6ab0558e4339acd75ebf68040c73` |

The output's hash changes with the elapsed time printed on its last line; every other line is
deterministic.

## Development notes

- The first Möbius loop enumerated divisors by trial up to `d`, which made part A quadratic. It now
  enumerates divisors from the factorization.
- An identity first written for "the orbits multiply to `m`" multiplied `m`'s own prime powers back
  together, which is a tautology. It was replaced by the product of the computed orbit values and by
  the polynomial identity `∏ Φ_d = 1 + x + … + x^(m−1)`.

## The second receipt: `colourless_tower.py`

Written the same day for the record's §12, after Brandon's reply that the colourless classes are
the compressible things. The same rules hold: elements of `ℚ(ζ_n)` are integer polynomials reduced
modulo `Φ_n`, and numbers of `ℚ(√5)` are pairs compared by exact sign tests.

Parts:
- **P.** The trace of `ζ_n^j` against the Ramanujan sum `c_n(j)` for every `n ≤ 200` and `j < n`,
  with `Tr ζ_n = μ(n)`. The Mertens function `M(N)` as the running sum of these traces for
  `N ≤ 200` (`M(200) = −8`). The norm `∏_(d|n) d^(−μ(d)) = e^(Λ(n))` for `n ≤ 5000`.
- **Q.** For each prime power `p^(k+1) ≤ 400`, the layer trace down to `ℚ(ζ_(p^k))`: `p·ω^j` when
  `p | j`, `0` otherwise. Also `ord_(3^k)(10) = 3^(k−2)` for `k = 2, …, 12`.
- **R.** The Fibonacci model set with window `[−1, τ − 1)` in the conjugate colour. Its 1,086 points
  in `[0, 1500]` are in exact order, with gaps `τ` and `1` in the order of `a → ab, b → a`, starting
  at 0. For `n ≤ 60`, `τⁿ` and `τ′ⁿ` against the Lucas and Fibonacci numbers, with the hidden
  colour `|τ′ⁿ|` strictly shrinking.

```bash
cd research/records/2026-10-26_A_GALOIS_GAP_IS_A_MODES_MOMENTUM_AN_ORBITS_GAPS_MULTIPLY_TO_ITS_PRIME_AND_A_TIME_BOUNDARY_IS_THE_PUMPED_MODE_receipts
timeout 60 python3 -I colourless_tower.py > colourless_tower.txt
```

- **Projection.** About 5 s, from a first development run of 4,966 ms. The deadline is 60 s, fixed
  by an outer `timeout`.
- **Measured.** Through the same `runpy` wrapper the run took 4,879 ms wall time, with a peak
  resident set of 12,764 KiB on one thread; the script's own clock read 4,857 ms. Measured over the
  deadline: 4,879/60,000.
- **Result.** The last line is `all 30248 checks hold`.

| File | SHA-256 |
|---|---|
| `colourless_tower.py` | `b6ae728d350aa367bfb02c4acecfd5f8aa447fe45cec54954815d43f8c67fb22` |
| `colourless_tower.txt` | `86ea37f1661c8d4c89306758f635420f6acb78602d76bf23ca060a5024c7a90d` |

**Development notes.**
- The window `[−1, τ − 1)` was found by trying candidate windows on a scratch run before the exact
  check. The committed check is exact.
- The model set's points are sorted by a rational approximation of `√5`, and their order is then
  verified exactly.
